use crate::Heap;
use crate::{gc::Gc, sexp::ValueType};
use std::mem::{size_of, MaybeUninit};

pub struct GcVec<T> {
    storage: Gc<Storage<T>>,
}

impl<T: 'static> GcVec<T> {
    pub fn new(heap: &mut Heap) -> Self {
        Self::with_capacity(heap, 0)
    }

    pub fn with_capacity(heap: &mut Heap, cap: usize) -> Self {
        Self {
            storage: Storage::<T>::new(heap, cap),
        }
    }

    fn data(&self) -> *mut T {
        self.storage.data.as_ptr() as *mut T
    }

    fn grow(&mut self, heap: &mut Heap, capacity: usize) {
        let old_capacity = self.capacity();
        let new_capacity = capacity;
        if new_capacity == old_capacity {
            return;
        }

        let len = self.len();
        let mut temp = Storage::new(heap, new_capacity);
        unsafe {
            core::ptr::copy_nonoverlapping(self.data(), temp.data.as_mut_ptr().cast::<T>(), len);
        }

        self.storage = temp;
        self.storage.len = len;
    }

    pub fn len(&self) -> usize {
        self.storage.len
    }

    pub fn capacity(&self) -> usize {
        self.storage.cap
    }
    pub fn as_mut_ptr(&self) -> *mut T {
        self.data()
    }

    pub fn as_ptr(&self) -> *const T {
        self.data()
    }

    /// `swap_remove` removes the element located at `index` and replaces it with the last value
    /// in the GcVec, returning the removed element to the caller.
    #[must_use]
    pub fn swap_remove(&mut self, index: usize) -> T {
        let len = self.len();

        assert!(
            (index < len),
            "swap_remove index (is {}) should be < len (is {})",
            index,
            len
        );

        unsafe { core::ptr::swap(self.as_mut_ptr().add(len - 1), self.as_mut_ptr().add(index)) };

        let x = unsafe { core::ptr::read(self.as_ptr().add(self.len() - 1)) };
        self.storage.len -= 1;
        x
    }

    pub fn shrink_to(&mut self, mutator: &mut Heap, min_capacity: usize) {
        let len = self.len();
        let capacity = self.capacity();

        if min_capacity < len {
            self.shrink_to_fit(mutator);
            return;
        }

        if capacity == min_capacity {
            return;
        }

        assert!(
            capacity >= min_capacity,
            "Tried to shrink to a larger capacity"
        );

        self.grow(mutator, min_capacity);
    }
    pub fn shrink_to_fit(&mut self, mutator: &mut Heap) {
        let len = self.len();
        if len == self.capacity() {
            return;
        }

        self.grow(mutator, len);
    }
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        let len = self.len();
        let data = self.as_mut_ptr();
        let mut read = data;
        let mut write = read;

        let last = unsafe { data.add(len) };

        while read < last {
            let should_retain = unsafe { f(&mut *read) };
            if should_retain {
                if read != write {
                    unsafe {
                        core::mem::swap(&mut *read, &mut *write);
                    }
                }
                write = unsafe { write.add(1) };
            }

            read = unsafe { read.add(1) };
        }

        self.truncate((write as usize - data as usize) / core::mem::size_of::<T>());
    }
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let original_len = self.len();
        // Avoid double drop if the drop guard is not executed,
        // since we may make some holes during the process.
        unsafe { self.set_len(0) };

        // Vec: [Kept, Kept, Hole, Hole, Hole, Hole, Unchecked, Unchecked]
        //      |<-              processed len   ->| ^- next to check
        //                  |<-  deleted cnt     ->|
        //      |<-              original_len                          ->|
        // Kept: Elements which predicate returns true on.
        // Hole: Moved or dropped element slot.
        // Unchecked: Unchecked valid elements.
        //
        // This drop guard will be invoked when predicate or `drop` of element panicked.
        // It shifts unchecked elements to cover holes and `set_len` to the correct length.
        // In cases when predicate and `drop` never panick, it will be optimized out.
        struct BackshiftOnDrop<'a, T: 'static> {
            v: &'a mut GcVec<T>,
            processed_len: usize,
            deleted_cnt: usize,
            original_len: usize,
        }

        impl<T: 'static> Drop for BackshiftOnDrop<'_, T> {
            fn drop(&mut self) {
                if self.deleted_cnt > 0 {
                    // SAFETY: Trailing unchecked items must be valid since we never touch them.
                    unsafe {
                        std::ptr::copy(
                            self.v.as_ptr().add(self.processed_len),
                            self.v
                                .as_mut_ptr()
                                .add(self.processed_len - self.deleted_cnt),
                            self.original_len - self.processed_len,
                        );
                    }
                }
                // SAFETY: After filling holes, all items are in contiguous memory.
                unsafe {
                    self.v.set_len(self.original_len - self.deleted_cnt);
                }
            }
        }

        let mut g = BackshiftOnDrop {
            v: self,
            processed_len: 0,
            deleted_cnt: 0,
            original_len,
        };

        fn process_loop<F, T: 'static, const DELETED: bool>(
            original_len: usize,
            f: &mut F,
            g: &mut BackshiftOnDrop<'_, T>,
        ) where
            F: FnMut(&mut T) -> bool,
        {
            while g.processed_len != original_len {
                // SAFETY: Unchecked element must be valid.
                let cur = unsafe { &mut *g.v.as_mut_ptr().add(g.processed_len) };
                if !f(cur) {
                    // Advance early to avoid double drop if `drop_in_place` panicked.
                    g.processed_len += 1;
                    g.deleted_cnt += 1;
                    // SAFETY: We never touch this element again after dropped.
                    unsafe { std::ptr::drop_in_place(cur) };
                    // We already advanced the counter.
                    if DELETED {
                        continue;
                    } else {
                        break;
                    }
                }
                if DELETED {
                    // SAFETY: `deleted_cnt` > 0, so the hole slot must not overlap with current element.
                    // We use copy for move, and never touch this element again.
                    unsafe {
                        let hole_slot = g.v.as_mut_ptr().add(g.processed_len - g.deleted_cnt);
                        std::ptr::copy_nonoverlapping(cur, hole_slot, 1);
                    }
                }
                g.processed_len += 1;
            }
        }

        // Stage 1: Nothing was deleted.
        process_loop::<F, T, false>(original_len, &mut f, &mut g);

        // Stage 2: Some elements were deleted.
        process_loop::<F, T, true>(original_len, &mut f, &mut g);

        // All item are processed. This can be optimized to `set_len` by LLVM.
        drop(g);
    }
    pub fn clear(&mut self) {
        self.truncate(0);
    }
    /// `append` moves every element from `other` to the back of `self`. `other.is_empty()` is `true` once this operation
    /// completes and its capacity is unaffected.
    ///
    ///
    /// TODO: Should we assume that `other` is already rooted?
    pub fn append(&mut self, mutator: &mut Heap, other: &mut GcVec<T>) {
        if other.is_empty() {
            return;
        }

        let other_len = other.len();
        self.reserve(mutator, other_len);

        unsafe {
            core::ptr::copy_nonoverlapping(
                other.as_ptr(),
                self.as_mut_ptr().add(self.len()),
                other_len,
            );
        };

        unsafe {
            other.set_len(0);
            self.set_len(self.len() + other_len);
        };
    }
    pub fn resize(&mut self, mutator: &mut Heap, new_len: usize, value: T)
    where
        T: Clone,
    {
        let len = self.len();

        match new_len.cmp(&len) {
            core::cmp::Ordering::Equal => {}
            core::cmp::Ordering::Greater => {
                let num_elems = new_len - len;
                self.reserve(mutator, num_elems);
                for _i in 0..num_elems {
                    self.push(mutator, value.clone());
                }
            }
            core::cmp::Ordering::Less => {
                self.truncate(new_len);
            }
        }
    }

    pub fn reserve(&mut self, mutator: &mut Heap, additional: usize) {
        self.try_reserve(mutator, additional);
    }

    /// `resize_with` will invoke the supplied callable `f` as many times as is required until
    /// `len() == new_len` is true. If the `new_len` exceeds the current [`len()`](MiniVec::len)
    /// then the GcVec will be resized via a call to `truncate(new_len)`. If the `new_len` and
    /// `len()` are equal then no operation is performed.
    pub fn resize_with<F>(&mut self, mutator: &mut Heap, new_len: usize, mut f: F)
    where
        F: FnMut(&mut Heap) -> T,
    {
        use core::cmp::Ordering::{Equal, Greater, Less};

        let len = self.len();
        match new_len.cmp(&len) {
            Equal => {}
            Greater => {
                let num_elems = new_len - len;
                self.reserve(mutator, num_elems);
                for _i in 0..num_elems {
                    let val = f(mutator); // do not root `val` because it is rooted in `push()` already
                    self.push(mutator, val);
                }
            }
            Less => {
                self.truncate(new_len);
            }
        }
    }

    pub fn splice<'a, R, I>(
        &mut self,
        mutator: &'a mut Heap,
        range: R,
        replace_with: I,
    ) -> Splice<'a, <I as IntoIterator>::IntoIter>
    where
        I: IntoIterator<Item = T>,

        R: core::ops::RangeBounds<usize>,
    {
        let len = self.len();

        let start_idx = match range.start_bound() {
            core::ops::Bound::Included(&n) => n,
            core::ops::Bound::Excluded(&n) => {
                n.checked_add(1).expect("Start idx exceeded numeric limits")
            }
            core::ops::Bound::Unbounded => 0,
        };

        let end_idx = match range.end_bound() {
            core::ops::Bound::Included(&n) => {
                n.checked_add(1).expect("End idx exceeded numeric limits")
            }
            core::ops::Bound::Excluded(&n) => n,
            core::ops::Bound::Unbounded => len,
        };

        assert!(
            (start_idx <= end_idx),
            "start splice index (is {}) should be <= end splice index (is {})",
            start_idx,
            end_idx
        );

        assert!(
            (end_idx <= len),
            "end splice index (is {}) should be <= len (is {})",
            end_idx,
            len
        );

        let data = self.as_mut_ptr();

        if !data.is_null() {
            unsafe {
                self.set_len(start_idx);
            }
        }

        make_splice_iterator(
            self,
            data,
            len - end_idx,
            start_idx,
            end_idx,
            replace_with.into_iter(),
            mutator,
        )
    }
    #[allow(clippy::ptr_as_ptr)]
    pub fn split_off(&mut self, mutator: &mut Heap, at: usize) -> Self {
        let len = self.len();

        assert!(
            (at <= len),
            "`at` split index (is {}) should be <= len (is {})",
            at,
            len
        );

        if len == 0 {
            let other = if self.capacity() > 0 {
                Self::with_capacity(mutator, self.capacity())
            } else {
                Self::new(mutator)
            };

            return other;
        }

        if at == 0 {
            let orig_cap = self.capacity();

            let other = Self {
                storage: self.storage,
            };

            self.storage = Storage::new(mutator, 0);
            self.reserve_exact(mutator, orig_cap);

            return other;
        }
        let mut other = Self::with_capacity(mutator, self.capacity());
        unsafe {
            self.set_len(at);
            other.set_len(len - at);
        }

        let src = unsafe { self.as_ptr().add(at) };
        let dst = other.as_mut_ptr();
        let count = len - at;

        unsafe {
            core::ptr::copy_nonoverlapping(src, dst, count);
        }

        other
    }
    /// `reserve_exact` ensures that the capacity of the GcVec is exactly equal to
    /// `len() + additional` unless the capacity is already sufficient in which case no operation is
    /// performed.
    ///
    pub fn reserve_exact(&mut self, mutator: &mut Heap, additional: usize) {
        let capacity = self.capacity();
        let len = self.len();

        let total_required = len + additional;
        if capacity >= total_required {
            return;
        }

        self.grow(mutator, total_required);
    }

    /// `truncate` adjusts the length of the GcVec to be `len`. If `len` is greater than or equal
    /// to the current length no operation is performed. Otherwise, the GcVec's length is
    /// readjusted to `len` and any remaining elements to the right of `len` are dropped.
    pub fn truncate(&mut self, len: usize) {
        let self_len = self.len();
        if len >= self_len {
            return;
        }

        self.storage.len = len;
        if !core::mem::needs_drop::<T>() {
            return;
        }

        let s = unsafe { std::slice::from_raw_parts_mut(self.data().add(len), self_len - len) };
        unsafe {
            core::ptr::drop_in_place(s);
        }
    }

    /// Pushes value to GcVec without check for overflow and allocating more space.
    ///
    /// # Safety
    /// Unsafe to call because it can overflow and write to unprotected memory
    pub unsafe fn push_no_grow(&mut self, value: T) {
        let len = self.len();

        let data = self.data();

        data.add(len).write(value);

        self.storage.len += 1;
    }
    /// `push` appends an element `value` to the end of the GcVec. `push` automatically reallocates
    /// if the GcVec does not have sufficient capacity.
    pub fn push(&mut self, mutator: &mut Heap, value: T) {
        let len = self.len();
        let cap = self.capacity();

        if len == cap {
            self.grow(mutator, next_capacity::<T>(cap));
        }

        let data = self.data();
        unsafe {
            data.add(len).write(value);
        }
        self.storage.len += 1;
    }
    pub fn extend_from_slice(&mut self, mutator: &mut Heap, slice: &[T])
    where
        T: Clone,
    {
        self.reserve(mutator, slice.len());
        for x in (*slice).iter() {
            self.push(mutator, (*x).clone());
        }
    }
    pub fn pop(&mut self) -> Option<T> {
        let len = self.len();
        if len == 0 {
            return None;
        }

        unsafe {
            let v = self.as_ptr().add(len - 1).read();
            self.storage.len -= 1;
            Some(v)
        }
    }

    pub unsafe fn set_len(&mut self, len: usize) {
        self.storage.len = len;
    }

    pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();

        assert!(
            (index < len),
            "removal index (is {}) should be < len (is {})",
            index,
            len
        );

        unsafe {
            let p = self.as_mut_ptr().add(index);

            let x = core::ptr::read(p);

            let src = p.add(1);
            let dst = p;
            let count = len - index - 1;
            core::ptr::copy(src, dst, count);

            self.set_len(len - 1);

            x
        }
    }

    /// `remove_item` removes the first element identical to the supplied `item` using a
    /// left-to-right traversal of the elements.
    ///
    pub fn remove_item<V>(&mut self, item: &V) -> Option<T>
    where
        T: PartialEq<V>,
    {
        let len = self.len();
        for i in 0..len {
            if &self[i] == item {
                return Some(self.remove(i));
            }
        }
        None
    }
    pub fn try_reserve(&mut self, mutator: &mut Heap, additional: usize) {
        let capacity = self.capacity();
        let total_required = self.len().saturating_add(additional);

        if total_required <= capacity {
            return;
        }

        let mut new_capacity = next_capacity::<T>(capacity);
        while new_capacity < total_required {
            new_capacity = next_capacity::<T>(new_capacity);
        }

        self.grow(mutator, new_capacity);
    }
}

#[repr(C)]
struct Storage<T> {
    len: usize,
    cap: usize,
    data: [MaybeUninit<T>; 0],
}

impl<T: 'static> Storage<T> {
    fn new(heap: &mut Heap, cap: usize) -> Gc<Self> {
        unsafe {
            heap.allocate_var(
                Self {
                    len: 0,
                    cap,
                    data: [],
                },
                ValueType::GcVec as _,
                false,
                false,
                size_of::<Self>() + (cap * size_of::<T>()),
            )
        }
    }
}
const fn next_capacity<T>(capacity: usize) -> usize {
    let elem_size = core::mem::size_of::<T>();

    if capacity == 0 {
        return match elem_size {
            1 => 8,
            2..=1024 => 4,
            _ => 1,
        };
    }

    2 * capacity
}

impl<T: std::fmt::Debug + 'static> std::fmt::Debug for GcVec<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "GcVec[")?;
        for i in 0..self.len() {
            write!(f, "{:?}", self[i])?;
            if i != self.len() - 1 {
                write!(f, ",")?;
            }
        }

        write!(f, "]")
    }
}

impl<T: PartialEq + 'static> PartialEq for GcVec<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        for i in 0..self.len() {
            if self[i] != other[i] {
                return false;
            }
        }
        true
    }
}

impl<T: Eq + 'static> Eq for GcVec<T> {}

impl<T: 'static, I> core::ops::Index<I> for GcVec<T>
where
    I: core::slice::SliceIndex<[T]>,
{
    type Output = <I as core::slice::SliceIndex<[T]>>::Output;

    fn index(&self, index: I) -> &<GcVec<T> as core::ops::Index<I>>::Output {
        let v: &[T] = &**self;
        core::ops::Index::index(v, index)
    }
}

impl<T: 'static, I> core::ops::IndexMut<I> for GcVec<T>
where
    I: core::slice::SliceIndex<[T]>,
{
    fn index_mut(&mut self, index: I) -> &mut <GcVec<T> as core::ops::Index<I>>::Output {
        let v: &mut [T] = &mut **self;
        core::ops::IndexMut::index_mut(v, index)
    }
}

impl<T: 'static> core::ops::Deref for GcVec<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        let data = self.data();
        let len = self.len();
        unsafe { core::slice::from_raw_parts(data, len) }
    }
}

impl<T: 'static> core::ops::DerefMut for GcVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let data = self.data();
        let len = self.len();
        unsafe { core::slice::from_raw_parts_mut(data, len) }
    }
}

impl<T: 'static> core::hash::Hash for GcVec<T>
where
    T: core::hash::Hash,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: core::hash::Hasher,
    {
        let this: &[T] = &**self;
        core::hash::Hash::hash(this, state);
    }
}

/// `Splice` is an iterator that removes a sub-section of the backing `MiniVec` and then replaces it with the contents
/// of another iterator. The removed sub-section and the iterator used to replace it can have independent lengths.
///
pub struct Splice<'a, I>
where
    I: 'a + Iterator,

    <I as Iterator>::Item: 'static,
{
    vec_: core::ptr::NonNull<GcVec<I::Item>>,
    drain_pos_: core::ptr::NonNull<I::Item>,
    drain_end_: core::ptr::NonNull<I::Item>,
    remaining_pos_: core::ptr::NonNull<I::Item>,
    remaining_: usize,
    marker_: core::marker::PhantomData<&'a I::Item>,
    fill_: I,
    mutator: &'a mut Heap,
}

pub fn make_splice_iterator<'a, I: 'a + Iterator>(
    vec: &mut GcVec<I::Item>,
    data: *mut I::Item,
    remaining: usize,
    start_idx: usize,
    end_idx: usize,
    fill: I,
    mutator: &'a mut Heap,
) -> Splice<'a, I>
where
    <I as Iterator>::Item: 'static,
{
    if data.is_null() {
        let dangling = core::ptr::NonNull::<I::Item>::dangling();

        Splice {
            vec_: core::ptr::NonNull::from(vec),
            drain_pos_: dangling,
            drain_end_: dangling,
            remaining_pos_: dangling,
            remaining_: 0,
            marker_: core::marker::PhantomData,
            fill_: fill,
            mutator,
        }
    } else {
        Splice {
            vec_: core::ptr::NonNull::from(vec),
            drain_pos_: unsafe { core::ptr::NonNull::new_unchecked(data.add(start_idx)) },
            drain_end_: unsafe { core::ptr::NonNull::new_unchecked(data.add(end_idx)) },
            remaining_pos_: unsafe { core::ptr::NonNull::new_unchecked(data.add(end_idx)) },
            remaining_: remaining,
            marker_: core::marker::PhantomData,
            fill_: fill,
            mutator,
        }
    }
}

impl<I> Iterator for Splice<'_, I>
where
    I: Iterator,
    <I as Iterator>::Item: 'static,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.drain_pos_ >= self.drain_end_ {
            return None;
        }

        let p = self.drain_pos_.as_ptr();
        let tmp = unsafe { core::ptr::read(p) };
        self.drain_pos_ = unsafe { core::ptr::NonNull::new_unchecked(p.add(1)) };
        Some(tmp)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = (self.drain_end_.as_ptr() as *const _ as usize
            - self.drain_pos_.as_ptr() as *const _ as usize)
            / core::mem::size_of::<I::Item>();

        (len, Some(len))
    }
}

impl<I: Iterator> ExactSizeIterator for Splice<'_, I> where <I as Iterator>::Item: 'static {}

impl<I> DoubleEndedIterator for Splice<'_, I>
where
    I: Iterator,
    <I as Iterator>::Item: 'static,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let pos = unsafe { self.drain_end_.as_ptr().sub(1) };
        if pos < self.drain_pos_.as_ptr() {
            return None;
        }

        let tmp = unsafe { core::ptr::read(pos) };
        self.drain_end_ = unsafe { core::ptr::NonNull::new_unchecked(pos) };
        Some(tmp)
    }
}

struct DropGuard<'b, 'a, I>
where
    I: Iterator,
    <I as Iterator>::Item: 'static,
{
    splice: &'b mut Splice<'a, I>,
}

impl<'b, 'a, I> Drop for DropGuard<'b, 'a, I>
where
    I: Iterator,
    <I as Iterator>::Item: 'static,
{
    fn drop(&mut self) {
        // much like Drain, remove the rest of the elements from the splice range if they
        // haven't already been exhausted
        //
        for x in &mut self.splice {
            core::mem::drop(x);
        }

        let vec = unsafe { self.splice.vec_.as_mut() };

        // first, figure out where our draining operation started
        // this is at offset vec.len() from the start of [T]'s data
        //
        let drain_begin = unsafe { vec.as_mut_ptr().add(vec.len()) };

        // infer the number of items we drained by where the remaining_pos_ is
        //
        let num_drained = (self.splice.remaining_pos_.as_ptr() as usize - drain_begin as usize)
            / core::mem::size_of::<I::Item>();

        // fill the drained sub-section using the iterator the user supplied
        // if the iterator, for example, has more elements than the draiend region allows,
        // we need to know this so we can reallocate the GcVec accordingly
        //
        let needs_more = {
            let mut needs_more = true;
            for idx in 0..num_drained {
                if let Some(val) = self.splice.fill_.next() {
                    unsafe {
                        core::ptr::write(drain_begin.add(idx), val);
                        vec.set_len(vec.len() + 1);
                    };
                } else {
                    needs_more = false;
                }
            }

            needs_more
        };

        // if we don't have any more elements in the iterator the user supplied, we can
        // go ahead and shift the tail down
        //
        if !needs_more {
            // if the supplied iterator had exactly the number of elements that we drained,
            // we don't need to memcpy and can instead just adjust the length of the GcVec
            // and return
            //
            if unsafe { vec.as_ptr().add(vec.len()) == self.splice.remaining_pos_.as_ptr() } {
                unsafe {
                    vec.set_len(vec.len() + self.splice.remaining_);
                }
                return;
            }

            // we need to copy things down from Drain's "tail" to where our iterator left
            // off in the drained range
            // this basically downshifts the elements from right-to-left so it's safe to
            // call `core::ptr::copy`
            //
            let src = self.splice.remaining_pos_.as_ptr();
            let dst = unsafe { vec.as_mut_ptr().add(vec.len()) };
            let count = self.splice.remaining_;
            unsafe {
                core::ptr::copy(src, dst, count);
                vec.set_len(vec.len() + self.splice.remaining_);
            };

            return;
        }

        // we need to handle the rest of the iterator's elements now
        // pool them into a temporary GcVec for storage
        //
        let mut tmp: GcVec<_> = GcVec::new(&mut self.splice.mutator); // (&mut self.splice.fill_).collect();
        for x in &mut self.splice.fill_ {
            tmp.push(&mut self.splice.mutator, x);
        }
        // reserve extra capacity if required
        // note, this will invalidate all of our previously cached pointers in the Splice
        // iterator so we have to store the offset of the drain tail manually
        //
        let capacity = vec.capacity();
        let remaining_offset = (self.splice.remaining_pos_.as_ptr() as usize
            - vec.as_ptr() as usize)
            / core::mem::size_of::<I::Item>();

        // if our GcVec's length + the remaining elements + the extra tmp length exceeds
        // our capacity we need to reallocate
        //
        let total_elements = vec.len() + self.splice.remaining_ + tmp.len();

        if total_elements > capacity {
            vec.grow(&mut self.splice.mutator, total_elements)
        }

        // let's first move the Drain tail over to the right
        // we know our Drain's tail starts at the `remaining_offset` and we have to copy
        // self.splice.remaining_ elements over starting at the offset of our current len
        // plus the tail len
        //
        if self.splice.remaining_ > 0 {
            unsafe {
                let src = vec.as_ptr().add(remaining_offset);
                let dst = vec.as_mut_ptr().add(vec.len() + tmp.len());
                let count = self.splice.remaining_;
                core::ptr::copy(src, dst, count);
            };
        }

        // finally we copy the remaining tmp elements into the GcVec and then we make sure
        // to set its length to 0 to prevent any sort of double-frees
        //
        if !tmp.is_empty() {
            unsafe {
                let src = tmp.as_ptr();
                let dst = vec.as_mut_ptr().add(vec.len());
                let count = tmp.len();
                core::ptr::copy(src, dst, count);
            };
        }

        unsafe {
            vec.set_len(vec.len() + self.splice.remaining_ + tmp.len());
            if !tmp.is_empty() {
                tmp.set_len(0);
            }
        };
    }
}

impl<I: Iterator> Drop for Splice<'_, I>
where
    <I as Iterator>::Item: 'static,
{
    fn drop(&mut self) {
        while let Some(item) = self.next() {
            let guard = DropGuard { splice: self };
            drop(item);
            core::mem::forget(guard);
        }

        DropGuard { splice: self };
    }
}
