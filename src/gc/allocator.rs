use super::mmap::Mmap;
use core::{mem::size_of, ptr::null_mut};
use indexmap::IndexSet;

pub const KB: usize = 1024;
pub const MB: usize = KB * KB;
pub const GB: usize = 1024 * MB;

pub const MIN_ALLOCATION: usize = 16;

pub const BLOCK_SIZE: usize = 8 * 1024;

pub const BRACKET_SIZES: [usize; NUM_OF_SIZE_BRACKETS] = {
    let mut bracket_sizes: [usize; NUM_OF_SIZE_BRACKETS] = [0; NUM_OF_SIZE_BRACKETS];
    let mut i = 0;
    while i < NUM_OF_SIZE_BRACKETS {
        if i < NUM_THREAD_LOCAL_SIZE_BRACKETS {
            bracket_sizes[i] = THREAD_LOCAL_BRACKET_QUANTUM_SIZE * (i + 1);
        } else if i < NUM_REGULAR_SIZE_BRACKETS {
            bracket_sizes[i] = BRACKET_QUANTUM_SIZE * (i - NUM_THREAD_LOCAL_SIZE_BRACKETS + 1)
                + (THREAD_LOCAL_BRACKET_QUANTUM_SIZE * NUM_THREAD_LOCAL_SIZE_BRACKETS);
        } else if i == NUM_OF_SIZE_BRACKETS - 2 {
            bracket_sizes[i] = 1 * KB;
        } else {
            bracket_sizes[i] = 2 * KB;
        }
        i += 1;
    }
    bracket_sizes
};

pub const NUM_OF_PAGES: [usize; NUM_OF_SIZE_BRACKETS] = {
    let mut num_of_pages: [usize; NUM_OF_SIZE_BRACKETS] = [0; NUM_OF_SIZE_BRACKETS];
    let mut i = 0;
    while i < NUM_OF_SIZE_BRACKETS {
        if i < NUM_THREAD_LOCAL_SIZE_BRACKETS {
            num_of_pages[i] = 1;
        } else if i < ((NUM_THREAD_LOCAL_SIZE_BRACKETS + NUM_REGULAR_SIZE_BRACKETS) / 2) {
            num_of_pages[i] = 1;
        } else if i < NUM_REGULAR_SIZE_BRACKETS {
            num_of_pages[i] = 1;
        } else if i == NUM_OF_SIZE_BRACKETS - 2 {
            num_of_pages[i] = 2;
        } else {
            num_of_pages[i] = 4;
        }
        i += 1;
    }
    num_of_pages
};

pub const NUM_OF_SLOTS: [usize; NUM_OF_SIZE_BRACKETS] = {
    let mut num_of_slotsc: [usize; NUM_OF_SIZE_BRACKETS] = [0; NUM_OF_SIZE_BRACKETS];
    let mut header_sizes = [0; NUM_OF_SIZE_BRACKETS];
    let mut i = 0;
    while i < NUM_OF_SIZE_BRACKETS {
        let bracket_size = BRACKET_SIZES[i];
        let run_size = PAGE_SIZE * NUM_OF_PAGES[i];
        let max_num_of_slots = run_size / bracket_size;

        let fixed_header_size =
            round_up(Run::fixed_header_size() as _, size_of::<u64>() as _) as usize;
        let mut header_size = 0;
        let mut num_of_slots = 0;

        let mut s = max_num_of_slots as isize;

        while s >= 0 {
            let tmp_slots_size = bracket_size * s as usize;
            let tmp_unaligned_header_size = fixed_header_size;

            let tmp_header_size = if tmp_unaligned_header_size % bracket_size == 0 {
                tmp_unaligned_header_size
            } else {
                tmp_unaligned_header_size
                    + (bracket_size - tmp_unaligned_header_size % bracket_size)
            };

            if tmp_slots_size + tmp_header_size <= run_size {
                num_of_slots = s as _;
                header_size = tmp_header_size;
                break;
            }
            s -= 1;
        }
        header_size += run_size % bracket_size;
        num_of_slotsc[i] = num_of_slots;
        header_sizes[i] = header_size;
        i += 1;
    }
    let _ = header_sizes;
    num_of_slotsc
};

pub const DEFAULT_PAGE_RELEASE_THRESHOLD: usize = 4 * MB;
pub const NUM_THREAD_LOCAL_SIZE_BRACKETS: usize = 16;
pub const MAX_THREAD_LOCAL_BRACKET_SIZE: usize = 128;
pub const NUM_REGULAR_SIZE_BRACKETS: usize = 39;
pub const MAX_REGULAR_BRACKET_SIZE: usize = 512;
pub const THREAD_LOCAL_BRACKET_QUANTUM_SIZE: usize = 8;
pub const BRACKET_QUANTUM_SIZE: usize = 16;
pub const BRACKET_QUANTUM_SIZE_SHIFT: usize = 4;
pub const MAGIC_NUM: u8 = 42;
pub const MAGIC_NUM_FREE: u8 = 43;
pub const NUM_OF_SIZE_BRACKETS: usize = 42;
pub const PAGE_SIZE: usize = 4 * KB;

pub const HEADER_SIZES: [usize; NUM_OF_SIZE_BRACKETS] = {
    let mut num_of_slotsc: [usize; NUM_OF_SIZE_BRACKETS] = [0; NUM_OF_SIZE_BRACKETS];
    let mut header_sizes = [0; NUM_OF_SIZE_BRACKETS];
    let mut i = 0;
    while i < NUM_OF_SIZE_BRACKETS {
        let bracket_size = BRACKET_SIZES[i];
        let run_size = PAGE_SIZE * NUM_OF_PAGES[i];
        let max_num_of_slots = run_size / bracket_size;

        let fixed_header_size =
            round_up(Run::fixed_header_size() as _, size_of::<u64>() as _) as usize;
        let mut header_size = 0;
        let mut num_of_slots = 0;

        let mut s = max_num_of_slots as isize;

        while s >= 0 {
            let tmp_slots_size = bracket_size * s as usize;
            let tmp_unaligned_header_size = fixed_header_size;

            let tmp_header_size = if tmp_unaligned_header_size % bracket_size == 0 {
                tmp_unaligned_header_size
            } else {
                tmp_unaligned_header_size
                    + (bracket_size - tmp_unaligned_header_size % bracket_size)
            };

            if tmp_slots_size + tmp_header_size <= run_size {
                num_of_slots = s as _;
                header_size = tmp_header_size;
                break;
            }
            s -= 1;
        }
        header_size += run_size % bracket_size;
        num_of_slotsc[i] = num_of_slots;
        header_sizes[i] = header_size;
        i += 1;
    }
    let _ = num_of_slotsc;
    header_sizes
};

#[repr(C)]
pub struct Run {
    magic_num: u8,
    next: *mut Self,
    size_bracket_index: u8,
    free_list: SlotFreeList<false>,
    bulk_free_list: SlotFreeList<true>,
}

impl Run {
    #[inline]
    pub fn is_full(&self) -> bool {
        self.free_list.size() == 0
    }
    #[inline]
    pub fn merge_bulk_free_list_to_free_list(&mut self) {
        let mut list = std::mem::replace(&mut self.bulk_free_list, SlotFreeList::new());
        self.free_list.merge(&mut list);
        self.bulk_free_list = list;
    }

    #[inline]
    pub unsafe fn slot_from_ptr(&self, ptr: *const u8) -> *mut u8 {
        let sz = *BRACKET_SIZES.get_unchecked(self.size_bracket_index as usize);
        let ix = (ptr as usize).wrapping_sub(self.first_slot() as usize) / sz;
        let p = self.first_slot().add(ix * sz);
        p
    }

    #[inline]
    pub unsafe fn to_slot(&self, ptr: *const u8) -> *mut u8 {
        let idx = self.size_bracket_index as usize;
        let bracket_size = *BRACKET_SIZES.get_unchecked(idx);
        let offset_from_slot_base = ptr as usize - self.first_slot() as usize;
        debug_assert_eq!(
            offset_from_slot_base % bracket_size,
            0,
            "run {:p}, ptr {:p}",
            self,
            ptr
        );
        let slot_idx = offset_from_slot_base / bracket_size;
        debug_assert!(slot_idx < NUM_OF_SLOTS[idx]);
        ptr as _
    }
    #[inline]
    pub unsafe fn slot_index(&self, ptr: *const u8) -> usize {
        let idx = self.size_bracket_index as usize;
        let bracket_size = *BRACKET_SIZES.get_unchecked(idx);
        let offset_from_slot_base = ptr as usize - self.first_slot() as usize;
        debug_assert_eq!(offset_from_slot_base % bracket_size, 0);
        let slot_idx = offset_from_slot_base / bracket_size;
        debug_assert!(slot_idx < NUM_OF_SLOTS[idx]);
        slot_idx
    }
    pub const fn fixed_header_size() -> usize {
        size_of::<Self>()
    }

    pub fn first_slot(&self) -> *mut u8 {
        unsafe {
            (self as *const Self as *mut u8).add(HEADER_SIZES[self.size_bracket_index as usize])
        }
    }
    #[inline]
    pub fn end(&self) -> *mut u8 {
        (self as *const Self as usize + PAGE_SIZE * NUM_OF_PAGES[self.size_bracket_index as usize])
            as _
    }

    #[inline]
    pub unsafe fn last_slot(&self) -> *mut u8 {
        let idx = self.size_bracket_index as usize;
        let bracket_size = *BRACKET_SIZES.get_unchecked(idx);
        let end = self.end();
        let last_slot = end.sub(bracket_size);
        debug_assert!(self.first_slot() <= last_slot);
        last_slot
    }

    pub unsafe fn alloc(&mut self) -> *mut u8 {
        self.free_list.remove().cast()
    }

    #[inline]
    pub unsafe fn add_to_free_list_shared(
        &mut self,
        ptr: *mut u8,
        free_list: *mut SlotFreeList<true>,
    ) -> usize {
        let idx = self.size_bracket_index as usize;
        let bracket_size = *BRACKET_SIZES.get_unchecked(idx);

        let slot = self.to_slot(ptr);
        memx::memset(std::slice::from_raw_parts_mut(slot.cast(), bracket_size), 0);
        (*free_list).add(slot.cast());

        bracket_size
    }
    #[inline]
    pub unsafe fn add_to_bulk_free_list(&mut self, ptr: *mut u8) -> usize {
        let list = &mut self.bulk_free_list as *mut _;
        self.add_to_free_list_shared(ptr, list)
    }

    pub fn is_all_free(&self) -> bool {
        self.free_list.size() == NUM_OF_SLOTS[self.size_bracket_index as usize]
    }
    pub unsafe fn init_free_list(&mut self) {
        let idx = self.size_bracket_index as usize;
        let br_size = BRACKET_SIZES[idx];
        let first_slot = self.first_slot();
        let mut slot = self.last_slot();

        while slot >= first_slot {
            self.free_list.add(slot.cast());
            slot = slot.sub(br_size);
        }
    }
    #[inline]
    pub fn zero_header_and_slot_headers(&mut self) {
        let idx = self.size_bracket_index as usize;
        let mut slot = self.free_list.head();
        while !slot.is_null() {
            unsafe {
                let next_slot = (*slot).next();
                (*slot).clear();
                slot = next_slot;
            }
        }

        unsafe {
            memx::memset(
                std::slice::from_raw_parts_mut(self as *mut Self as *mut u8, HEADER_SIZES[idx]),
                0,
            );

            if cfg!(debug_assertions) {
                let size = NUM_OF_PAGES[idx] * PAGE_SIZE;
                let word_ptr = self as *mut Self as *mut usize;
                for i in 0..(size / size_of::<usize>()) {
                    assert_eq!(word_ptr.add(i).read(), 0);
                }
            }
        }
    }
}

pub struct FreeRun {
    magic_num: u8,
}

impl FreeRun {
    pub unsafe fn is_at_end_of_space(&self, rosalloc: &GcAllocator) -> bool {
        self as *const Self as usize + self.byte_size(rosalloc)
            == rosalloc.base as usize + rosalloc.size
    }

    pub fn should_release_pages(&self, heap: &GcAllocator) -> bool {
        unsafe {
            match heap.page_release_mode {
                PageReleaseMode::All => true,
                PageReleaseMode::None => false,
                PageReleaseMode::End => self.is_at_end_of_space(heap),
                PageReleaseMode::Size => self.byte_size(heap) >= heap.page_release_threshold,
                PageReleaseMode::SizeAndEnd => {
                    self.is_at_end_of_space(heap)
                        && self.byte_size(heap) >= heap.page_release_threshold
                }
            }
        }
    }

    pub unsafe fn release_pages(&self, rosalloc: &mut GcAllocator) {
        let start = self as *const Self as *mut u8;
        let byte_size = self.byte_size(rosalloc);
        if self.should_release_pages(rosalloc) {
            rosalloc.release_page_range(start, (start as usize + byte_size) as _);
        }
    }
    pub fn begin(&self) -> *mut u8 {
        self as *const Self as _
    }

    pub fn end(&self, heap: &GcAllocator) -> *mut u8 {
        unsafe { (self as *const Self as *mut u8).add(self.byte_size(heap)) }
    }

    pub unsafe fn byte_size(&self, heap: &GcAllocator) -> usize {
        let base = self.begin();

        let pm_idx = heap.to_page_map_index(base);
        heap.free_page_run_size_map[pm_idx]
    }

    pub unsafe fn set_byte_size(&self, heap: &mut GcAllocator, byte_size: usize) {
        let base = self.begin();
        let pm_idx = heap.to_page_map_index(base);

        heap.free_page_run_size_map[pm_idx] = byte_size;
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PageReleaseMode {
    None,
    Size,
    SizeAndEnd,
    End,
    All,
}

#[allow(dead_code)]
pub struct GcAllocator {
    mmap: Mmap,
    base: *mut u8,
    size: usize,

    current_runs: [*mut Run; BRACKET_SIZES.len()],

    free_page_runs: IndexSet<*mut FreeRun>,
    free_page_run_size_map: Vec<usize>,
    page_map: *mut u8,
    page_map_size: usize,

    page_map_mmap: Mmap,
    page_release_mode: PageReleaseMode,
    page_release_threshold: usize,

    non_full_runs: [IndexSet<*mut Run>; BRACKET_SIZES.len()],
}

#[inline(always)]
pub const fn round_down(x: u64, n: u64) -> u64 {
    let x = x as i64;
    let n = n as i64;
    (x & -n) as u64
}

#[inline(always)]
pub const fn round_up(x: u64, n: u64) -> u64 {
    round_down(x.wrapping_add(n).wrapping_sub(1), n)
    //round_down(x + n - 1, n)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum PageMapKind {
    Empty,
    Released,
    Run,
    RunPart,
    LargeObject,
    LargeObjectPart,
}

impl GcAllocator {
    #[inline]
    pub const fn bracket_size_to_index(size: usize) -> usize {
        let idx;
        if size == 1 * KB {
            idx = NUM_OF_SIZE_BRACKETS - 2;
        } else if size == 2 * KB {
            idx = NUM_OF_SIZE_BRACKETS - 1;
        } else if size <= MAX_THREAD_LOCAL_BRACKET_SIZE {
            idx = size / THREAD_LOCAL_BRACKET_QUANTUM_SIZE - 1;
        } else {
            idx = ((size - MAX_THREAD_LOCAL_BRACKET_SIZE) / BRACKET_QUANTUM_SIZE - 1)
                + NUM_THREAD_LOCAL_SIZE_BRACKETS;
        }

        idx
    }

    #[inline]
    pub const fn round_to_bracket_size(size: usize) -> usize {
        if size <= MAX_THREAD_LOCAL_BRACKET_SIZE {
            round_up(size as _, THREAD_LOCAL_BRACKET_QUANTUM_SIZE as _) as _
        } else if size <= MAX_REGULAR_BRACKET_SIZE {
            round_up(size as _, BRACKET_QUANTUM_SIZE as _) as _
        } else if size <= 1 * KB {
            1 * KB
        } else {
            2 * KB
        }
    }

    #[inline]
    pub const fn size_to_index(size: usize) -> usize {
        if size <= MAX_THREAD_LOCAL_BRACKET_SIZE {
            round_up(size as _, THREAD_LOCAL_BRACKET_QUANTUM_SIZE as _) as usize
                / THREAD_LOCAL_BRACKET_QUANTUM_SIZE
                - 1
        } else if size <= MAX_REGULAR_BRACKET_SIZE {
            (round_up(size as _, BRACKET_QUANTUM_SIZE as _) as usize
                - MAX_THREAD_LOCAL_BRACKET_SIZE)
                / BRACKET_QUANTUM_SIZE
                - 1
                + NUM_THREAD_LOCAL_SIZE_BRACKETS
        } else if size <= 1 * KB {
            NUM_OF_SIZE_BRACKETS - 2
        } else {
            NUM_OF_SIZE_BRACKETS - 1
        }
    }

    #[inline]
    pub const fn size_to_index_and_bracket_size(size: usize) -> (usize, usize) {
        (Self::size_to_index(size), Self::round_to_bracket_size(size))
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn base(&self) -> *mut u8 {
        self.base
    }

    pub unsafe fn new(
        size: usize,
        page_release_mode: PageReleaseMode,
        page_release_threshold: usize,
    ) -> Self {
        let size = round_up(size as _, PAGE_SIZE as _) as usize;
        let map = Mmap::new(size, PAGE_SIZE);
        let num_of_pages = size / PAGE_SIZE;
        let page_map = Mmap::new(round_up(num_of_pages as _, PAGE_SIZE as _) as _, PAGE_SIZE);

        let base = map.start();
        let mut free_pages = base.cast::<FreeRun>();

        (*free_pages).magic_num = 0x42;
        let free_page_run_size_map = vec![0usize; num_of_pages];
        let mut free_page_runs = IndexSet::with_capacity(num_of_pages);

        free_page_runs.insert(free_pages);
        let mut this = Self {
            base,
            free_page_runs,
            free_page_run_size_map,
            mmap: map,
            page_map: page_map.start(),
            page_map_mmap: page_map,
            page_map_size: num_of_pages,

            current_runs: [&mut DEDICATED_FULL_RUN; 42],
            size,
            page_release_threshold,
            page_release_mode,

            non_full_runs: [(); 42].map(|_| IndexSet::new()),
        };
        (*free_pages).set_byte_size(&mut this, size);

        this
    }

    #[inline]
    pub fn round_down_to_page_map_index(&self, addr: *const u8) -> usize {
        (addr as usize - self.base as usize) / PAGE_SIZE
    }

    pub unsafe fn alloc_pages(&mut self, num_pages: usize, page_map_type: PageMapKind) -> *mut u8 {
        let mut res = null_mut();

        let req_byte_size = num_pages * PAGE_SIZE;
        let mut i = 0;
        loop {
            if i >= self.free_page_runs.len() {
                break;
            }
            let fpr = *self.free_page_runs.get_index(i).unwrap_unchecked();

            let fpr_byte_size = (*fpr).byte_size(self);

            if req_byte_size <= fpr_byte_size {
                self.free_page_runs.remove(&fpr);

                if req_byte_size < fpr_byte_size {
                    let remainder = fpr.cast::<u8>().add(req_byte_size).cast::<FreeRun>();
                    if cfg!(debug_assertions) {
                        (*remainder).magic_num = MAGIC_NUM_FREE;
                    }
                    (*remainder).set_byte_size(self, fpr_byte_size - req_byte_size);
                    self.free_page_runs.insert(remainder);

                    (*fpr).set_byte_size(self, req_byte_size);
                }
                res = fpr.cast::<u8>();
            }
            i += 1;
        }
        if !res.is_null() {
            let page_map_idx = self.to_page_map_index(res);

            match page_map_type {
                x if x as u8 == PageMapKind::Run as u8 => {
                    self.page_map.add(page_map_idx).write(PageMapKind::Run as _);
                    for i in 1..num_pages {
                        self.page_map
                            .add(page_map_idx + i)
                            .write(PageMapKind::RunPart as _);
                    }
                }
                x if x as u8 == PageMapKind::LargeObject as u8 => {
                    self.page_map
                        .add(page_map_idx)
                        .write(PageMapKind::LargeObject as _);
                    for i in 1..num_pages {
                        self.page_map
                            .add(page_map_idx + i)
                            .write(PageMapKind::LargeObjectPart as _);
                    }
                }
                _ => {
                    unreachable!()
                }
            }

            return res.cast();
        }
        res
    }

    #[inline]
    pub fn to_page_map_index(&self, addr: *const u8) -> usize {
        let byte_offset = addr as usize - self.base as usize;
        byte_offset / PAGE_SIZE
    }
    #[inline]
    pub unsafe fn page_map_kind_at(&self, idx: usize) -> PageMapKind {
        self.page_map.add(idx).cast::<PageMapKind>().read()
    }

    #[inline]
    pub unsafe fn page_map_kind(&self, ptr: *mut u8) -> PageMapKind {
        let idx = self.to_page_map_index(ptr);
        self.page_map.add(idx).cast::<PageMapKind>().read()
    }
    unsafe fn alloc_run(&mut self, index: usize) -> *mut Run {
        let run = self
            .alloc_pages(NUM_OF_PAGES[index], PageMapKind::Run)
            .cast::<Run>();

        if run.is_null() {
            return run;
        }

        (*run).magic_num = 0;
        (*run).free_list = SlotFreeList::new();
        (*run).bulk_free_list = SlotFreeList::new();
        (*run).size_bracket_index = index as _;
        (*run).next = null_mut();
        (*run).init_free_list();
        run
    }

    unsafe fn alloc_large(&mut self, size: usize, bulk_allocated: &mut usize) -> *mut u8 {
        let num_pages = round_up(size as _, PAGE_SIZE as _) as usize / PAGE_SIZE;

        let r = self.alloc_pages(num_pages, PageMapKind::LargeObject);

        if !r.is_null() {
            *bulk_allocated += num_pages * PAGE_SIZE;
        }
        r
    }
    pub unsafe fn refill_run(&mut self, idx: usize) -> *mut Run {
        let bt = &mut self.non_full_runs[idx];
        if !bt.is_empty() {
            let it = bt.first().unwrap_unchecked();
            let non_full_run = *it;

            bt.remove(&non_full_run);
            return non_full_run;
        }
        self.alloc_run(idx)
    }
    #[inline]
    unsafe fn alloc_raw_from_run(&mut self, size: usize, bulk_allocated: &mut usize) -> *mut u8 {
        let (index, sz) = Self::size_to_index_and_bracket_size(size);
        let mut current_run = self.current_runs[index];
        let slot_addr = (*current_run).alloc();
        if !slot_addr.is_null() {
            *bulk_allocated += sz;
            return slot_addr;
        }

        current_run = self.refill_run(index);

        if current_run.is_null() {
            self.current_runs[index] = &mut DEDICATED_FULL_RUN;
            return null_mut();
        }
        *bulk_allocated += sz;
        self.current_runs[index] = current_run;
        (*current_run).alloc()
    }

    /// Allocates `size` bytes on the heap and increments `bulk_allocated` if new memory was allocated.
    ///
    /// Memory is considered new if:
    /// 1) it is new pages or new run, then bulk_allocated is incremented by new pages allocated size
    /// 2) it is "recyclable" run, then we increment bulk_allocated by number of free slots in that exact run
    pub unsafe fn alloc(&mut self, size: usize, bulk_allocated: &mut usize) -> *mut u8 {
        let p = if size < 2048 {
            self.alloc_raw_from_run(size, bulk_allocated)
        } else {
            self.alloc_large(size, bulk_allocated)
        };
        //  println!("alloc {:p} {}", p, bulk_allocated);
        p
    }

    unsafe fn free_from_run(&mut self, ptr: *mut u8, run: *mut Run) -> usize {
        let idx = (*run).size_bracket_index as usize;
        let bracket_size = BRACKET_SIZES[idx];
        core::ptr::write_bytes(ptr, 0, bracket_size);
        (*run).free_list.add(ptr.cast());

        if (*run).is_all_free() {
            self.non_full_runs[idx].remove(&run);
            if run == self.current_runs[idx] {
                self.current_runs[idx] = &mut DEDICATED_FULL_RUN;
            }

            self.free_pages(run.cast());
        } else {
            // It is not completely free. If it wasn't the current run or
            // already in the non-full run set (i.e., it was full) insert it
            // into the non-full run set.
            if run != self.current_runs[idx] {
                if !self.non_full_runs[idx].contains(&run) {
                    self.non_full_runs[idx].insert(run);
                }
            }
        }

        bracket_size
    }

    pub unsafe fn free(&mut self, ptr: *mut u8) -> usize {
        let mut pm_idx = self.round_down_to_page_map_index(ptr);
        let run;

        match self.page_map.add(pm_idx).cast::<PageMapKind>().read() {
            PageMapKind::LargeObject => {
                return self.free_pages(ptr);
            }
            PageMapKind::LargeObjectPart => {
                unreachable!("Unreachable: trying to free large object part at {:p}", ptr);
            }
            PageMapKind::RunPart => {
                // find the beginning of the run
                while {
                    pm_idx -= 1;
                    self.page_map.add(pm_idx).cast::<PageMapKind>().read() != PageMapKind::Run
                } {}
                run = self.base.add(pm_idx * PAGE_SIZE);
            }
            PageMapKind::Run => {
                run = self.base.add(pm_idx * PAGE_SIZE);
            }
            _ => unreachable!("Trying to free unallocated memory at {:p}", ptr),
        }

        self.free_from_run(ptr, run.cast())
    }
    #[inline]
    pub fn is_free_page(&self, idx: usize) -> bool {
        unsafe {
            let pm_type = self.page_map.add(idx).read();
            pm_type == PageMapKind::Released as u8 || pm_type == PageMapKind::Empty as u8
        }
    }

    pub unsafe fn free_pages(&mut self, ptr: *mut u8) -> usize {
        let pm_idx = self.to_page_map_index(ptr);
        let pm_type = self.page_map.add(pm_idx).read();
        let pm_part_type;
        match pm_type {
            x if x == PageMapKind::Run as u8 => pm_part_type = PageMapKind::RunPart as u8,
            x if x == PageMapKind::LargeObject as u8 => {
                pm_part_type = PageMapKind::LargeObjectPart as u8
            }
            _ => unreachable!(),
        }

        let mut num_pages = 1;
        self.page_map.add(pm_idx).write(PageMapKind::Empty as _);
        let mut idx = pm_idx + 1;
        let end = self.page_map_size;
        while idx < end && self.page_map.add(idx).read() == pm_part_type {
            self.page_map.add(idx).write(PageMapKind::Empty as _);
            num_pages += 1;
            idx += 1;
        }

        let byte_size = num_pages * PAGE_SIZE;

        let mut fpr = ptr.cast::<FreeRun>();

        if cfg!(debug_assertions) {
            (*fpr).magic_num = MAGIC_NUM_FREE;
        }

        (*fpr).set_byte_size(self, byte_size);

        if !self.free_page_runs.is_empty() {
            let mut i = 0;
            while i < self.free_page_runs.len() {
                let item = &self.free_page_runs[i];
                let it = *item;
                if it < fpr {
                    i += 1;
                    continue;
                }

                let h = it;
                if (*fpr).end(self) == (*h).begin() {
                    if cfg!(debug_assertions) {
                        (*h).magic_num = 0;
                    }
                    self.free_page_runs.remove(&it);
                    (*fpr).set_byte_size(self, (*fpr).byte_size(self) + (*h).byte_size(self));
                } else {
                    break;
                }
                i += 1;
            }
            if !self.free_page_runs.is_empty() {
                let mut i = self.free_page_runs.len() - 1;
                while i > 0 {
                    //println!("{} {}", i, self.free_page_runs.len());
                    let item = &self.free_page_runs[i];
                    let it = *item;
                    if it > fpr {
                        i -= 1;
                        continue;
                    }
                    let l = it;

                    if (*l).end(self) == (*fpr).begin() {
                        self.free_page_runs.remove(&it);

                        (*l).set_byte_size(self, (*l).byte_size(self) + (*fpr).byte_size(self));
                        if cfg!(debug_assertions) {
                            (*fpr).magic_num = 0;
                        }
                        fpr = l;
                    } else {
                        break;
                    }
                    i -= 1;
                }
            }
        }
        (*fpr).release_pages(self);
        self.free_page_runs.insert(fpr);
        byte_size
    }

    unsafe fn release_page_range(&mut self, mut start: *mut u8, end: *mut u8) -> usize {
        if cfg!(debug_assertions) {
            // In the debug build, the first page of a free page run
            // contains a magic number for debugging. Exclude it.
            start = start.add(PAGE_SIZE);

            if start == end {
                return 0;
            }
        }

        let mut pm_idx = self.to_page_map_index(start);
        let mut reclaimed_bytes = 0;
        let max_idx = pm_idx + (end as usize - start as usize) / PAGE_SIZE;
        while pm_idx < max_idx {
            if self.page_map.add(pm_idx).read() == PageMapKind::Empty as u8 {
                // Mark the page as released and update how many bytes we released.
                reclaimed_bytes += PAGE_SIZE;
                self.page_map.add(pm_idx).write(PageMapKind::Released as _);
            }
            pm_idx += 1;
        }
        self.mmap.decommit(start, reclaimed_bytes);
        reclaimed_bytes
    }

    pub unsafe fn bulk_free(&mut self, pointers: &[*mut u8]) -> usize {
        let mut freed_bytes = 0;
        let mut runs = IndexSet::new();

        for &ptr in pointers.iter() {
            let pm_idx = self.round_down_to_page_map_index(ptr);
            let run;

            let page_map_entry = self.page_map.add(pm_idx).cast::<PageMapKind>().read();

            if page_map_entry == PageMapKind::Run {
                run = self.base.add(pm_idx * PAGE_SIZE).cast::<Run>();
            } else if page_map_entry == PageMapKind::RunPart {
                let mut pi = pm_idx;
                // find the beginning of the run
                while {
                    pi -= 1;
                    self.page_map.add(pi).cast::<PageMapKind>().read() != PageMapKind::Run
                } {}
                run = self.base.add(pi * PAGE_SIZE).cast::<Run>();
            } else if page_map_entry == PageMapKind::LargeObject {
                //   println!("large??");
                freed_bytes += self.free_pages(ptr);

                continue;
            } else {
                #[cfg(debug_assertions)]
                unreachable!("Unreachable: page map type: {:?}", page_map_entry);
                #[cfg(not(debug_assertions))]
                {
                    core::hint::unreachable_unchecked();
                }
            }

            freed_bytes += (*run).add_to_bulk_free_list(ptr);
            runs.insert(run);
        }

        for run in runs {
            let idx = (*run).size_bracket_index as usize;

            let run_was_full = (*run).is_full();
            (*run).merge_bulk_free_list_to_free_list();

            if (*run).is_all_free() {
                let run_was_current = run == *self.current_runs.get_unchecked(idx);
                if !run_was_full {
                    self.non_full_runs[idx].remove(&run);
                }

                if !run_was_current {
                    (*run).zero_header_and_slot_headers();
                    self.free_pages(run.cast());
                }
            } else {
                if run == *self.current_runs.get_unchecked(idx) {
                    debug_assert!(!self.non_full_runs[idx].contains(&run));
                } else if run_was_full {
                    self.non_full_runs[idx].insert(run);
                } else {
                    debug_assert!(self.non_full_runs[idx].contains(&run));
                }
            }
        }

        freed_bytes
    }
    pub fn usable_size(&self, ptr: *mut u8) -> usize {
        unsafe {
            let mut pm_idx = self.round_down_to_page_map_index(ptr);

            match self.page_map.add(pm_idx).cast::<PageMapKind>().read() {
                PageMapKind::Released | PageMapKind::Empty | PageMapKind::LargeObjectPart => {
                    #[cfg(debug_assertions)]
                    unreachable!("Unreachable: pm_idx={}, ptr={:p}", pm_idx, ptr);
                    #[cfg(not(debug_assertions))]
                    {
                        std::hint::unreachable_unchecked();
                    }
                }
                PageMapKind::LargeObject => {
                    let mut num_pages = 1;
                    let mut idx = pm_idx + 1;
                    let end = self.page_map_size;
                    while idx < end
                        && self.page_map.add(idx).cast::<PageMapKind>().read()
                            == PageMapKind::LargeObjectPart
                    {
                        num_pages += 1;
                        idx += 1;
                    }
                    return num_pages * PAGE_SIZE;
                }
                PageMapKind::Run | PageMapKind::RunPart => {
                    while self.page_map.add(pm_idx).cast::<PageMapKind>().read() != PageMapKind::Run
                    {
                        pm_idx -= 1;
                    }

                    let run = self.base.add(pm_idx * PAGE_SIZE).cast::<Run>();

                    let idx = (*run).size_bracket_index;
                    *BRACKET_SIZES.get_unchecked(idx as usize)
                }
            }
        }
    }
    #[inline]
    pub const fn index_to_bracket_size(idx: usize) -> usize {
        BRACKET_SIZES[idx]
    }
}

static mut DEDICATED_FULL_RUN: Run = Run {
    free_list: SlotFreeList::new(),
    bulk_free_list: SlotFreeList::new(),
    magic_num: 0,
    next: null_mut(),
    size_bracket_index: 0,
};

// We use the tail (`USE_TAIL` == true) for the bulk or thread-local free lists to avoid the need to
// traverse the list from the head to the tail when merging free lists.
// We don't use the tail (`USE_TAIL` == false) for the free list to avoid the need to manage the
// tail in the allocation fast path for a performance reason.
#[repr(C)]
pub struct SlotFreeList<const USE_TAIL: bool> {
    /// A pointer (Slot*) to the head of the list. Always 8 bytes so that we will have the same
    /// layout between 32 bit and 64 bit, which is not strictly necessary, but we do so for 1)
    /// uniformity, 2) we won't need to change this code if we move to a non-low 4G heap in the
    /// future, and 3) the space savings by using 32 bit fields in 32 bit would be lost in noise
    /// (won't open up enough space to cause an extra slot to be available).
    head: u64,
    /// A pointer (Slot*) to the tail of the list. Always 8 bytes so that we will have the same
    /// layout between 32 bit and 64 bit. The tail is stored to speed up merging of lists.
    /// Unused if USE_TAIL is false.
    tail: u64,
    /// The number of slots in the list. This is used to make it fast to check if a free list is all
    /// free without traversing the whole free list.
    size: u32,
    #[allow(dead_code)]
    padding: u32,
}

impl<const USE_TAIL: bool> SlotFreeList<USE_TAIL> {
    pub const fn new() -> Self {
        Self {
            head: 0,
            tail: 0,
            size: 0,
            padding: 0,
        }
    }
    #[inline]
    pub fn head(&self) -> *mut Slot {
        self.head as *mut _
    }
    #[inline]
    pub fn tail(&self) -> *mut Slot {
        assert!(USE_TAIL);
        self.tail as *mut _
    }
    #[inline]
    pub const fn size(&self) -> usize {
        self.size as _
    }
    #[inline]
    pub fn remove(&mut self) -> *mut Slot {
        let slot;
        if cfg!(debug_assertions) {
            self.verify();
        }
        unsafe {
            let headp = &self.head as *const u64 as *mut *mut Slot;
            let tailp = if USE_TAIL {
                &self.tail as *const u64 as *mut *mut Slot
            } else {
                null_mut()
            };
            let old_head = *headp;
            if old_head.is_null() {
                if USE_TAIL {
                    debug_assert!(tailp.read().is_null());
                }
                return null_mut();
            } else {
                if USE_TAIL {
                    debug_assert!(!tailp.read().is_null());
                }
                let old_head_next = (*old_head).next();
                slot = old_head;
                headp.write(old_head_next);
                if USE_TAIL && old_head_next.is_null() {
                    tailp.write(null_mut());
                }
            }
            (*slot).clear();
            self.size -= 1;
            if cfg!(debug_assertions) {
                self.verify();
            }
            slot
        }
    }
    #[inline]
    pub fn add(&mut self, slot: *mut Slot) {
        if cfg!(debug_assertions) {
            self.verify();
        }
        debug_assert!(!slot.is_null());
        unsafe {
            debug_assert!((*slot).next().is_null());
            let headp = &self.head as *const u64 as *mut *mut Slot;
            let tailp = if USE_TAIL {
                &self.tail as *const u64 as *mut *mut Slot
            } else {
                null_mut()
            };
            let old_head = *headp;

            if old_head.is_null() {
                if USE_TAIL {
                    debug_assert!(tailp.read().is_null());
                }
                headp.write(slot);
                if USE_TAIL {
                    tailp.write(slot);
                }
            } else {
                if USE_TAIL {
                    debug_assert!(!tailp.read().is_null());
                }
                headp.write(slot);
                (*slot).set_next(old_head);
            }
            self.size += 1;
            if cfg!(debug_assertions) {
                self.verify();
            }
        }
    }
    /// Merge the given list into this list. Empty the given list.
    /// Deliberately support only a kUseTail == true SlotFreeList parameter because 1) we don't
    /// currently have a situation where we need a kUseTail == false SlotFreeList parameter, and 2)
    /// supporting the kUseTail == false parameter would require a O(n) linked list traversal to do
    /// the merge if 'this' SlotFreeList has kUseTail == false, which we'd like to avoid.
    pub fn merge(&mut self, list: &mut SlotFreeList<true>) {
        if cfg!(debug_assertions) {
            self.verify();
            list.verify();
        }

        if list.size() == 0 {
            return;
        }
        let headp = &self.head as *const u64 as *mut *mut Slot;
        let tailp = if USE_TAIL {
            &self.tail as *const u64 as *mut *mut Slot
        } else {
            null_mut()
        };
        unsafe {
            let old_head = headp.read();
            if old_head.is_null() {
                headp.write(list.head());
                if USE_TAIL {
                    tailp.write(list.tail());
                }
                self.size = list.size() as _;
            } else {
                headp.write(list.head());
                (*list.tail()).set_next(old_head);
                self.size += list.size() as u32;
            }
            list.reset();
            if cfg!(debug_assertions) {
                self.verify();
            }
        }
    }

    pub fn reset(&mut self) {
        self.head = 0;
        if USE_TAIL {
            self.tail = 0;
        }
        self.size = 0;
    }
    fn verify(&self) {
        unsafe {
            let head = self.head();
            let tail = if USE_TAIL { self.tail() } else { null_mut() };

            if self.size == 0 {
                assert!(head.is_null());
                if USE_TAIL {
                    assert!(tail.is_null());
                }
            } else {
                assert!(!head.is_null());
                if USE_TAIL {
                    assert!(!tail.is_null());
                }

                let mut count = 0;
                let mut slot = head;
                while !slot.is_null() {
                    count += 1;
                    if USE_TAIL && (*slot).next().is_null() {
                        assert_eq!(slot, tail);
                    }
                    slot = (*slot).next();
                }
                assert_eq!(count, self.size);
            }
        }
    }
}

pub struct Slot {
    pub next: *mut Self,
}

impl Slot {
    #[inline]
    pub fn next(&self) -> *mut Self {
        self.next
    }
    #[inline]
    pub fn set_next(&mut self, next: *mut Self) {
        self.next = next;
    }
    #[inline]
    pub fn left(&self, bracket_size: usize) -> *mut Self {
        let this = self as *const Self as usize;
        (this - bracket_size) as _
    }
    #[inline]
    pub fn clear(&mut self) {
        self.next = null_mut();
    }
}
