use std::{
    marker::PhantomData,
    mem::size_of,
    ptr::{null_mut, NonNull},
};

use crate::{
    gc::{allocator::PageReleaseMode, formatted_size, CellHeader, Gc},
    sexp::ValueType,
};

use self::ffi::ProfileStats;

pub const DEFAULT_INITIAL_HEAP_SIZE: usize = 256 * 1024 * size_of::<usize>();

pub struct Heap {}
impl Heap {
    #[allow(unused_variables)]
    pub fn new(
        heap_size: usize,
        min_heap_size: usize,
        max_heap_size: usize,
        threshold: usize,
        growth_multiplier: f64,
        page_release_mode: PageReleaseMode,
        page_release_threshold: usize,
        verbose: u8,
    ) -> Self {
        unsafe {
            ffi::GC_set_all_interior_pointers(1);
            std::env::set_var("GC_MARKERS", "1");
            ffi::GC_init();
            let sz = ffi::GC_get_heap_size();

            if sz < DEFAULT_INITIAL_HEAP_SIZE {
                ffi::GC_expand_hp(DEFAULT_INITIAL_HEAP_SIZE - sz);
            }
        }
        Self {}
    }

    pub fn collect(&mut self) {
        unsafe {
            ffi::GC_gcollect();
        }
    }

    pub fn print_stats(&self) {
        unsafe {
            let mut stats = ProfileStats::default();
            ffi::GC_get_prof_stats(&mut stats, size_of::<ProfileStats>());

            println!("heap stats:");
            println!(" heapsize_full={}", formatted_size(stats.heapsize_full));
            println!(
                " bytes_allocd_since_gc={}",
                formatted_size(stats.bytes_allocd_since_gc)
            );
            println!(
                " allocd_bytes_before_gc={}",
                formatted_size(stats.allocd_bytes_before_gc)
            );
            println!(" non_gc_bytes={}", formatted_size(stats.non_gc_bytes));
        }
    }

    pub fn allocate<T>(&mut self, value: T) -> Gc<T> {
        unsafe {
            let header =
                ffi::GC_malloc(size_of::<T>() + size_of::<CellHeader>()).cast::<CellHeader>();
            (*header).data = 0;

            (*header).tag = ValueType::Object as u32;
            #[cfg(feature = "track-source")]
            {
                (*header).source = std::panic::Location::caller();
            }
            (*header).data::<T>().write(value);

            Gc {
                header: NonNull::new_unchecked(header),
                marker: PhantomData,
            }
        }
    }
    pub fn allocate_tagged<T: 'static>(
        &mut self,
        value: T,
        tag: u32,
        immutable: bool,
        syntatic: bool,
    ) -> Gc<T> {
        let gc = self.allocate(value);
        unsafe {
            (*gc.header.as_ptr()).tag = tag as u32;

            (*gc.header.as_ptr()).set_syntatic(syntatic);
            (*gc.header.as_ptr()).set_immutable(immutable);

            #[cfg(feature = "track-source")]
            {
                (*gc.header.as_ptr()).source = std::panic::Location::caller();
            }
        }
        gc
    }

    pub unsafe fn allocate_var<T: 'static>(
        &mut self,
        value: T,
        tag: u32,
        immutable: bool,
        syntatic: bool,
        size: usize,
    ) -> Gc<T> {
        let header = ffi::GC_malloc(size + size_of::<CellHeader>()).cast::<CellHeader>();
        (*header).data = 0;
        (*header).set_immutable(immutable);
        (*header).set_syntatic(syntatic);

        (*header).tag = tag as u32;

        #[cfg(feature = "track-source")]
        {
            (*header).source = std::panic::Location::caller();
        }
        (*header).data::<T>().write(value);

        Gc {
            header: NonNull::new_unchecked(header),
            marker: PhantomData,
        }
    }

    pub unsafe fn malloc(&mut self, size: usize) -> *mut u8 {
        {
            let p = ffi::GC_malloc(size);

            p
        }
    }

    pub unsafe fn free(&mut self, ptr: *mut u8) {
        ffi::GC_free(ptr);
    }

    pub unsafe fn add_drop<T>(&mut self, p: Gc<T>) {
        if std::mem::needs_drop::<T>() {
            unsafe extern "C" fn drop_gc<T>(p: *mut u8, _data: *mut u8) {
                core::ptr::drop_in_place(p as *mut T);
            }
            ffi::GC_register_finalizer_no_order(
                p.header.as_ptr().cast(),
                Some(drop_gc::<T>),
                null_mut(),
                null_mut(),
                null_mut(),
            );
        }
    }
}

#[allow(dead_code)]
mod ffi {
    #[repr(C)]
    #[derive(Default, Debug)]
    pub struct ProfileStats {
        /// Heap size in bytes (including area unmapped to OS).
        pub(crate) heapsize_full: usize,
        /// Total bytes contained in free and unmapped blocks.
        pub(crate) free_bytes_full: usize,
        /// Amount of memory unmapped to OS.
        pub(crate) unmapped_bytes: usize,
        /// Number of bytes allocated since the recent collection.
        pub(crate) bytes_allocd_since_gc: usize,
        /// Number of bytes allocated before the recent collection.
        /// The value may wrap.
        pub(crate) allocd_bytes_before_gc: usize,
        /// Number of bytes not considered candidates for garbage collection.
        pub(crate) non_gc_bytes: usize,
        /// Garbage collection cycle number.
        /// The value may wrap.
        pub(crate) gc_no: usize,
        /// Number of marker threads (excluding the initiating one).
        pub(crate) markers_m1: usize,
        /// Approximate number of reclaimed bytes after recent collection.
        pub(crate) bytes_reclaimed_since_gc: usize,
        /// Approximate number of bytes reclaimed before the recent collection.
        /// The value may wrap.
        pub(crate) reclaimed_bytes_before_gc: usize,
        /// Number of bytes freed explicitly since the recent GC.
        pub(crate) expl_freed_bytes_since_gc: usize,
    }

    #[link(name = "gc")]
    extern "C" {

        pub(crate) fn GC_get_heap_size() -> usize;
        pub(crate) fn GC_expand_hp(x: usize);

        pub(crate) fn GC_set_all_interior_pointers(x: i32);
        pub(crate) fn GC_malloc(nbytes: usize) -> *mut u8;

        pub(crate) fn GC_malloc_uncollectable(nbytes: usize) -> *mut u8;

        pub(crate) fn GC_realloc(old: *mut u8, new_size: usize) -> *mut u8;

        pub(crate) fn GC_free(dead: *mut u8);

        pub(crate) fn GC_register_finalizer(
            ptr: *mut u8,
            finalizer: Option<unsafe extern "C" fn(*mut u8, *mut u8)>,
            client_data: *mut u8,
            old_finalizer: *mut extern "C" fn(*mut u8, *mut u8),
            old_client_data: *mut *mut u8,
        );

        pub(crate) fn GC_register_finalizer_no_order(
            ptr: *mut u8,
            finalizer: Option<unsafe extern "C" fn(*mut u8, *mut u8)>,
            client_data: *mut u8,
            old_finalizer: *mut extern "C" fn(*mut u8, *mut u8),
            old_client_data: *mut *mut u8,
        );

        pub(crate) fn GC_gcollect();

        pub(crate) fn GC_get_full_gc_total_time() -> usize;

        pub(crate) fn GC_get_prof_stats(prof_stats: *mut ProfileStats, stats_size: usize) -> usize;

        pub(crate) fn GC_malloc_atomic(nbytes: usize) -> *mut u8;

        pub(crate) fn GC_malloc_atomic_uncollectable(nbytes: usize) -> *mut u8;

        pub(crate) fn GC_thread_is_registered() -> u32;

        pub(crate) fn GC_register_my_thread(stack_base: *mut u8) -> i32;

        pub(crate) fn GC_unregister_my_thread() -> i32;

        pub(crate) fn GC_allow_register_threads();

        pub(crate) fn GC_init();
    }
}
