#![feature(
    const_type_id,
    ptr_metadata,
    core_intrinsics,
    const_fn_fn_ptr_basics,
    const_ptr_offset_from,
    wrapping_int_impl,
    try_trait_v2
)]

pub mod fnv;
#[macro_use]
pub mod gc;

pub mod disasm;
pub mod gc_bdwgc;
pub mod hash;
pub mod sexp;
pub mod vec;
pub mod vm;

#[cfg(feature = "bdwgc")]
pub use gc_bdwgc::Heap;

#[cfg(not(feature = "bdwgc"))]
pub use gc::Heap;
