#![feature(arbitrary_self_types, vec_retain_mut)]
use comet::api::Gc;

#[cfg(feature = "immix")]
pub type Heap = comet::immix::Immix;
#[cfg(feature = "minimark")]
pub type Heap = comet::minimark::MiniMark;
#[cfg(feature = "marksweep")]
pub type Heap = comet::marksweep::MarkSweep;
#[cfg(feature = "semispace")]
pub type Heap = comet::semispace::SemiSpace;

pub type Managed<T> = Gc<T, Heap>;
pub type Weak<T> = comet::api::Weak<T, Heap>;

#[macro_export]
macro_rules! debug_unreachable {
    () => {
        debug_unreachable!("unreachable statement reached")
    };
    ($message: expr) => {{
        #[cfg(debug_assertions)]
        {
            unreachable!($message);
        }
        #[cfg(not(debug_assertions))]
        unsafe {
            core::hint::unreachable_unchecked()
        }
    }};
}

pub mod compiler;
pub mod init;
pub mod jit;
pub mod runtime;
