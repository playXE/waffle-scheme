use std::{mem::size_of, sync::atomic::AtomicU64};

use crate::{
    compiler::UpvalLoc,
    method_jit::lir::calling_convention,
    runtime::{
        value::{Closure, ScmPrototype, Value},
        vm::{apply, CallFrame},
        SchemeThread,
    },
    Managed,
};
