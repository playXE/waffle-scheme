pub mod bc2lbc;
pub mod c0;
pub mod c1;
pub mod lbc;

use std::mem::size_of;

use comet_extra::alloc::vector::Vector;

use crate::{
    compiler::UpvalLoc,
    runtime::{
        value::{Closure, ScmPrototype, Value},
        vm::{apply, CallFrame},
        SchemeThread,
    },
};

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub enum Trampoline {
    Return = 0,
    Call = 1,
    Exception = 2,
    Jit,
}

pub type JITSig =
    extern "C" fn(&mut SchemeThread, trampoline: &mut Trampoline, entry_ip: usize) -> Value;

pub extern "C" fn jit_trampoline(
    thread: &mut SchemeThread,
    frame: &mut CallFrame,
    func: Value,
    nargs: u32,
) {
    thread.trampoline_fn = func;
    thread.trampoline_arguments.clear();
    thread
        .trampoline_arguments
        .extend_from_slice(unsafe { frame.slice(nargs as _) });
    for _ in 0..nargs {
        unsafe {
            frame.pop();
        }
    }
}

pub extern "C" fn jit_apply(
    thread: &mut SchemeThread,
    frame: &mut CallFrame,
    func: Value,
    nargs: u32,
    res: &mut Trampoline,
) -> Value {
    let val = match apply(thread, func, unsafe { frame.slice(nargs as usize) }) {
        Ok(val) => val,
        Err(e) => {
            *res = Trampoline::Exception;
            e
        }
    };

    for _ in 0..nargs {
        unsafe {
            frame.pop();
        }
    }
    val
}

pub unsafe extern "C" fn close_over(
    thread: &mut SchemeThread,
    frame: &mut CallFrame,
    proto: Value,
) -> Value {
    let p = proto.downcast::<ScmPrototype>();
    let locations = Value::new(p.upvalues);
    let upvalues = Vector::with_capacity(
        &mut thread.mutator,
        locations.blob_length() / size_of::<UpvalLoc>(),
    );

    let mut c = thread.mutator.allocate(
        Closure {
            prototype: p,
            upvalues,
        },
        comet::gc_base::AllocationSpace::New,
    );
    let n = locations.blob_length() / size_of::<UpvalLoc>();
    for i in 0..n {
        let l = locations.blob_ref::<UpvalLoc>(i);
        if l.local {
            assert!(frame.upvalues > frame.bp.add(frame.si));
            c.upvalues
                .push(&mut thread.mutator, frame.upvalues.add(l.index as _).read());
        } else {
            c.upvalues.push(
                &mut thread.mutator,
                frame.closure.unwrap_unchecked().upvalues[l.index as usize],
            )
        }
    }
    Value::new(c)
}

pub extern "C" fn cons(thread: &mut SchemeThread, car: Value, cdr: Value) -> Value {
    Value::new(crate::runtime::cons(thread, car, cdr))
}

pub unsafe extern "C" fn list(thread: &mut SchemeThread, argv: *mut Value, argc: u32) -> Value {
    crate::runtime::make_list(thread, std::slice::from_raw_parts(argv, argc as _))
}
pub unsafe extern "C" fn vector(thread: &mut SchemeThread, argv: *mut Value, argc: u32) -> Value {
    let mut vec = crate::runtime::make_vector(thread, argc as _);

    for i in 0..argc {
        vec.vec.push(&mut thread.mutator, argv.add(i as _).read());
    }

    Value::new(vec)
}
