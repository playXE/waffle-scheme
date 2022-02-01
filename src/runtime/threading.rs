use std::ptr::{null_mut, NonNull};

use comet::api::{Collectable, Finalize, Trace};
use parking_lot::lock_api::RawMutex;

use crate::{
    init::wrong_type_argument,
    runtime::{cons, make_box, value::ScmBox, vm, SchemeThreadRef},
};

use super::{
    defun, make_exception, make_string,
    value::{Null, Value},
    SchemeThread,
};

pub struct Thread {
    pub(crate) value: Value,
    pub(crate) handle: Option<comet::mutator::JoinData>,
}
unsafe impl Trace for Thread {
    fn trace(&mut self, _vis: &mut dyn comet::api::Visitor) {
        self.value.trace(_vis);
    }
}

unsafe impl Finalize for Thread {}
impl Collectable for Thread {}

pub fn subr_thread_spawn(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    let rt = thread.runtime;
    let proc = args[0];
    if !proc.applicablep() {
        return Err(wrong_type_argument(
            thread,
            "thread/spawn",
            "function",
            proc,
            1,
        ));
    }

    let result_box = Value::new(make_box(thread, Value::new(Null)));

    let handle = thread.mutator.spawn_mutator(move |mutator| {
        let thread = Box::leak(Box::new(SchemeThread {
            current_frame: null_mut(),
            rc: 1,
            runtime: rt,
            mutator: mutator.clone(),
            trampoline_arguments: vec![],
            trampoline_fn: Value::new(Null),
        }));
        let mut thread = SchemeThreadRef {
            ptr: unsafe { NonNull::new_unchecked(thread) },
        };
        rt.inner().global_lock.lock();
        rt.inner().threads.push(thread.clone());
        unsafe {
            rt.inner().global_lock.unlock();
        }
        let result = vm::apply(&mut thread, proc, &[]);

        match result {
            Ok(val) => {
                result_box.downcast::<ScmBox>().value =
                    Value::new(cons(&mut thread, Value::new(0i32), val));
            }
            Err(e) => {
                result_box.downcast::<ScmBox>().value =
                    Value::new(cons(&mut thread, Value::new(1i32), e));
            }
        }
        rt.inner().global_lock.lock();
        rt.inner().threads.retain(|thr| thr.ptr != thread.ptr);
        unsafe {
            rt.inner().global_lock.unlock();
        }
    });

    Ok(Value::new(thread.mutator.allocate(
        Thread {
            value: result_box,
            handle: Some(handle),
        },
        comet::gc_base::AllocationSpace::New,
    )))
}

pub fn subr_thread_join(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    let handle = args[0];
    if !handle.is_cell::<Thread>() {
        return Err(wrong_type_argument(
            thread,
            "thread/join",
            "thread",
            handle,
            1,
        ));
    }
    let mut handle = handle.downcast::<Thread>();
    if let Some(native_handle) = handle.handle.take() {
        native_handle.join(&thread.mutator);

        let result = handle.value.downcast::<ScmBox>().value.cons();

        if result.car.get_int32() == 0 {
            return Ok(result.cdr);
        } else {
            let tag = thread.runtime.global_symbol(super::Global::ScmEval);
            let message = make_string(thread, &format!("thread had exception: {}", result.cdr));
            return Err(Value::new(make_exception(
                thread,
                tag,
                message,
                Value::new(Null),
            )));
        }
    } else {
        let tag = thread.runtime.global_symbol(super::Global::ScmEval);
        let message = make_string(thread, "thread was already joined");
        return Err(Value::new(make_exception(
            thread,
            tag,
            message,
            Value::new(Null),
        )));
    }
}

pub(crate) fn init(thread: &mut SchemeThread) {
    defun(thread, "thread/spawn", subr_thread_spawn, 1, false, false);
    defun(thread, "thread/join", subr_thread_join, 1, false, false);
    defun(
        thread,
        "thread-id",
        |thread, _| {
            let id = std::thread::current().id();

            Ok(Value::new(make_string(thread, format!("{:?}", id))))
        },
        0,
        false,
        false,
    );
    defun(
        thread,
        "thread?",
        |_, args| Ok(Value::new(args[0].is_cell::<Thread>())),
        1,
        false,
        false,
    );
}
