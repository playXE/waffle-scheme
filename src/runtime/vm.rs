use std::{mem::size_of, ptr::null_mut};

use alloca::with_alloca;
use comet::api::Trace;
use comet_extra::alloc::vector::Vector;

use crate::{
    compiler::{Op, UpvalLoc},
    runtime::{
        make_list,
        value::{Null, ScmSymbol, Upval, Upvalue},
    },
    Managed,
};

use super::{
    make_exception, make_string,
    value::{Closure, NativeFunction, ScmPrototype, Value},
    Global, SchemeThread,
};

#[repr(C)]
pub struct Frame {
    pub prev: *mut Frame,
    pub p: Managed<ScmPrototype>,
    pub c: Option<Managed<Closure>>,

    pub stack: *mut Value,
    pub locals: *mut Value,
    pub upvalues: *mut Value,
    pub si: usize,
}
unsafe impl Trace for Frame {
    fn trace(&mut self, vis: &mut dyn comet::api::Visitor) {
        self.p.trace(vis);
        self.c.trace(vis);
        for j in 0..self.si {
            unsafe {
                (&mut *self.stack.add(j)).trace(vis);
            }
        }
        for j in 0..self.p.locals {
            unsafe {
                (&mut *self.locals.add(j as _)).trace(vis);
            }
        }
        for j in 0..self.p.local_free_variable_count {
            unsafe {
                (&mut *self.upvalues.add(j as _)).trace(vis);
            }
        }
    }
}
impl Frame {
    pub fn new(
        p: Managed<ScmPrototype>,
        c: Option<Managed<Closure>>,
        stack: *mut Value,
        locals: *mut Value,
    ) -> Self {
        Self {
            prev: null_mut(),
            p,
            c,
            stack,

            locals,
            upvalues: null_mut(),
            si: 0,
        }
    }
}

pub fn arity_error_least(thread: &mut SchemeThread, expected: usize, got: usize) -> Value {
    let tag = thread.runtime.global_symbol(Global::ScmEval);
    let msg = make_string(
        thread,
        format!(
            "function expected at least {} arguments but got {}",
            expected, got
        ),
    );
    Value::new(make_exception(thread, tag, msg, Value::new(Null)))
}
pub fn arity_error_most(thread: &mut SchemeThread, expected: usize, got: usize) -> Value {
    let tag = thread.runtime.global_symbol(Global::ScmEval);
    let msg = make_string(
        thread,
        format!(
            "function expected at most {} arguments but got {}",
            expected, got
        ),
    );
    Value::new(make_exception(thread, tag, msg, Value::new(Null)))
}

pub fn arity_error(thread: &mut SchemeThread) -> Value {
    let tag = thread.runtime.global_symbol(Global::ScmEval);
    let msg = make_string(thread, format!("function got bad number of arguments",));
    Value::new(make_exception(thread, tag, msg, Value::new(Null)))
}

pub fn immutable_assign(thread: &mut SchemeThread, to: Managed<ScmSymbol>) -> Value {
    let tag = thread.runtime.global_symbol(Global::ScmEval);
    let msg = make_string(
        thread,
        format!("Cannot assign to immutable variable '{}'", to.name),
    );
    Value::new(make_exception(thread, tag, msg, Value::new(Null)))
}

pub fn vm_apply(
    thread: &mut SchemeThread,
    prototype: Managed<ScmPrototype>,
    closure: Option<Managed<Closure>>,
    _argc: usize,
    args: &[Value],
    trampoline: &mut bool,
) -> Result<Value, Value> {
    with_alloca(
        size_of::<Value>() * prototype.stack_max as usize
            + size_of::<Value>() * prototype.locals as usize
            + size_of::<Value>() * prototype.local_free_variable_count as usize,
        |stack| unsafe {
            let stack_ptr = stack.as_mut_ptr().cast::<Value>();

            core::ptr::copy_nonoverlapping(
                &Value::encode_null_value(),
                stack_ptr,
                stack.len() / size_of::<Value>(),
            );

            let locals_ptr = stack_ptr.add(prototype.stack_max as _);
            let upvalues_ptr = locals_ptr.add(prototype.locals as _);

            let mut f = Frame::new(prototype, closure, stack_ptr, locals_ptr);
            f.prev = thread.current_frame;
            thread.current_frame = &mut f;
            if prototype.local_free_variable_count > 0 {
                let data = prototype.local_free_variables.as_ptr().cast::<usize>();
                f.upvalues = upvalues_ptr;
                for i in 0..prototype.local_free_variable_count {
                    let index = data.add(i as _).read();
                    f.upvalues
                        .add(i as _)
                        .write(Value::new(thread.mutator.allocate(
                            Upvalue {
                                closed: false,
                                upval: Upval {
                                    local: locals_ptr.add(index as _),
                                },
                            },
                            comet::gc_base::AllocationSpace::New,
                        )));
                }
            }
            macro_rules! vm_ret {
                ($val: expr) => {
                    for i in 0..prototype.local_free_variable_count {
                        (*f.upvalues.add(i as usize)).upvalue_close();
                    }
                    let prev = thread.current_frame;
                    thread.current_frame = (*prev).prev;
                    return $val;
                };
            }
            if args.len() < prototype.arguments as usize
                && (!prototype.variable_arity && args.len() != prototype.arguments as usize - 1)
            {
                vm_ret!(Err(arity_error_least(
                    thread,
                    prototype.arguments as _,
                    args.len()
                )));
            } else if args.len() > prototype.arguments as usize && !prototype.variable_arity {
                vm_ret!(Err(arity_error_most(
                    thread,
                    prototype.arguments as _,
                    args.len()
                )));
            }

            for i in 0..prototype.arguments {
                if prototype.variable_arity && i == prototype.arguments - 1 {
                    f.locals
                        .add(i as _)
                        .write(make_list(thread, &args[i as usize..]));
                    break;
                } else {
                    f.locals.add(i as _).write(args[i as usize]);
                }
            }

            let code = prototype.code;

            let mut ip = 0;
            loop {
                let op = code.as_ptr().cast::<Op>().add(ip).read();
                ip += 1;
                match op {
                    Op::PushConstant(c) => {
                        let val = prototype.constants[c as usize];
                        f.stack.add(f.si).write(val);
                        f.si += 1;
                    }
                    Op::PushFalse => {
                        f.stack.add(f.si).write(Value::new(false));
                        f.si += 1;
                    }
                    Op::PushTrue => {
                        f.stack.add(f.si).write(Value::new(true));
                        f.si += 1;
                    }
                    Op::PushInt(x) => {
                        f.stack.add(f.si).write(Value::new(x));
                        f.si += 1;
                    }
                    Op::PushNull => {
                        f.stack.add(f.si).write(Value::new(Null));
                        f.si += 1;
                    }
                    Op::Pop => {
                        f.si -= 1;
                    }
                    Op::GlobalSet => {
                        let mut k = f.stack.add(f.si - 1).read().downcast::<ScmSymbol>();
                        f.si -= 1;
                        let v = f.stack.add(f.si - 1).read();
                        f.si -= 1;
                        if !k.mutable {
                            vm_ret!(Err(immutable_assign(thread, k)));
                        }
                        k.value = v;
                    }
                    Op::GlobalGet => {
                        let k = f.stack.add(f.si - 1).read().downcast::<ScmSymbol>();
                        f.si -= 1;
                        f.stack.add(f.si).write(k.value);
                        f.si += 1;
                    }
                    Op::LocalSet(x) => {
                        let v = f.stack.add(f.si - 1).read();
                        f.si -= 1;

                        f.locals.add(x as _).write(v);
                    }
                    Op::LocalGet(x) => {
                        f.stack.add(f.si).write(f.locals.add(x as _).read());
                        f.si += 1;
                    }
                    Op::UpvalueGet(x) => {
                        f.stack
                            .add(f.si)
                            .write(closure.unwrap_unchecked().upvalues[x as usize].upvalue());
                        f.si += 1;
                    }
                    Op::UpvalueSet(x) => {
                        let v = f.stack.add(f.si - 1).read();
                        f.si -= 1;
                        closure.unwrap_unchecked().upvalues[x as usize].upvalue_set(v);
                    }
                    Op::CloseOver => {
                        let p = f.stack.add(f.si - 1).read().downcast::<ScmPrototype>();
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

                        for i in 0..locations.blob_length() / size_of::<UpvalLoc>() {
                            let l = locations.blob_ref::<UpvalLoc>(i);
                            if l.local {
                                c.upvalues
                                    .push(&mut thread.mutator, f.upvalues.add(l.index as _).read());
                            } else {
                                c.upvalues.push(
                                    &mut thread.mutator,
                                    closure.unwrap_unchecked().upvalues[l.index as usize],
                                );
                            }
                        }

                        f.stack.add(f.si - 1).write(Value::new(c));
                    }
                    Op::Return => {
                        let val = if f.si != 0 {
                            f.si -= 1;
                            f.stack.add(f.si).read()
                        } else {
                            Value::encode_undefined_value()
                        };

                        for i in 0..prototype.local_free_variable_count {
                            (*f.upvalues.add(i as usize)).upvalue_close();
                        }
                        let prev = thread.current_frame;
                        thread.current_frame = (*prev).prev;
                        return Ok(val);
                    }
                    Op::TailApply(argc) => {
                        let fun = f.stack.add(f.si - 1).read();
                        f.si -= 1;

                        thread.trampoline_arguments.clear();
                        for i in 0..argc {
                            thread
                                .trampoline_arguments
                                .push(f.stack.add(f.si - argc as usize + i as usize).read());
                        }
                        thread.trampoline_fn = fun;
                        *trampoline = true;

                        for i in 0..prototype.local_free_variable_count {
                            (*f.upvalues.add(i as usize)).upvalue_close();
                        }
                        let prev = thread.current_frame;
                        thread.current_frame = (*prev).prev;
                        return Ok(Value::encode_undefined_value());
                    }
                    Op::Apply(argc) => {
                        let fun = f.stack.add(f.si - 1).read();
                        f.si -= 1;

                        let tmp = apply(
                            thread,
                            fun,
                            std::slice::from_raw_parts(
                                f.stack.add(f.si - argc as usize),
                                argc as _,
                            ),
                        );
                        if let Err(e) = tmp {
                            for i in 0..prototype.local_free_variable_count {
                                (*f.upvalues.add(i as usize)).upvalue_close();
                            }
                            let prev = thread.current_frame;
                            thread.current_frame = (*prev).prev;
                            return Err(e);
                        } else if let Ok(val) = tmp {
                            f.si -= argc as usize;
                            f.stack.add(f.si).write(val);
                            f.si += 1;
                        }
                    }
                    Op::JumpIfFalse(x) => {
                        let cond = f.stack.add(f.si - 1).read();
                        f.si -= 1;
                        if !cond.to_boolean() {
                            ip = x as usize;
                        }
                    }
                    Op::Jump(x) => {
                        ip = x as usize;
                    }
                }
            }
        },
    )
}

pub fn apply(
    thread: &mut SchemeThread,
    mut function: Value,
    args: &[Value],
) -> Result<Value, Value> {
    let mut args = args.to_vec();
    loop {
        if !function.applicablep() {
            let tag = thread.runtime.global_symbol(Global::ScmEval);
            let message = make_string(
                thread,
                format!("attempt to apply non-function {}", function),
            );
            return Err(Value::new(make_exception(
                thread,
                tag,
                message,
                Value::new(Null),
            )));
        }
        let mut trampoline = false;
        if function.native_functionp() {
            let native = function.downcast::<NativeFunction>();
            if args.len() < native.arguments {
                return Err(arity_error_least(thread, native.arguments, args.len()));
            } else if args.len() > native.arguments && !native.variable_arity {
                return Err(arity_error_most(thread, native.arguments, args.len()));
            }
            return (native.callback)(thread, &args);
        }

        let (prototype, closure) = if function.prototypep() {
            (function.downcast::<ScmPrototype>(), None)
        } else {
            (
                function.downcast::<Closure>().prototype,
                Some(function.downcast::<Closure>()),
            )
        };

        let result = vm_apply(
            thread,
            prototype,
            closure,
            args.len(),
            &args,
            &mut trampoline,
        );
        args.clear();
        if trampoline && result.is_ok() {
            function = thread.trampoline_fn;

            args = std::mem::replace(&mut thread.trampoline_arguments, vec![]);
        } else {
            return result;
        }
    }
}
