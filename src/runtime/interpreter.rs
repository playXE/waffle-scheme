use std::{mem::size_of, ptr::null_mut};

use crate::{compiler::Op, Managed};

use super::{
    value::{Closure, ScmPrototype, Upval, Upvalue, Value},
    vm::Frame,
    SchemeThread, SchemeThreadRef,
};

#[allow(dead_code)]
pub struct Stack {
    mem: *mut u8,
    start: *mut Value,
    pub(crate) cursor: *mut Value,
    end: *mut Value,
    pub(crate) current: *mut Frame,
}

pub const STACK_SIZE: usize = 8 * 1024;

impl Stack {
    pub fn new() -> Self {
        let mem = unsafe { libc::calloc(1, STACK_SIZE * 8).cast::<u8>() };
        Self {
            start: mem.cast(),
            mem: mem.cast(),
            cursor: mem.cast(),
            end: unsafe { mem.add(STACK_SIZE * 8).cast() },
            current: null_mut(),
        }
    }

    pub fn new_frame(
        &mut self,
        p: Managed<ScmPrototype>,
        c: Option<Managed<Closure>>,
    ) -> Option<*mut Frame> {
        let stack_size = p.stack_max + p.locals + p.local_free_variable_count;
        let stack_size = stack_size as usize;
        unsafe {
            if self.cursor.add(stack_size) >= self.end {
                return None;
            }
            let locals = self.cursor;
            let locals = stack.add(p.stack_max as _);
            let upvalues = locals.add(p.locals as _);
            let mut frame = Frame::new(p, c, self.cursor, locals);
            frame.upvalues = upvalues;
            frame.prev = self.current;
            let frame = Box::leak(Box::new(frame));
            self.current = frame;
            Some(frame)
        }
    }
}

impl SchemeThread {
    unsafe fn allocate_stack(&mut self, count: usize) -> *mut Value {
        let result = self.sp;
        let new_sp = result.add(count);
        if new_sp >= self.end {
            return null_mut();
        }
        self.sp = new_sp;
        result
    }

    pub unsafe fn vm_loop(
        &mut self,
        mut function: Managed<ScmPrototype>,
        mut closure: Option<Managed<Closure>>,
        mut argc: usize,
    ) -> Result<Value, Value> {
        let mut exit = true;
        loop {
            let stack_size = (function.stack_max as usize
                + function.locals as usize
                + function.local_free_variable_count as usize)
                * size_of::<Value>();
            let stack = self.allocate_stack(stack_size + size_of::<Frame>());
            if stack.is_null() {
                panic!("stack overflow");
            }

            let frame = stack.cast::<Frame>();
            (*frame).sp = stack;
            (*frame).stack = stack.add(size_of::<Frame>());
            (*frame).locals = stack.add(function.stack_max as usize);
            (*frame).upvalues = stack.add(function.stack_max as usize + function.locals as usize);
            (*frame).prev = self.current_frame;
            self.current_frame = frame;
            (*frame).exit_on_return = Value::new(exit);
            exit = false;
            if function.local_free_variable_count > 0 {
                let data = function.local_free_variables.as_ptr().cast::<usize>();

                for i in 0..function.local_free_variable_count {
                    let index = data.add(i as _).read();
                    (*frame)
                        .upvalues
                        .add(i as _)
                        .write(Value::new(self.mutator.allocate(
                            Upvalue {
                                closed: false,
                                upval: Upval {
                                    local: (*frame).locals.add(index as _),
                                },
                            },
                            comet::gc_base::AllocationSpace::New,
                        )));
                }
            }

            macro_rules! vm_ret {
                ($val: expr) => {
                    for i in 0..function.local_free_variable_count {
                        (*(*frame).upvalues.add(i as usize)).upvalue_close();
                    }
                    let prev = frame;
                    self.current_frame = (*prev).prev;
                    if (*prev).exit_on_return.get_bool() {
                        return $val;
                    } else if $val.is_err() {
                        return $val;
                    }
                    let val = $val?;
                    frame = self.current_frame;
                    (*frame).stack.add((*frame).si).write(val);
                    (*frame).si += 1;
                };
            }

            for i in 0..function.arguments {
                if function.variable_arity && i == function.arguments - 1 {}
            }
            loop {}
        }
    }
}
