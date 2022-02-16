use std::{alloc::Layout, intrinsics::unlikely, mem::size_of, ptr::null_mut};

use comet::api::{Trace, Visitor};
use comet_extra::alloc::{array::Array, vector::Vector};

use crate::{
    compiler::{Op, UpvalLoc},
    method_jit::{JITSig, Trampoline},
    runtime::make_list,
    Managed,
};

use super::{
    make_exception, make_string,
    value::{
        Closure, NativeFunction, Null, ScmPrototype, ScmSymbol, Undefined, Upval, Upvalue, Value,
    },
    Global, SchemeThread,
};
pub fn check_arguments(
    thread: &mut SchemeThread,
    argc: usize,
    prototype: Managed<ScmPrototype>,
) -> Result<(), Value> {
    if argc < prototype.arguments as usize
        && (!prototype.variable_arity && argc != prototype.arguments as usize - 1)
    {
        return Err(arity_error_least(thread, prototype.arguments as _, argc));
    } else if argc > prototype.arguments as usize && !prototype.variable_arity {
        return Err(arity_error_most(thread, prototype.arguments as _, argc));
    }
    Ok(())
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

pub struct VMStack {
    start: *mut u8,
    end: *mut u8,
    cursor: *mut u8,

    pub(crate) current_frame: *mut CallFrame,
}

impl VMStack {
    pub fn new() -> Self {
        unsafe {
            let memory = libc::malloc(8 * 8192).cast::<u8>();
            let end = memory.add(8 * 8192);
            Self {
                start: memory,
                end,
                cursor: memory,
                current_frame: null_mut(),
            }
        }
    }
    /// Allocates `size` bytes in a VM stack. Returns NULL if no memory is left
    pub unsafe fn alloc(&mut self, size: usize) -> *mut u8 {
        let result = self.cursor;
        let new_cursor = self.cursor.add(size);
        if new_cursor >= self.end {
            return null_mut();
        }
        self.cursor = new_cursor;
        result
    }

    pub unsafe fn make_frame(
        &mut self,
        callee: Value,
        closure: Option<Managed<Closure>>,
        env: *mut Value,
        args_on_stack: usize,
    ) -> *mut CallFrame {
        if !callee.native_functionp() {
            let prototype = if callee.is_cell::<ScmPrototype>() {
                callee.downcast::<ScmPrototype>()
            } else {
                callee.downcast::<Closure>().prototype
            };
            let stack_size = (prototype.local_free_variable_count + prototype.stack_max) as usize
                * size_of::<Value>()
                + size_of::<CallFrame>();
            let sp = self.cursor;
            let memory = self.alloc(stack_size);
            if memory.is_null() {
                return null_mut();
            }

            let frame = memory.cast::<CallFrame>();

            (*frame).callee = Value::new(prototype);
            (*frame).closure = closure;
            (*frame).sp = sp;
            (*frame).bp = memory.add(size_of::<CallFrame>()).cast();
            (*frame).si = 0;
            (*frame).exit_on_return = false;
            (*frame).upvalues = (*frame).bp.add(prototype.stack_max as usize);
            (*frame).ip = 0;
            (*frame).code = Some(prototype.code);
            (*frame).env = env;
            (*frame).prev = self.current_frame;

            self.current_frame = frame;
            return frame;
        } else {
            // native frames are not allowed to use VM stack
            let stack_size = size_of::<CallFrame>() + (args_on_stack * size_of::<Value>());
            let prev = self.cursor;
            let memory = self.alloc(stack_size);
            if memory.is_null() {
                return null_mut();
            }
            let frame = memory.cast::<CallFrame>();
            (*frame).ip = 0;
            (*frame).code = None;
            (*frame).callee = callee;
            (*frame).closure = None;
            (*frame).exit_on_return = true;
            (*frame).env = null_mut();
            (*frame).si = 0;
            (*frame).sp = prev;
            (*frame).bp = memory.add(size_of::<CallFrame>()).cast();
            (*frame).upvalues = null_mut();
            (*frame).prev = self.current_frame;
            self.current_frame = frame;
            return frame;
        }
    }

    /// Removes frame from the stack and returns true if `exit_on_return` was true
    pub unsafe fn leave_frame(&mut self) -> bool {
        let frame = self.current_frame;
        let should_exit = (*frame).exit_on_return;
        if !(*frame).is_native_frame() {
            let prototype = (*frame).callee.downcast::<ScmPrototype>();

            for i in 0..prototype.local_free_variable_count {
                (*(*frame).upvalues.add(i as _)).upvalue_close();
            }
            if !(*frame).env.is_null() {
                std::alloc::dealloc(
                    (*frame).env.cast(),
                    Layout::array::<Value>(prototype.locals as _).unwrap(),
                );
            }
        }

        self.cursor = (*frame).sp;
        self.current_frame = (*frame).prev;

        should_exit
    }
}
unsafe impl Trace for VMStack {
    fn trace(&mut self, vis: &mut dyn Visitor) {
        let mut frame = self.current_frame;
        unsafe {
            while !frame.is_null() {
                (*frame).trace(vis);
                frame = (*frame).prev;
            }
        }
    }
}
impl Drop for VMStack {
    fn drop(&mut self) {
        unsafe {
            libc::free(self.start.cast());
        }
    }
}
pub struct CallFrame {
    pub(crate) prev: *mut Self,
    /// Saved stack pointer. It points to the start of the frame
    pub(crate) sp: *mut u8,
    /// Pointer to the start of value stack
    pub(crate) bp: *mut Value,
    /// Pointer to the start of upvalue array
    pub(crate) upvalues: *mut Value,
    pub(crate) si: usize,
    /// Local variable storage, allocated at call site and freed when frame is exited
    pub(crate) env: *mut Value,
    pub(crate) exit_on_return: bool,
    pub(crate) ip: usize,
    pub(crate) code: Option<Managed<Array<u8>>>,
    pub(crate) callee: Value,
    pub(crate) closure: Option<Managed<Closure>>,
}
impl CallFrame {
    #[inline]
    pub fn is_native_frame(&self) -> bool {
        self.callee.native_functionp()
    }

    #[inline(always)]
    pub unsafe fn pop(&mut self) -> Value {
        self.si -= 1;
        self.bp.add(self.si).read()
    }

    fn code(&self) -> &[Op] {
        unsafe {
            std::slice::from_raw_parts(
                self.code.unwrap_unchecked().as_ptr().cast::<Op>(),
                self.code.unwrap_unchecked().len() / size_of::<Op>(),
            )
        }
    }
    #[inline(always)]
    pub unsafe fn push(&mut self, val: Value) {
        if !self.is_native_frame() {
            let code = self.code();
            debug_assert!(
                self.bp.add(self.si) < self.upvalues
                    || self
                        .callee
                        .downcast::<ScmPrototype>()
                        .local_free_variable_count
                        == 0,
                "overflow {:p} < {:p} at {}: {:?} (code: {:?})",
                self.bp.add(self.si),
                self.upvalues,
                self.ip - 1,
                code[self.ip - 1],
                code
            );
        }
        self.bp.add(self.si).write(val);

        self.si += 1;
    }

    #[inline(always)]
    pub unsafe fn at(&mut self, at: isize) -> &mut Value {
        &mut *self.bp.offset(at)
    }

    #[inline(always)]
    pub unsafe fn fetch_opcode(&mut self) -> Op {
        let ptr = self
            .code
            .unwrap_unchecked()
            .as_ptr()
            .cast::<Op>()
            .add(self.ip);
        ptr.read()
    }

    #[inline(always)]
    pub fn fetch_constant(&mut self, c: u32) -> Value {
        #[cfg(debug_assertions)]
        {
            self.callee.downcast::<ScmPrototype>().constants[c as usize]
        }
        #[cfg(not(debug_assertions))]
        unsafe {
            *self
                .callee
                .downcast::<ScmPrototype>()
                .constants
                .get_unchecked(c as usize)
        }
    }

    #[inline(always)]
    pub unsafe fn env(&mut self, at: u16) -> &mut Value {
        &mut *self.env.add(at as _)
    }
    #[inline(always)]
    pub unsafe fn upvalue(&mut self, at: u16) -> Value {
        let val = self
            .closure
            .unwrap_unchecked()
            .upvalues
            .get_unchecked(at as usize)
            .upvalue();

        val
    }

    #[inline(always)]
    pub unsafe fn upvalue_set(&mut self, at: u16, val: Value) {
        self.closure.unwrap_unchecked().upvalues[at as usize].upvalue_set(val);
    }

    #[inline(always)]
    pub unsafe fn slice(&self, count: usize) -> &[Value] {
        std::slice::from_raw_parts(self.bp.add(self.si - count), count)
    }
}
unsafe impl Trace for CallFrame {
    fn trace(&mut self, vis: &mut dyn Visitor) {
        self.callee.trace(vis);
        self.closure.trace(vis);
        if !self.is_native_frame() {
            let prototype = self.callee.downcast::<ScmPrototype>();
            let nlocals = prototype.locals;
            let nupvalues = prototype.local_free_variable_count;
            unsafe {
                for i in 0..nlocals {
                    (*self.env.add(i as _)).trace(vis);
                }
                for i in 0..nupvalues {
                    (*self.upvalues.add(i as _)).trace(vis);
                }
            }
            self.code.trace(vis);
        }
        unsafe {
            for i in 0..self.si {
                (*self.bp.add(i)).trace(vis);
            }
        }
    }
}
pub(crate) unsafe extern "C" fn close_over(thread: &mut SchemeThread, frame: &mut CallFrame) {
    let p = frame.pop().downcast::<ScmPrototype>();
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
    frame.push(Value::new(c));
}
unsafe fn vm_loop(thread: &mut SchemeThread, trampoline: &mut Trampoline) -> Value {
    let mut frame = &mut *(*thread).vm_stack.current_frame;
    let hotness = thread.runtime.inner().hotness;
    loop {
        let op = frame.fetch_opcode();

        frame.ip += 1;
        match op {
            Op::LoopHint => {
                let proto = frame.callee.downcast::<ScmPrototype>();
                if unlikely(
                    proto
                        .n_calls
                        .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                        >= hotness,
                ) {
                    let inner = thread.runtime;
                    let inner = inner.inner();
                    let code = inner.jit.compile(thread, proto, inner.dump_jit);
                    proto
                        .jit_code
                        .store(code as *mut u8, std::sync::atomic::Ordering::Release);

                    let fun = { std::mem::transmute::<_, JITSig>(code) };
                    let entry = proto.entry_points.get(&(frame.ip as u32 - 1)).unwrap();
                    if inner.dump_jit {
                        eprintln!("JIT: trampoline to compiled code at {}", entry);
                    }
                    let val = fun(thread, trampoline, *entry as usize);

                    thread.vm_stack.leave_frame();

                    return val;
                }
            }
            Op::PushConstant(c) => {
                let constant = frame.fetch_constant(c);
                frame.push(constant);
            }
            Op::PushInt(x) => {
                frame.push(Value::new(x));
            }
            Op::PushNull => {
                frame.push(Value::new(Null));
            }
            Op::PushTrue | Op::PushFalse => {
                frame.push(Value::new(op == Op::PushTrue));
            }
            Op::Return => {
                let value = if frame.si == 0 {
                    Value::new(Undefined)
                } else {
                    frame.pop()
                };
                let exit = thread.vm_stack.leave_frame();

                /*if exit {
                    return Ok(value);
                }

                frame = &mut *thread.vm_stack.current_frame;
                frame.push(value);*/
                debug_assert!(exit);
                return value;
            }

            Op::LocalGet(at) => {
                let local = *frame.env(at);

                frame.push(local);
            }
            Op::LocalSet(at) => {
                let value = frame.pop();
                *frame.env(at) = value;
            }
            Op::UpvalueGet(at) => {
                let value = frame.upvalue(at);

                frame.push(value);
            }
            Op::UpvalueSet(at) => {
                let value = frame.pop();
                frame.upvalue_set(at, value);
            }
            Op::Pop => {
                frame.pop();
            }
            Op::GlobalGet => {
                let sym = frame.pop().downcast::<ScmSymbol>();
                frame.push(sym.value);
            }
            Op::GlobalSet => {
                let mut sym = frame.pop().downcast::<ScmSymbol>();
                let val = frame.pop();
                sym.value = val;
            }
            Op::Jump(ip) => {
                frame.ip = ip as _;
            }
            Op::JumpIfFalse(ip) => {
                let val = frame.pop();
                if !val.to_boolean() {
                    frame.ip = ip as _;
                }
            }
            Op::TailApply(nargs) => {
                let callee = frame.pop();
                let args = frame.slice(nargs as _);
                /* if callee.native_functionp() {
                    match apply(thread, callee, args) {
                        Ok(value) => match thread.vm_stack.leave_frame() {
                            true => {
                                return Ok(value);
                            }
                            false => {
                                frame = &mut *thread.vm_stack.current_frame;
                                frame.push(value);
                            }
                        },
                        Err(error) => {
                            // pop all frames that were spawned in this loop
                            while !thread.vm_stack.leave_frame() {}
                            return Err(error);
                        }
                    }
                } else {
                    let (proto, closure) = if callee.is_cell::<ScmPrototype>() {
                        (callee.downcast::<ScmPrototype>(), None)
                    } else {
                        (
                            callee.downcast::<Closure>().prototype,
                            Some(callee.downcast::<Closure>()),
                        )
                    };
                    if !proto
                        .jit_code
                        .load(std::sync::atomic::Ordering::Acquire)
                        .is_null()
                        || proto
                            .n_calls
                            .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                            >= thread.runtime.inner().hotness
                    {
                        match apply(thread, callee, args) {
                            Ok(val) => {
                                for _ in 0..nargs {
                                    frame.pop();
                                }
                                frame.push(val);
                                continue;
                            }
                            Err(val) => {
                                while !thread.vm_stack.leave_frame() {}
                                return Err(val);
                            }
                        }
                    } else {
                        let env = match pre_call(thread, callee, args) {
                            Ok(env) => env,
                            Err(error) => {
                                while !thread.vm_stack.leave_frame() {}
                                return Err(error);
                            }
                        };

                        let should_exit = thread.vm_stack.leave_frame();
                        let new_frame = thread.vm_stack.make_frame(callee, closure, env, 0);
                        if new_frame.is_null() {
                            while !thread.vm_stack.leave_frame() {}
                            return Err(stack_overflow(thread, callee));
                        }
                        setup_upvalues(thread, &mut *new_frame);
                        (*new_frame).exit_on_return = should_exit;

                        frame = &mut *new_frame;
                        continue;
                    }
                }*/

                thread.trampoline_fn = callee;
                thread.trampoline_arguments.clear();
                thread.trampoline_arguments.extend_from_slice(args);
                assert!(thread.vm_stack.leave_frame());
                *trampoline = Trampoline::Call;
                return Value::new(Undefined);
            }
            Op::Apply(nargs) => {
                let callee = frame.pop();
                let args = frame.slice(nargs as _);
                match apply(thread, callee, args) {
                    Ok(val) => {
                        for _ in 0..nargs {
                            frame.pop();
                        }
                        frame.push(val);
                    }
                    Err(val) => {
                        thread.vm_stack.leave_frame();
                        *trampoline = Trampoline::Exception;
                        return val;
                    }
                }
                /*println!("apply {}", callee);
                for arg in args {
                    println!("arg {}", arg);
                }*/
                /* if callee.native_functionp() {
                    match apply(thread, callee, args) {
                        Ok(value) => {
                            for _ in 0..nargs {
                                frame.pop();
                            }
                            frame.push(value);
                        }
                        Err(error) => {
                            for _ in 0..nargs {
                                frame.pop();
                            }
                            // pop all frames that were spawned in this loop
                            while !thread.vm_stack.leave_frame() {}
                            return Err(error);
                        }
                    }
                } else {
                    let (proto, closure) = if callee.is_cell::<ScmPrototype>() {
                        (callee.downcast::<ScmPrototype>(), None)
                    } else {
                        (
                            callee.downcast::<Closure>().prototype,
                            Some(callee.downcast::<Closure>()),
                        )
                    };
                    if proto
                        .jit_code
                        .load(std::sync::atomic::Ordering::Acquire)
                        .is_null()
                        || proto
                            .n_calls
                            .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                            >= thread.runtime.inner().hotness
                    {
                        match apply(thread, callee, args) {
                            Ok(val) => {
                                for _ in 0..nargs {
                                    frame.pop();
                                }
                                frame.push(val);
                                continue;
                            }
                            Err(val) => {
                                while !thread.vm_stack.leave_frame() {}
                                return Err(val);
                            }
                        }
                    } else {
                        let env = match pre_call(thread, callee, args) {
                            Ok(env) => env,
                            Err(error) => {
                                while !thread.vm_stack.leave_frame() {}
                                return Err(error);
                            }
                        };
                        for _ in 0..nargs {
                            frame.pop();
                        }

                        let new_frame = thread.vm_stack.make_frame(callee, closure, env, 0);

                        if new_frame.is_null() {
                            while !thread.vm_stack.leave_frame() {}
                            return Err(stack_overflow(thread, callee));
                        }
                        setup_upvalues(thread, &mut *new_frame);
                        (*new_frame).exit_on_return = false;
                        frame = &mut *new_frame;
                        continue;
                    }
                }*/
            }
            Op::CloseOver => {
                close_over(thread, frame);
            }
        }
    }
}

pub fn stack_overflow(thread: &mut SchemeThread, f: Value) -> Value {
    let tag = thread.runtime.global_symbol(super::Global::ScmEval);
    let message = make_string(
        thread,
        format!("stack overflow while calling fucntion {}", f),
    );
    Value::new(make_exception(thread, tag, message, Value::new(Null)))
}

pub fn not_function(thread: &mut SchemeThread, func: Value) -> Value {
    let tag = thread.runtime.global_symbol(super::Global::ScmEval);
    let message = make_string(thread, format!("attempt to apply non-function {}", func));

    return Value::new(make_exception(thread, tag, message, Value::new(Null)));
}
pub(crate) fn pre_call(
    thread: &mut SchemeThread,
    func: Value,
    args: &[Value],
) -> Result<*mut Value, Value> {
    if !func.applicablep() {
        let tag = thread.runtime.global_symbol(super::Global::ScmEval);
        let message = make_string(thread, format!("attempt to apply non-function {}", func));

        return Err(Value::new(make_exception(
            thread,
            tag,
            message,
            Value::new(Null),
        )));
    }
    let prototype = if func.is_cell::<ScmPrototype>() {
        func.downcast::<ScmPrototype>()
    } else {
        func.downcast::<Closure>().prototype
    };
    check_arguments(thread, args.len(), prototype)?;

    unsafe {
        let env = std::alloc::alloc(Layout::array::<Value>(prototype.locals as _).unwrap())
            .cast::<Value>();
        for i in 0..prototype.arguments {
            if prototype.variable_arity && i == prototype.arguments - 1 {
                env.add(i as _)
                    .write(make_list(thread, &args[i as usize..]));
                break;
            } else {
                env.add(i as _).write(args[i as usize]);
            }
        }

        Ok(env)
    }
}

pub unsafe extern "C" fn setup_upvalues(thread: &mut SchemeThread, frame: &mut CallFrame) {
    let prototype = frame.callee.downcast::<ScmPrototype>();
    let data = prototype.local_free_variables.as_ptr().cast::<usize>();

    for i in 0..prototype.local_free_variable_count {
        let index = data.add(i as _).read();

        frame
            .upvalues
            .add(i as _)
            .write(Value::new(thread.mutator.allocate(
                Upvalue {
                    closed: false,
                    upval: Upval {
                        local: frame.env.add(index as _),
                    },
                },
                comet::gc_base::AllocationSpace::New,
            )))
    }
}

fn enter_function(
    thread: &mut SchemeThread,
    function: Value,
    args: &[Value],
) -> Result<Managed<ScmPrototype>, Value> {
    let env = pre_call(thread, function, args)?;
    unsafe {
        let (proto, closure) = if function.is_cell::<ScmPrototype>() {
            (function.downcast::<ScmPrototype>(), None)
        } else {
            (
                function.downcast::<Closure>().prototype,
                Some(function.downcast::<Closure>()),
            )
        };

        let frame = thread.vm_stack.make_frame(function, closure, env, 0);
        (*frame).exit_on_return = true;
        if frame.is_null() {
            return Err(stack_overflow(thread, function));
        }
        setup_upvalues(thread, &mut *frame);
        Ok(proto)
    }
}

pub fn apply(thread: &mut SchemeThread, function: Value, args: &[Value]) -> Result<Value, Value> {
    thread.trampoline_fn = function;
    thread.trampoline_arguments.clear();
    thread.trampoline_arguments.extend_from_slice(args);
    // save frame that entered this trampoline
    let _entry_frame = thread.vm_stack.current_frame;
    loop {
        let function = thread.trampoline_fn;
        let argc = thread.trampoline_arguments.len();
        let argv = thread.trampoline_arguments.as_ptr();
        let args = unsafe { std::slice::from_raw_parts(argv, argc) };
        if function.native_functionp() {
            let func = function.downcast::<NativeFunction>();
            unsafe {
                let frame = thread
                    .vm_stack
                    .make_frame(function, None, null_mut(), args.len());
                if frame.is_null() {
                    return Err(stack_overflow(thread, function));
                }
                for arg in args {
                    (*frame).push(*arg);
                }
                let result = (func.callback)(thread, (*frame).slice(args.len()));
                thread.vm_stack.leave_frame();
                return result;
            }
        } else {
            let proto = enter_function(thread, function, args)?;
            let code = proto.jit_code.load(std::sync::atomic::Ordering::Relaxed);

            if code.is_null() {
                let mut trampoline = Trampoline::Return;
                if proto
                    .n_calls
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                    >= thread.runtime.inner().hotness
                {
                    let inner = thread.runtime;
                    let inner = inner.inner();
                    let code = inner.jit.compile(thread, proto, inner.dump_jit);
                    proto
                        .jit_code
                        .store(code as *mut u8, std::sync::atomic::Ordering::Release);

                    let fun = unsafe { std::mem::transmute::<_, JITSig>(code) };

                    let val = fun(thread, &mut trampoline, 0);
                    unsafe {
                        thread.vm_stack.leave_frame();
                    }
                    match trampoline {
                        Trampoline::Return => return Ok(val),
                        Trampoline::Exception => return Err(val),
                        Trampoline::Jit => continue,
                        Trampoline::Call => {
                            continue;
                        }
                    }
                } else {
                    let result = unsafe { vm_loop(thread, &mut trampoline) };
                    match trampoline {
                        Trampoline::Call => continue,
                        Trampoline::Exception => return Err(result),
                        Trampoline::Return => return Ok(result),
                        Trampoline::Jit => continue,
                    }
                }
            } else {
                let mut trampoline = Trampoline::Return;
                let fun = unsafe { std::mem::transmute::<_, JITSig>(code) };

                let val = fun(thread, &mut trampoline, 0);
                unsafe {
                    thread.vm_stack.leave_frame();
                }
                match trampoline {
                    Trampoline::Return => return Ok(val),
                    Trampoline::Exception => return Err(val),
                    Trampoline::Jit => continue,
                    Trampoline::Call => {
                        continue;
                    }
                }
            }
        };
    }
}
