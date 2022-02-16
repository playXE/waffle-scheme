pub mod compiler;
pub mod opcodes;
//pub mod parse;

use std::{intrinsics::unlikely, mem::size_of, ptr::null_mut};

use comet_extra::alloc::vector::Vector;

use crate::{
    compiler::UpvalLoc,
    method_jit::Trampoline,
    runtime::{
        make_list,
        value::{
            Closure, NativeFunction, Null, ScmPrototype, ScmSymbol, Undefined, Upval, Upvalue,
            Value,
        },
        vm::{arity_error_least, arity_error_most, check_arguments, stack_overflow},
        SchemeThread,
    },
    vm::opcodes::Opcode,
    Managed,
};

unsafe fn vm_loop(
    thread: &mut SchemeThread,
    proto: Managed<ScmPrototype>,
    closure: Option<Managed<Closure>>,
    argc: usize,
    argv: *mut Value,
    trampoline: &mut Trampoline,
) -> Value {
    let frame = thread
        .vm_stack
        .make_frame(Value::new(proto), closure, null_mut(), 0);
    if unlikely(frame.is_null()) {
        *trampoline = Trampoline::Exception;
        return stack_overflow(thread, Value::new(proto));
    }
    let frame = &mut *frame;
    frame.si = proto.stack_max as _;
    match check_arguments(thread, argc, proto) {
        Ok(_) => (),
        Err(e) => {
            *trampoline = Trampoline::Exception;
            return e;
        }
    }
    let args = std::slice::from_raw_parts(argv, argc);
    for i in 0..proto.arguments {
        if proto.variable_arity && i == proto.arguments - 1 {
            let lst = make_list(thread, &args[i as usize..]);
            frame.bp.add(i as _).write(lst);
            println!("vaarg r{}: {}", i, lst);
        } else {
            frame.bp.add(i as _).write(args[i as usize]);
            println!("arg r{}: {}", i, args[i as usize]);
        }
    }
    let data = proto.local_free_variables.as_ptr().cast::<usize>();
    for i in 0..proto.local_free_variable_count {
        let index = data.add(i as _).read();
        frame
            .upvalues
            .add(i as _)
            .write(Value::new(thread.mutator.allocate(
                Upvalue {
                    closed: false,
                    upval: Upval {
                        local: frame.bp.add(index as _),
                    },
                },
                comet::gc_base::AllocationSpace::New,
            )));
    }
    let mut ip = 0;
    let code = frame.code.unwrap_unchecked();
    macro_rules! ret {
        ($val: expr) => {{
            thread.vm_stack.leave_frame();
            return $val;
        }};
    }
    loop {
        let op = code.as_ptr().cast::<Opcode>().add(ip).read();
        ip += 1;

        match op {
            Opcode::Move(dst, src) => {
                let src = frame.bp.add(src as _).read();
                frame.bp.add(dst as _).write(src);
            }
            Opcode::LoadI(r, i) => {
                frame.bp.add(r as _).write(Value::new(i));
            }
            Opcode::LoadK(r, k) => {
                let k = frame.callee.downcast::<ScmPrototype>().constants[k as usize];
                frame.bp.add(r as _).write(k);
            }
            Opcode::LoadF(r) => frame.bp.add(r as _).write(Value::new(false)),
            Opcode::LoadT(r) => frame.bp.add(r as _).write(Value::new(true)),
            Opcode::LoadN(r) => frame.bp.add(r as _).write(Value::new(Null)),
            Opcode::LoadG(r, k) => {
                let k = frame.callee.downcast::<ScmPrototype>().constants[k as usize];
                let sym = k.downcast::<ScmSymbol>();
                frame.bp.add(r as _).write(sym.value);
            }
            Opcode::StoreG(k, r) => {
                let k = frame.callee.downcast::<ScmPrototype>().constants[k as usize];
                let mut sym = k.downcast::<ScmSymbol>();
                let value = frame.bp.add(r as _).read();
                sym.value = value;
            }
            Opcode::LoadU(r, i) => {
                let value = frame.closure.unwrap_unchecked().upvalues[i as usize].upvalue();
                frame.bp.add(r as _).write(value);
            }
            Opcode::StoreU(i, r) => {
                let value = frame.bp.add(r as _).read();
                frame.closure.unwrap_unchecked().upvalues[i as usize].upvalue_set(value);
            }
            Opcode::Jump(new_ip) => {
                ip = new_ip as usize;
            }
            Opcode::JumpIfFalse(r, new_ip) => {
                let r = frame.bp.add(r as _).read();
                if !r.to_boolean() {
                    ip = new_ip as usize;
                }
            }
            Opcode::JumpIfTrue(r, new_ip) => {
                let r = frame.bp.add(r as _).read();
                if r.to_boolean() {
                    ip = new_ip as usize;
                }
            }
            Opcode::Apply(r1, r2, nargs) => {
                // r1 is the destination register
                // r2 is the register which contains the function
                // nargs is the number of arguments

                let rwin = r2 + 1;

                let callee = frame.bp.add(r2 as _).read();
                let args = std::slice::from_raw_parts(frame.bp.add(rwin as _), nargs as _);
                match apply(thread, callee, args) {
                    Ok(value) => {
                        frame.bp.add(r1 as _).write(value);
                    }
                    Err(value) => {
                        *trampoline = Trampoline::Exception;
                        ret!(value);
                    }
                }
            }
            Opcode::TailApply(r1, nargs) => {
                // r1 is the register which contains the function
                // nargs is the number of arguments
                thread.trampoline_arguments.clear();
                let rwin = r1 + 1;
                let args = std::slice::from_raw_parts(frame.bp.add(rwin as _), nargs as _);
                *trampoline = Trampoline::Call;
                thread.trampoline_arguments.extend_from_slice(args);
                thread.trampoline_fn = frame.bp.add(r1 as _).read();
                ret!(Value::new(Undefined));
            }
            Opcode::Closure(r1, r2) => {
                let p = frame.bp.add(r2 as _).read().downcast::<ScmPrototype>();
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
                frame.bp.add(r1 as _).write(Value::new(c));
            }
            Opcode::Return(r1) => {
                let val = frame.bp.add(r1 as _).read();
                ret!(val);
            }
            Opcode::Return0 => ret!(Value::new(Undefined)),
        }
    }
}

pub fn apply(thread: &mut SchemeThread, func: Value, args: &[Value]) -> Result<Value, Value> {
    thread.trampoline_fn = func;
    thread.trampoline_arguments.clear();
    thread.trampoline_arguments.extend_from_slice(args);
    unsafe {
        loop {
            let mut trampoline = Trampoline::Return;
            let argc = thread.trampoline_arguments.len();
            let argv = thread.trampoline_arguments.as_ptr();

            let func = thread.trampoline_fn;

            if func.native_functionp() {
                let frame = thread.vm_stack.make_frame(func, None, null_mut(), 0);
                if frame.is_null() {
                    return Err(stack_overflow(thread, func));
                }
                let native = func.downcast::<NativeFunction>();
                if args.len() < native.arguments {
                    return Err(arity_error_least(thread, native.arguments, args.len()));
                } else if args.len() > native.arguments && !native.variable_arity {
                    return Err(arity_error_most(thread, native.arguments, args.len()));
                }
                return (native.callback)(thread, &args);
            } else {
                let (prototype, closure) = if func.is_cell::<Closure>() {
                    (
                        func.downcast::<Closure>().prototype,
                        Some(func.downcast::<Closure>()),
                    )
                } else {
                    (func.downcast::<ScmPrototype>(), None)
                };
                let value = vm_loop(
                    thread,
                    prototype,
                    closure,
                    argc,
                    argv as *mut Value,
                    &mut trampoline,
                );
                match trampoline {
                    Trampoline::Call => continue,
                    Trampoline::Return => return Ok(value),
                    Trampoline::Exception => return Err(value),
                    Trampoline::Jit => continue,
                }
            }
        }
    }
}
