use crate::{
    sexp::{make_exception, make_string, ContextRef, Global, Op, Procedure, Value, ValueType},
    vm::UpvalLoc,
};

pub fn disasm(ctx: ContextRef, x: Value) -> Value {
    let proc = if x.closurep() {
        x.closure_procedure()
    } else if x.procedurep() {
        x
    } else {
        let kind = ctx.global(Global::ScmEval);
        let message = make_string(ctx, format!("cannot disassembly value '{}'", x));

        return make_exception(
            ctx,
            kind,
            message,
            Value::new_null(),
            Value::new_null(),
            Value::new_null(),
        );
    };

    let mut out = String::new();
    let proc = proc.downcast::<Procedure>(ValueType::Function as _);
    out.push_str("disassembly for procedure");
    if !proc.name.is_null() {
        out.push(' ');
        out.push_str(&proc.name.to_string());
    }
    out.push_str(&format!(" at {:p}:\n", proc));
    out.push_str("constants: \n");
    for i in 0..proc.constants.vector_length() {
        out.push_str(&format!(" {:04}: {}\n", i, proc.constants.vector_ref(i)));
    }
    out.push_str("local_free_variables: \n");
    for i in 0..proc.local_free_variables.bvector_length::<usize>() {
        out.push_str(&format!(
            " {:04}: {}\n",
            i,
            proc.local_free_variables.bvector_ref::<usize>(i)
        ));
    }

    out.push_str("upvalues: \n");
    for i in 0..proc.upvalues.bvector_length::<UpvalLoc>() {
        let l = proc.upvalues.bvector_ref::<UpvalLoc>(i);
        out.push_str(&format!(" {:04}: ({}, {:04})", i, l.local, l.index));
    }
    out.push_str(&format!(
        "stack_size: {}\nlocals: {}\n",
        proc.stack_max, proc.locals
    ));

    out.push_str("code: \n");
    let mut ip = proc.code.bvector_raw();
    unsafe {
        let start = ip;
        let end = ip.add(proc.code.bvector_length::<u8>());

        while ip < end {
            let op = ip.cast::<Op>().read();
            out.push(' ');
            out.push_str(&format!("{:p}: ", ip));
            ip = ip.add(1);

            match op {
                Op::LoadN => out.push_str("LOAD_NULL\n"),
                Op::LoadC => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);
                    out.push_str(&format!("LOAD_CONST {:04}\n", ix));
                }
                Op::LoadI => {
                    let i = ip.cast::<i32>().read();
                    ip = ip.add(4);
                    out.push_str(&format!("LOAD_INT {}\n", i));
                }
                Op::LoadF => {
                    let f = ip.cast::<u64>().read();
                    ip = ip.add(8);
                    out.push_str(&format!("LOAD_FLONUM {}", f64::from_bits(f)));
                }

                Op::LocalRef => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);
                    out.push_str(&format!("LOCAL_REF {}\n", ix));
                }
                Op::LocalSet => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);
                    out.push_str(&format!("LOCAL_SET {}\n", ix));
                }
                Op::ClosureRef => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);

                    out.push_str(&format!("CLOSURE_REF {}\n", ix));
                }
                Op::ClosureSet => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);
                    out.push_str(&format!("CLOSURE_SET {}\n", ix));
                }

                Op::GlobalRef => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);

                    out.push_str(&format!(
                        "GLOBAL_REF {}\n",
                        proc.constants.vector_ref(ix as _)
                    ));
                }

                Op::GlobalSet => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);

                    out.push_str(&format!(
                        "GLOBAL_SET {}\n",
                        proc.constants.vector_ref(ix as _)
                    ));
                }
                Op::Apply => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);
                    out.push_str(&format!("APPLY {}\n", ix));
                }
                Op::TailApply => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);
                    out.push_str(&format!("TAIL_APPLY {}\n", ix));
                }
                Op::Jump => {
                    let new_ip = ip.cast::<u32>().read();
                    ip = ip.add(4);
                    let x = start.add(new_ip as _);
                    out.push_str(&format!("JUMP {:p}\n", x));
                }
                Op::JumpIfFalse => {
                    let new_ip = ip.cast::<u32>().read();
                    ip = ip.add(4);
                    let x = start.add(new_ip as _);
                    out.push_str(&format!("JUMP_IF_FALSE {:p}\n", x));
                }
                Op::JumpIfTrue => {
                    let new_ip = ip.cast::<u32>().read();
                    let x = start.add(new_ip as _);
                    out.push_str(&format!("JUMP_IF_TRUE {:p}\n", x));
                    ip = ip.add(4);
                }
                Op::Return => {
                    out.push_str("RETURN\n");
                }
                Op::Dup => {
                    out.push_str("DUP\n");
                }
                Op::Pop => {
                    out.push_str("POP\n");
                }

                Op::MakeClosure => {
                    out.push_str("MAKE_CLOSURE\n");
                }
            }
        }
    }
    make_string(ctx, out)
}
