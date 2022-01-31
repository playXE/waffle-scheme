use crate::runtime::{
    cons, defun, make_exception, make_list, make_string,
    value::{Null, Value, ValueType},
    SchemeThread,
};

pub(crate) fn enable_core(thread: &mut SchemeThread) {
    init_core(thread);
}

pub fn wrong_type_argument(
    thread: &mut SchemeThread,
    in_proc: &str,
    expecting: ValueType,
    got: Value,
    at: usize,
) -> Value {
    let tag = thread
        .runtime
        .global_symbol(crate::runtime::Global::ScmEval);
    let message = make_string(
        thread,
        format!(
            "In procedure {}: Wrong type argument in position {} (expecting {}): {}",
            in_proc, at, expecting, got
        ),
    );
    Value::new(make_exception(thread, tag, message, Value::new(Null)))
}

fn init_core(thread: &mut SchemeThread) {
    defun(
        thread,
        "car",
        |thread, args| {
            if !args[0].consp() {
                return Err(wrong_type_argument(
                    thread,
                    "car",
                    ValueType::Pair,
                    args[0],
                    1,
                ));
            }
            Ok(args[0].car())
        },
        1,
        false,
        false,
    );
    defun(
        thread,
        "cdr",
        |thread, args| {
            if !args[0].consp() {
                return Err(wrong_type_argument(
                    thread,
                    "cdr",
                    ValueType::Pair,
                    args[0],
                    1,
                ));
            }
            Ok(args[0].cdr())
        },
        1,
        false,
        false,
    );

    defun(
        thread,
        "list",
        |thread, args| Ok(make_list(thread, args)),
        0,
        true,
        false,
    );

    defun(
        thread,
        "apply",
        |thread, args| {
            let fun = args[0];
            if !fun.applicablep() {
                return Err(wrong_type_argument(
                    thread,
                    "apply",
                    ValueType::Function,
                    fun,
                    1,
                ));
            }
            crate::runtime::vm::apply(thread, fun, if args.len() > 1 { &args[1..] } else { &[] })
        },
        1,
        true,
        false,
    );

    defun(
        thread,
        "display",
        |_, args| {
            print!("{}", args[0]);
            Ok(Value::new(Null))
        },
        1,
        false,
        false,
    );
    defun(
        thread,
        "displayln",
        |_, args| {
            println!("{}", args[0]);
            Ok(Value::new(Null))
        },
        1,
        false,
        false,
    );
    defun(
        thread,
        "atom?",
        |_, args| {
            let p = args[0];
            Ok(Value::new(
                p.is_bool()
                    || p.is_number()
                    || p.stringp()
                    || p.vectorp()
                    || p.blobp()
                    || p.symbolp(),
            ))
        },
        1,
        false,
        false,
    );
    defun(
        thread,
        "boolean?",
        |_, args| Ok(Value::new(args[0].is_bool())),
        1,
        false,
        false,
    );
    defun(
        thread,
        "integer?",
        |_, args| Ok(Value::new(args[0].is_int32())),
        1,
        false,
        false,
    );
    defun(
        thread,
        "list?",
        |_, args| Ok(Value::new(args[0].listp())),
        1,
        false,
        false,
    );
    defun(
        thread,
        "number?",
        |_, args| Ok(Value::new(args[0].is_number())),
        1,
        false,
        false,
    );

    defun(
        thread,
        "null?",
        |_, args| Ok(Value::new(args[0].is_null())),
        1,
        false,
        false,
    );

    defun(
        thread,
        "pair?",
        |_, args| Ok(Value::new(args[0].consp())),
        1,
        false,
        false,
    );
    defun(
        thread,
        "procedure?",
        |_, args| Ok(Value::new(args[0].applicablep())),
        1,
        false,
        false,
    );

    defun(
        thread,
        "string?",
        |_, args| Ok(Value::new(args[0].stringp())),
        1,
        false,
        false,
    );

    defun(
        thread,
        "symbol?",
        |_, args| Ok(Value::new(args[0].symbolp())),
        1,
        false,
        false,
    );

    defun(
        thread,
        "cons",
        |thread, args| Ok(Value::new(cons(thread, args[0], args[1]))),
        2,
        false,
        false,
    );

    defun(
        thread,
        "length",
        |thread, args| {
            let arg = args[0];
            let mut lst = arg;
            let mut c = 0i32;
            while !lst.is_null() {
                if !lst.consp() {
                    return Err(wrong_type_argument(
                        thread,
                        "length",
                        ValueType::Pair,
                        lst,
                        1,
                    ));
                }
                lst = lst.cdr();
                c += 1;
            }
            Ok(Value::new(c))
        },
        1,
        false,
        false,
    );

    defun(
        thread,
        "set-car!",
        |thread, args| {
            let pair = args[0];
            let val = args[1];
            if !pair.consp() {
                return Err(wrong_type_argument(
                    thread,
                    "set-car!",
                    ValueType::Pair,
                    pair,
                    1,
                ));
            }
            pair.set_car(val);
            Ok(Value::new(Null))
        },
        2,
        false,
        false,
    );

    defun(
        thread,
        "set-cdr!",
        |thread, args| {
            let pair = args[0];
            let val = args[1];
            if !pair.consp() {
                return Err(wrong_type_argument(
                    thread,
                    "set-cdr!",
                    ValueType::Pair,
                    pair,
                    1,
                ));
            }
            pair.set_cdr(val);
            Ok(Value::new(Null))
        },
        2,
        false,
        false,
    );

    defun(
        thread,
        "+",
        |_thread, args| {
            let mut res = args
                .get(0)
                .copied()
                .unwrap_or_else(|| Value::encode_int32(0));
            for arg in args.iter().skip(1) {
                if arg.is_int32() && res.is_int32() {
                    res = Value::new(res.get_int32().wrapping_add(arg.get_int32()));
                } else {
                    res = Value::new(res.get_number() + arg.get_number());
                }
            }
            Ok(res)
        },
        0,
        true,
        false,
    );

    defun(
        thread,
        "-",
        |_thread, args| {
            let mut res = args
                .get(0)
                .copied()
                .unwrap_or_else(|| Value::encode_int32(0));
            for arg in args.iter().skip(1) {
                if arg.is_int32() && res.is_int32() {
                    res = Value::new(res.get_int32().wrapping_sub(arg.get_int32()));
                } else {
                    res = Value::new(res.get_number() - arg.get_number());
                }
            }
            Ok(res)
        },
        0,
        true,
        false,
    );
    defun(
        thread,
        "/",
        |_thread, args| {
            let mut dividend = args[0];
            for arg in args.iter().skip(1) {
                dividend = Value::new(dividend.get_number() / arg.get_number());
            }
            Ok(dividend)
        },
        1,
        true,
        false,
    );
    defun(
        thread,
        "*",
        |_thread, args| {
            let mut res = args
                .get(0)
                .copied()
                .unwrap_or_else(|| Value::encode_int32(0));
            for arg in args.iter().skip(1) {
                if arg.is_int32() && res.is_int32() {
                    res = Value::new(res.get_int32().wrapping_mul(arg.get_int32()));
                } else {
                    res = Value::new(res.get_number() * arg.get_number());
                }
            }
            Ok(res)
        },
        0,
        true,
        false,
    );
    defun(
        thread,
        "=",
        |_, args| {
            let first = args[0];
            for arg in args.iter().skip(1) {
                if !Value::same_value(*arg, first) {
                    return Ok(Value::new(false));
                }
            }
            Ok(Value::new(true))
        },
        1,
        true,
        false,
    );
    defun(
        thread,
        "gc",
        |thread, _| {
            thread.mutator.collect(&mut []);
            Ok(Value::new(Null))
        },
        0,
        false,
        false,
    );
}
