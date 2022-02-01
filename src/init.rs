use crate::runtime::{
    cons, define, defun, make_exception, make_list, make_string, make_vector,
    value::{Null, ScmSymbol, ScmVector, Value, ValueType},
    SchemeThread,
};
use std::sync::atomic::AtomicU64;

pub(crate) fn enable_core(thread: &mut SchemeThread) {
    init_core(thread);
}

pub fn vector_out_of_bounds(
    thread: &mut SchemeThread,
    in_proc: &str,
    index: usize,
    length: usize,
) -> Value {
    let tag = thread
        .runtime
        .global_symbol(crate::runtime::Global::ScmEval);
    let message = make_string(
        thread,
        format!(
            "In procedure: {}: vector access out of bounds: length is {} but tried to access slot at {}",
            in_proc,length, index,
        ),
    );
    Value::new(make_exception(thread, tag, message, Value::new(Null)))
}

pub fn wrong_type_argument(
    thread: &mut SchemeThread,
    in_proc: &str,
    expecting: &str,
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
    crate::runtime::subr_arith::init(thread);
    defun(
        thread,
        "car",
        |thread, args| {
            if !args[0].consp() {
                return Err(wrong_type_argument(thread, "car", "pair", args[0], 1));
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
                return Err(wrong_type_argument(thread, "cdr", "pair", args[0], 1));
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
                return Err(wrong_type_argument(thread, "apply", "procedure", fun, 1));
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
                    return Err(wrong_type_argument(thread, "length", "pair", lst, 1));
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
                return Err(wrong_type_argument(thread, "set-car!", "pair", pair, 1));
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
                return Err(wrong_type_argument(thread, "set-cdr!", "pair", pair, 1));
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
        "eq?",
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
    define(thread, "nil", Value::encode_null_value(), false);
    defun(
        thread,
        "vector?",
        |_thread, args| Ok(Value::new(args[0].vectorp())),
        1,
        false,
        false,
    );
    defun(
        thread,
        "make-vector",
        |thread, args| {
            let count = args[0];
            if !count.is_int32() {
                return Err(wrong_type_argument(thread, "vector", "integer", count, 1));
            }
            let init = args.get(1).copied().unwrap_or(Value::new(0i32));

            let mut vec = make_vector(thread, count.get_int32() as _);
            for _ in 0..count.get_int32() {
                vec.vec.push(&mut thread.mutator, init);
            }
            Ok(Value::new(vec))
        },
        1,
        true,
        false,
    );

    defun(
        thread,
        "vector",
        |thread, args| {
            let mut vec = make_vector(thread, args.len());
            for arg in args.iter() {
                vec.vec.push(&mut thread.mutator, *arg);
            }
            Ok(Value::new(vec))
        },
        0,
        true,
        false,
    );

    defun(
        thread,
        "vector-length",
        |thread, args| {
            let arg = args[0];
            println!("{}", arg);
            if !arg.vectorp() {
                return Err(wrong_type_argument(
                    thread,
                    "vector-length",
                    "vector",
                    arg,
                    1,
                ));
            }
            Ok(Value::new(arg.vector_length() as i32))
        },
        1,
        false,
        false,
    );
    defun(
        thread,
        "vector-ref",
        |thread, args| {
            let arg = args[0];
            if !arg.vectorp() {
                return Err(wrong_type_argument(thread, "vector-ref", "vector", arg, 1));
            }
            let index = args[1];
            if !index.is_int32() {
                return Err(wrong_type_argument(
                    thread,
                    "vector-ref",
                    "integer",
                    index,
                    2,
                ));
            }

            if index.get_int32() as usize >= arg.vector_length() {
                return Ok(Value::new(Null));
            }
            Ok(arg.vector_ref(index.get_int32() as usize))
        },
        2,
        false,
        false,
    );

    defun(
        thread,
        "vector-set!",
        |thread, args| {
            let arg = args[0];
            if !arg.vectorp() {
                return Err(wrong_type_argument(thread, "vector-set!", "vector", arg, 1));
            }
            let index = args[1];
            if !index.is_int32() {
                return Err(wrong_type_argument(
                    thread,
                    "vector-set!",
                    "integer",
                    index,
                    2,
                ));
            }
            let index = index.get_int32() as usize;
            if index < arg.vector_length() {
                arg.vector_set(index, args[2]);
            }
            Ok(Value::new(Null))
        },
        3,
        false,
        false,
    );
    defun(
        thread,
        "vector-cas!",
        |thread, args| {
            let vec = args[0];
            let pos = args[1];
            let old_v = args[2];
            let new_v = args[3];

            if !vec.vectorp() {
                return Err(wrong_type_argument(thread, "vector-cas!", "vector", vec, 1));
            }

            if !pos.is_int32() {
                return Err(wrong_type_argument(
                    thread,
                    "vector-cas!",
                    "integer",
                    pos,
                    2,
                ));
            }

            let index = pos.get_int32() as usize;
            if index >= vec.vector_length() {
                return Err(vector_out_of_bounds(
                    thread,
                    "vector-cas!",
                    index,
                    vec.vector_length(),
                ));
            }
            let slot = &vec.downcast::<ScmVector>().vec[index];
            let as_atomic = unsafe { std::mem::transmute::<_, &AtomicU64>(slot) };
            Ok(Value::new(
                as_atomic
                    .compare_exchange(
                        old_v.get_raw(),
                        new_v.get_raw(),
                        std::sync::atomic::Ordering::SeqCst,
                        std::sync::atomic::Ordering::Relaxed,
                    )
                    .is_ok(),
            ))
        },
        4,
        false,
        false,
    );

    defun(
        thread,
        "vector->list",
        |thread, args| {
            let vec = args[0];
            if !vec.vectorp() {
                return Err(wrong_type_argument(
                    thread,
                    "vector->list",
                    "vector",
                    vec,
                    1,
                ));
            }

            Ok(make_list(thread, &vec.downcast::<ScmVector>().vec))
        },
        1,
        false,
        false,
    );
    defun(
        thread,
        "list->vector",
        |thread, args| {
            let list = args[0];
            if !list.listp() {
                return Err(wrong_type_argument(thread, "list->vector", "pair", list, 1));
            }

            list.to_vector(thread)
        },
        1,
        false,
        false,
    );

    defun(
        thread,
        "vector-fill!",
        |thread, args| {
            let vec = args[0];
            if !vec.vectorp() {
                return Err(wrong_type_argument(
                    thread,
                    "vector-fill!",
                    "vector",
                    vec,
                    1,
                ));
            }

            for i in 0..vec.vector_length() {
                vec.vector_set(i, args[1]);
            }
            Ok(Value::new(Null))
        },
        2,
        false,
        false,
    );
    defun(
        thread,
        "vector-push",
        |thread, args| {
            let vec = args[0];
            if !vec.vectorp() {
                return Err(wrong_type_argument(
                    thread,
                    "vector-fill!",
                    "vector",
                    vec,
                    1,
                ));
            }
            if args.len() > 1 {
                for arg in &args[1..] {
                    vec.downcast::<ScmVector>()
                        .vec
                        .push(&mut thread.mutator, *arg);
                }
            }
            Ok(Value::new(Null))
        },
        1,
        true,
        false,
    );

    defun(
        thread,
        "string?",
        |_thread, args| Ok(Value::new(args[0].stringp())),
        1,
        false,
        false,
    );

    defun(
        thread,
        "string-length",
        |thread, args| {
            if !args[0].stringp() {
                return Err(wrong_type_argument(
                    thread,
                    "string-length",
                    "string",
                    args[0],
                    1,
                ));
            }
            Ok(Value::new(args[0].string_length() as i32))
        },
        1,
        false,
        false,
    );
    defun(
        thread,
        "string-ref",
        |thread, args| {
            if !args[0].stringp() {
                return Err(wrong_type_argument(
                    thread,
                    "string-ref",
                    "string",
                    args[0],
                    1,
                ));
            }

            if !args[1].fixnump() {
                return Err(wrong_type_argument(
                    thread,
                    "string-ref",
                    "integer",
                    args[1],
                    1,
                ));
            }

            let index = args[1].get_int32();
            let string = args[0].string();
            if index > string.string.len() as i32 {
                return Err(vector_out_of_bounds(
                    thread,
                    "string-ref",
                    index as _,
                    string.string.len(),
                ));
            }

            Ok(Value::new(
                string.string.chars().nth(index as _).unwrap() as i32
            ))
        },
        2,
        false,
        false,
    );

    defun(
        thread,
        "char?",
        |_, args| {
            if args[0].fixnump() {
                let x = args[0].get_int32();
                if let Some(_) = char::from_u32(x as u32) {
                    return Ok(Value::new(true));
                }
            }
            Ok(Value::new(false))
        },
        1,
        false,
        false,
    );

    defun(
        thread,
        "char->string",
        |thread, args| {
            if args[0].fixnump() {
                let x = args[0].get_int32();
                if let Some(c) = char::from_u32(x as u32) {
                    return Ok(Value::new(make_string(thread, format!("{}", c))));
                } else {
                }
            }
            let tag = thread
                .runtime
                .global_symbol(crate::runtime::Global::ScmEval);
            let message = make_string(thread, format!("Invalid character: '{}'", args[0]));
            return Err(Value::new(make_exception(
                thread,
                tag,
                message,
                Value::new(Null),
            )));
        },
        1,
        false,
        false,
    );

    defun(
        thread,
        "gensym",
        |thread, _args| {
            let id = crate::runtime::ID.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            let cpy = make_string(thread, format!("GENSYM-#{:x}", id));
            let sym = ScmSymbol {
                name: Value::new(cpy),
                id,
                value: Value::new(Null),
                mutable: true,
            };
            Ok(Value::new(
                thread
                    .mutator
                    .allocate(sym, comet::gc_base::AllocationSpace::New),
            ))
        },
        0,
        false,
        false,
    );
}
