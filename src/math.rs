use crate::{
    sexp::{CallResult, ContextRef, Value},
    vm::{defun, type_error},
};

pub fn subr_num_add(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return CallResult::Done(Value::new_i32(
                args[0].as_int32().wrapping_add(args[1].as_int32()),
            ));
        }

        if args[0].flonump() && args[1].flonump() {
            return CallResult::Done(Value::new_f64(args[0].as_double() + args[1].as_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return CallResult::Done(Value::new_f64(args[0].as_number() + args[1].as_number()));
        }
        if !args[1].is_number() {
            return CallResult::Done(type_error(ctx, "+", 2, "number", args[1]));
        } else {
            return CallResult::Done(type_error(ctx, "+", 1, "number", args[0]));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return CallResult::Done(args[0]);
        }
        return CallResult::Done(type_error(ctx, "+", 1, "number", args[0]));
    }
    if args.len() == 0 {
        return CallResult::Done(Value::new_i32(0i32));
    }
    let mut acc = args[0];
    for i in 1..args.len() {
        if !args[i].is_number() {
            return CallResult::Done(type_error(ctx, "+", i as u32 + 1, "number", args[i]));
        }
        acc = if acc.fixnump() && args[i].fixnump() {
            Value::new_i32(acc.as_int32().wrapping_add(args[i].as_int32()))
        } else {
            Value::new_f64(acc.as_number() + args[i].as_number())
        };
    }
    CallResult::Done(acc)
}

pub fn subr_num_sub(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return CallResult::Done(Value::new_i32(
                args[0].as_int32().wrapping_sub(args[1].as_int32()),
            ));
        }

        if args[0].flonump() && args[1].flonump() {
            return CallResult::Done(Value::new_f64(args[0].as_double() - args[1].as_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return CallResult::Done(Value::new_f64(args[0].as_number() - args[1].as_number()));
        }
        if !args[1].is_number() {
            return CallResult::Done(type_error(ctx, "-", 2, "number", args[1]));
        } else {
            return CallResult::Done(type_error(ctx, "-", 1, "number", args[0]));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return CallResult::Done(args[0]);
        }
        return CallResult::Done(type_error(ctx, "-", 1, "number", args[0]));
    }
    if args.len() == 0 {
        return CallResult::Done(Value::new_i32(0i32));
    }
    let mut acc = args[0];
    for i in 1..args.len() {
        if !args[i].is_number() {
            return CallResult::Done(type_error(ctx, "-", i as u32 + 1, "number", args[i]));
        }
        acc = if acc.fixnump() && args[i].fixnump() {
            Value::new_i32(acc.as_int32().wrapping_sub(args[i].as_int32()))
        } else {
            Value::new_f64(acc.as_number() - args[i].as_number())
        };
    }
    CallResult::Done(acc)
}

pub fn subr_num_mul(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return CallResult::Done(Value::new_i32(
                args[0].as_int32().wrapping_mul(args[1].as_int32()),
            ));
        }

        if args[0].flonump() && args[1].flonump() {
            return CallResult::Done(Value::new_f64(args[0].as_double() * args[1].as_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return CallResult::Done(Value::new_f64(args[0].as_number() * args[1].as_number()));
        }
        if !args[1].is_number() {
            return CallResult::Done(type_error(ctx, "*", 2, "number", args[1]));
        } else {
            return CallResult::Done(type_error(ctx, "*", 1, "number", args[0]));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return CallResult::Done(args[0]);
        }
        return CallResult::Done(type_error(ctx, "*", 1, "number", args[0]));
    }
    if args.len() == 0 {
        return CallResult::Done(Value::new_i32(0i32));
    }
    let mut acc = args[0];
    for i in 1..args.len() {
        if !args[i].is_number() {
            return CallResult::Done(type_error(ctx, "*", i as u32 + 1, "number", args[i]));
        }
        acc = if acc.fixnump() && args[i].fixnump() {
            Value::new_i32(acc.as_int32().wrapping_mul(args[i].as_int32()))
        } else {
            Value::new_f64(acc.as_number() * args[i].as_number())
        };
    }
    CallResult::Done(acc)
}

pub fn subr_num_div(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return CallResult::Done(Value::new_i32(
                args[0].as_int32().wrapping_div(args[1].as_int32()),
            ));
        }

        if args[0].flonump() && args[1].flonump() {
            return CallResult::Done(Value::new_f64(args[0].as_double() / args[1].as_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return CallResult::Done(Value::new_f64(args[0].as_number() / args[1].as_number()));
        }
        if !args[1].is_number() {
            return CallResult::Done(type_error(ctx, "/", 2, "number", args[1]));
        } else {
            return CallResult::Done(type_error(ctx, "/", 1, "number", args[0]));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return CallResult::Done(args[0]);
        }
        return CallResult::Done(type_error(ctx, "/", 1, "number", args[0]));
    }
    if args.len() == 0 {
        return CallResult::Done(Value::new_i32(0i32));
    }
    let mut acc = args[0];
    for i in 1..args.len() {
        if !args[i].is_number() {
            return CallResult::Done(type_error(ctx, "/", i as u32 + 1, "number", args[i]));
        }
        acc = if acc.fixnump() && args[i].fixnump() {
            Value::new_i32(acc.as_int32().wrapping_div(args[i].as_int32()))
        } else {
            Value::new_f64(acc.as_number() / args[i].as_number())
        };
    }
    CallResult::Done(acc)
}

pub fn subr_num_eq(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return CallResult::Done(Value::new_bool(args[0].as_int32() == args[1].as_int32()));
        }

        if args[0].flonump() && args[1].flonump() {
            return CallResult::Done(Value::new_bool(args[0].as_double() == args[1].as_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return CallResult::Done(Value::new_bool(args[0].as_number() == args[1].as_number()));
        }
        if !args[1].is_number() {
            return CallResult::Done(type_error(ctx, "=", 2, "number", args[1]));
        } else {
            return CallResult::Done(type_error(ctx, "=", 1, "number", args[0]));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return CallResult::Done(Value::new_bool(true));
        }
        return CallResult::Done(type_error(ctx, "=", 1, "number", args[0]));
    }
    if args.len() == 0 {
        return CallResult::Done(Value::new_i32(0i32));
    }

    for i in 0..args.len() - 1 {
        if !args[i].is_number() {
            return CallResult::Done(type_error(ctx, "=", i as u32 + 1, "number", args[i]));
        }
        if args[i].as_number() != args[i + 1].as_number() {
            return CallResult::Done(Value::new_bool(false));
        }
    }
    CallResult::Done(Value::new_bool(true))
}

pub fn subr_num_lt(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return CallResult::Done(Value::new_bool(args[0].as_int32() < args[1].as_int32()));
        }

        if args[0].flonump() && args[1].flonump() {
            return CallResult::Done(Value::new_bool(args[0].as_double() < args[1].as_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return CallResult::Done(Value::new_bool(args[0].as_number() < args[1].as_number()));
        }
        if !args[1].is_number() {
            return CallResult::Done(type_error(ctx, "<", 2, "number", args[1]));
        } else {
            return CallResult::Done(type_error(ctx, "<", 1, "number", args[0]));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return CallResult::Done(Value::new_bool(true));
        }
        return CallResult::Done(type_error(ctx, "<", 1, "number", args[0]));
    }
    if args.len() == 0 {
        return CallResult::Done(Value::new_i32(0i32));
    }

    for i in 0..args.len() - 1 {
        if !args[i].is_number() {
            return CallResult::Done(type_error(ctx, "<", i as u32 + 1, "number", args[i]));
        }
        if args[i].as_number() < args[i + 1].as_number() {
            return CallResult::Done(Value::new_bool(false));
        }
    }
    CallResult::Done(Value::new_bool(true))
}

pub fn subr_num_gt(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return CallResult::Done(Value::new_bool(args[0].as_int32() > args[1].as_int32()));
        }

        if args[0].flonump() && args[1].flonump() {
            return CallResult::Done(Value::new_bool(args[0].as_double() > args[1].as_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return CallResult::Done(Value::new_bool(args[0].as_number() > args[1].as_number()));
        }
        if !args[1].is_number() {
            return CallResult::Done(type_error(ctx, ">", 2, "number", args[1]));
        } else {
            return CallResult::Done(type_error(ctx, ">", 1, "number", args[0]));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return CallResult::Done(Value::new_bool(true));
        }
        return CallResult::Done(type_error(ctx, ">", 1, "number", args[0]));
    }
    if args.len() == 0 {
        return CallResult::Done(Value::new_i32(0i32));
    }

    for i in 0..args.len() - 1 {
        if !args[i].is_number() {
            return CallResult::Done(type_error(ctx, ">", i as u32 + 1, "number", args[i]));
        }
        if args[i].as_number() > args[i + 1].as_number() {
            return CallResult::Done(Value::new_bool(false));
        }
    }
    CallResult::Done(Value::new_bool(true))
}

pub fn subr_num_ge(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return CallResult::Done(Value::new_bool(args[0].as_int32() >= args[1].as_int32()));
        }

        if args[0].flonump() && args[1].flonump() {
            return CallResult::Done(Value::new_bool(args[0].as_double() >= args[1].as_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return CallResult::Done(Value::new_bool(args[0].as_number() >= args[1].as_number()));
        }
        if !args[1].is_number() {
            return CallResult::Done(type_error(ctx, ">=", 2, "number", args[1]));
        } else {
            return CallResult::Done(type_error(ctx, ">=", 1, "number", args[0]));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return CallResult::Done(Value::new_bool(true));
        }
        return CallResult::Done(type_error(ctx, ">=", 1, "number", args[0]));
    }
    if args.len() == 0 {
        return CallResult::Done(Value::new_i32(0i32));
    }

    for i in 0..args.len() - 1 {
        if !args[i].is_number() {
            return CallResult::Done(type_error(ctx, ">=", i as u32 + 1, "number", args[i]));
        }
        if args[i].as_number() >= args[i + 1].as_number() {
            return CallResult::Done(Value::new_bool(false));
        }
    }
    CallResult::Done(Value::new_bool(true))
}

pub fn subr_num_le(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return CallResult::Done(Value::new_bool(args[0].as_int32() <= args[1].as_int32()));
        }

        if args[0].flonump() && args[1].flonump() {
            return CallResult::Done(Value::new_bool(args[0].as_double() <= args[1].as_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return CallResult::Done(Value::new_bool(args[0].as_number() <= args[1].as_number()));
        }
        if !args[1].is_number() {
            return CallResult::Done(type_error(ctx, "<=", 2, "number", args[1]));
        } else {
            return CallResult::Done(type_error(ctx, "<=", 1, "number", args[0]));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return CallResult::Done(Value::new_bool(true));
        }
        return CallResult::Done(type_error(ctx, "<=", 1, "number", args[0]));
    }
    if args.len() == 0 {
        return CallResult::Done(Value::new_i32(0i32));
    }

    for i in 0..args.len() - 1 {
        if !args[i].is_number() {
            return CallResult::Done(type_error(ctx, "<=", i as u32 + 1, "number", args[i]));
        }
        if args[i].as_number() <= args[i + 1].as_number() {
            return CallResult::Done(Value::new_bool(false));
        }
    }
    CallResult::Done(Value::new_bool(true))
}

pub fn subr_num_integer_pred(_: ContextRef, args: &[Value], _: Value) -> CallResult {
    if args[0].fixnump() {
        return CallResult::Done(Value::new(true));
    }

    if args[0].is_number() {
        let num = args[0].as_number();

        if num.is_infinite() {
            return CallResult::Done(Value::new(false));
        }

        return CallResult::Done(Value::new(num.round() == num));
    }
    CallResult::Done(Value::new(false))
}

pub fn subr_num_fixnum_pred(_: ContextRef, args: &[Value], _: Value) -> CallResult {
    CallResult::Done(Value::new(args[0].fixnump()))
}
pub fn subr_num_flonum_pred(_: ContextRef, args: &[Value], _: Value) -> CallResult {
    CallResult::Done(Value::new(args[0].flonump()))
}

pub fn subr_num_number_pred(_: ContextRef, args: &[Value], _: Value) -> CallResult {
    CallResult::Done(Value::new(args[0].is_number()))
}

pub fn init_math(ctx: ContextRef) {
    defun(ctx, "+", subr_num_add, 1, true);
    defun(ctx, "-", subr_num_sub, 1, true);
    defun(ctx, "/", subr_num_div, 1, true);
    defun(ctx, "*", subr_num_mul, 1, true);
    defun(ctx, "=", subr_num_eq, 1, true);
    defun(ctx, ">", subr_num_gt, 1, true);
    defun(ctx, "<", subr_num_lt, 1, true);
    defun(ctx, "<=", subr_num_le, 1, true);
    defun(ctx, ">=", subr_num_ge, 1, true);
    defun(ctx, "integer?", subr_num_integer_pred, 1, false);
    defun(ctx, "fixnum?", subr_num_fixnum_pred, 1, false);
    defun(ctx, "flonum?", subr_num_flonum_pred, 1, false);
}
