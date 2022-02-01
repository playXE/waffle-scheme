use num::traits::Inv;

use crate::init::wrong_type_argument;

use super::{defun, value::Value, SchemeThread};

pub fn subr_num_add(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return Ok(Value::new(
                args[0].get_int32().wrapping_add(args[1].get_int32()),
            ));
        }

        if args[0].flonump() && args[1].flonump() {
            return Ok(Value::new(args[0].get_double() + args[1].get_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return Ok(Value::new(args[0].get_number() + args[1].get_number()));
        }
        if !args[1].is_number() {
            return Err(wrong_type_argument(thread, "+", "number", args[1], 2));
        } else {
            return Err(wrong_type_argument(thread, "+", "number", args[0], 1));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return Ok(args[0]);
        }
        return Err(wrong_type_argument(thread, "+", "number", args[0], 1));
    }
    if args.len() == 0 {
        return Ok(Value::new(0i32));
    }
    let mut acc = args[0];
    for i in 1..args.len() {
        if !args[i].is_number() {
            return Err(wrong_type_argument(thread, "+", "number", args[i], i + 1));
        }
        acc = if acc.fixnump() && args[i].fixnump() {
            Value::new(acc.get_int32().wrapping_add(args[i].get_int32()))
        } else {
            Value::new(acc.get_number() + args[i].get_number())
        };
    }
    Ok(acc)
}
pub fn subr_num_sub(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return Ok(Value::new(
                args[0].get_int32().wrapping_sub(args[1].get_int32()),
            ));
        }

        if args[0].flonump() && args[1].flonump() {
            return Ok(Value::new(args[0].get_double() - args[1].get_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return Ok(Value::new(args[0].get_number() - args[1].get_number()));
        }
        if !args[1].is_number() {
            return Err(wrong_type_argument(thread, "-", "number", args[1], 2));
        } else {
            return Err(wrong_type_argument(thread, "-", "number", args[0], 1));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return Ok(args[0]);
        }
        return Err(wrong_type_argument(thread, "-", "number", args[0], 1));
    }
    if args.len() == 0 {
        return Ok(Value::new(0i32));
    }
    let mut acc = args[0];
    for i in 1..args.len() {
        if !args[i].is_number() {
            return Err(wrong_type_argument(thread, "-", "number", args[i], i + 1));
        }
        acc = if acc.fixnump() && args[i].fixnump() {
            Value::new(acc.get_int32().wrapping_sub(args[i].get_int32()))
        } else {
            Value::new(acc.get_number() - args[i].get_number())
        };
    }
    Ok(acc)
}

pub fn subr_num_mul(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return Ok(Value::new(
                args[0].get_int32().wrapping_mul(args[1].get_int32()),
            ));
        }

        if args[0].flonump() && args[1].flonump() {
            return Ok(Value::new(args[0].get_double() * args[1].get_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return Ok(Value::new(args[0].get_number() * args[1].get_number()));
        }
        if !args[1].is_number() {
            return Err(wrong_type_argument(thread, "*", "number", args[1], 2));
        } else {
            return Err(wrong_type_argument(thread, "*", "number", args[0], 1));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return Ok(args[0]);
        }
        return Err(wrong_type_argument(thread, "*", "number", args[0], 1));
    }
    if args.len() == 0 {
        return Ok(Value::new(0i32));
    }
    let mut acc = args[0];
    for i in 1..args.len() {
        if !args[i].is_number() {
            return Err(wrong_type_argument(thread, "*", "number", args[i], i + 1));
        }
        acc = if acc.fixnump() && args[i].fixnump() {
            Value::new(acc.get_int32().wrapping_mul(args[i].get_int32()))
        } else {
            Value::new(acc.get_number() * args[i].get_number())
        };
    }
    Ok(acc)
}

pub fn subr_num_div(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    if args.len() == 2 {
        if args[0].flonump() && args[1].flonump() {
            return Ok(Value::new(args[0].get_double() / args[1].get_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return Ok(Value::new(args[0].get_number() / args[1].get_number()));
        }
        if !args[1].is_number() {
            return Err(wrong_type_argument(thread, "/", "number", args[1], 2));
        } else {
            return Err(wrong_type_argument(thread, "/", "number", args[0], 1));
        }
    }

    if args.len() == 1 {
        if args[0].is_number() {
            return Ok(Value::new(args[0].get_double().inv()));
        }
        return Err(wrong_type_argument(thread, "/", "number", args[0], 1));
    }
    if args.len() == 0 {
        return Ok(Value::new(0i32));
    }
    let mut acc = args[0];
    for i in 1..args.len() {
        if !args[i].is_number() {
            return Err(wrong_type_argument(thread, "+", "number", args[i], i + 1));
        }
        acc = Value::new(acc.get_number() / args[i].get_number());
    }
    Ok(acc)
}

pub fn subr_num_eq(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return Ok(Value::new(args[0] == args[1]));
        }

        if args[0].flonump() && args[1].flonump() {
            return Ok(Value::new(args[0].get_double() == args[1].get_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return Ok(Value::new(args[0].get_number() == args[1].get_number()));
        }

        if !args[1].is_number() {
            return Err(wrong_type_argument(thread, "=", "number", args[1], 2));
        } else {
            return Err(wrong_type_argument(thread, "=", "number", args[0], 1));
        }
    }
    if args.len() == 1 {
        if args[0].is_number() {
            return Ok(Value::new(true));
        }
        return Err(wrong_type_argument(thread, "=", "number", args[0], 1));
    }
    for i in 0..args.len() {
        if !args[i].is_number() {
            return Err(wrong_type_argument(thread, "=", "number", args[i], i + 1));
        }
    }

    for i in 0..args.len() - 1 {
        if args[i].get_number() != args[i + 1].get_number() {
            return Ok(Value::new(false));
        }
    }
    Ok(Value::new(true))
}

pub fn subr_num_lt(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return Ok(Value::new(args[0].get_int32() < args[1].get_int32()));
        }

        if args[0].flonump() && args[1].flonump() {
            return Ok(Value::new(args[0].get_double() < args[1].get_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return Ok(Value::new(args[0].get_number() < args[1].get_number()));
        }

        if !args[1].is_number() {
            return Err(wrong_type_argument(thread, "<", "number", args[1], 2));
        } else {
            return Err(wrong_type_argument(thread, "<", "number", args[0], 1));
        }
    }
    if args.len() == 1 {
        if args[0].is_number() {
            if args[0] == Value::encode_nan_value() {
                return Ok(Value::new(false));
            }
            return Ok(Value::new(true));
        }
        return Err(wrong_type_argument(thread, "<", "number", args[0], 1));
    }
    let mut has_nan = false;
    for i in 0..args.len() {
        if !args[i].is_number() {
            return Err(wrong_type_argument(thread, "<", "number", args[i], i + 1));
        }
        has_nan = args[i] == Value::encode_nan_value();
    }
    if has_nan {
        return Ok(Value::new(false));
    }
    for i in 0..args.len() - 1 {
        if args[i].get_number() >= args[i + 1].get_number() {
            return Ok(Value::new(false));
        }
    }
    Ok(Value::new(true))
}

pub fn subr_num_gt(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return Ok(Value::new(args[0].get_int32() > args[1].get_int32()));
        }

        if args[0].flonump() && args[1].flonump() {
            return Ok(Value::new(args[0].get_double() > args[1].get_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return Ok(Value::new(args[0].get_number() > args[1].get_number()));
        }

        if !args[1].is_number() {
            return Err(wrong_type_argument(thread, ">", "number", args[1], 2));
        } else {
            return Err(wrong_type_argument(thread, ">", "number", args[0], 1));
        }
    }
    if args.len() == 1 {
        if args[0].is_number() {
            if args[0] == Value::encode_nan_value() {
                return Ok(Value::new(false));
            }
            return Ok(Value::new(true));
        }
        return Err(wrong_type_argument(thread, ">", "number", args[0], 1));
    }
    let mut has_nan = false;
    for i in 0..args.len() {
        if !args[i].is_number() {
            return Err(wrong_type_argument(thread, ">", "number", args[i], i + 1));
        }
        has_nan = args[i] == Value::encode_nan_value();
    }
    if has_nan {
        return Ok(Value::new(false));
    }
    for i in 0..args.len() - 1 {
        if args[i].get_number() <= args[i + 1].get_number() {
            return Ok(Value::new(false));
        }
    }
    Ok(Value::new(true))
}

pub fn subr_num_le(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return Ok(Value::new(args[0].get_int32() <= args[1].get_int32()));
        }

        if args[0].flonump() && args[1].flonump() {
            return Ok(Value::new(args[0].get_double() <= args[1].get_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return Ok(Value::new(args[0].get_number() <= args[1].get_number()));
        }

        if !args[1].is_number() {
            return Err(wrong_type_argument(thread, "<=", "number", args[1], 2));
        } else {
            return Err(wrong_type_argument(thread, "<=", "number", args[0], 1));
        }
    }
    if args.len() == 1 {
        if args[0].is_number() {
            if args[0] == Value::encode_nan_value() {
                return Ok(Value::new(false));
            }
            return Ok(Value::new(true));
        }
        return Err(wrong_type_argument(thread, "<=", "number", args[0], 1));
    }
    let mut has_nan = false;
    for i in 0..args.len() {
        if !args[i].is_number() {
            return Err(wrong_type_argument(thread, "<=", "number", args[i], i + 1));
        }
        has_nan = args[i] == Value::encode_nan_value();
    }
    if has_nan {
        return Ok(Value::new(false));
    }
    for i in 0..args.len() - 1 {
        if args[i].get_number() > args[i + 1].get_number() {
            return Ok(Value::new(false));
        }
    }
    Ok(Value::new(true))
}
pub fn subr_num_ge(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    if args.len() == 2 {
        if args[0].fixnump() && args[1].fixnump() {
            return Ok(Value::new(args[0].get_int32() >= args[1].get_int32()));
        }

        if args[0].flonump() && args[1].flonump() {
            return Ok(Value::new(args[0].get_double() >= args[1].get_double()));
        }

        if args[0].is_number() && args[1].is_number() {
            return Ok(Value::new(args[0].get_number() >= args[1].get_number()));
        }

        if !args[1].is_number() {
            return Err(wrong_type_argument(thread, ">=", "number", args[1], 2));
        } else {
            return Err(wrong_type_argument(thread, ">=", "number", args[0], 1));
        }
    }
    if args.len() == 1 {
        if args[0].is_number() {
            if args[0] == Value::encode_nan_value() {
                return Ok(Value::new(false));
            }
            return Ok(Value::new(true));
        }
        return Err(wrong_type_argument(thread, ">=", "number", args[0], 1));
    }
    let mut has_nan = false;
    for i in 0..args.len() {
        if !args[i].is_number() {
            return Err(wrong_type_argument(thread, ">=", "number", args[i], i + 1));
        }
        has_nan = args[i] == Value::encode_nan_value();
    }
    if has_nan {
        return Ok(Value::new(false));
    }
    for i in 0..args.len() - 1 {
        if args[i].get_number() < args[i + 1].get_number() {
            return Ok(Value::new(false));
        }
    }
    Ok(Value::new(true))
}

pub fn subr_num_integer_pred(_thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    if args[0].fixnump() {
        return Ok(Value::new(true));
    }

    if args[0].is_number() {
        let num = args[0].get_number();
        if num.is_infinite() {
            return Ok(Value::new(false));
        }
        return Ok(Value::new(num.round() == num));
    }
    Ok(Value::new(false))
}

pub fn subr_num_fixnum_pred(_thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    Ok(Value::new(args[0].fixnump()))
}
pub fn subr_num_flonum_pred(_thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    Ok(Value::new(args[0].flonump()))
}

pub fn subr_num_number_pred(_thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    Ok(Value::new(args[0].is_number()))
}

pub fn subr_num_round(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    let arg = args[0];
    if !arg.is_number() {
        return Err(wrong_type_argument(thread, "round", "number", arg, 1));
    }
    if arg.fixnump() {
        return Ok(arg);
    }
    Ok(Value::new(arg.get_number().round()))
}
pub fn subr_num_floor(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    let arg = args[0];
    if !arg.is_number() {
        return Err(wrong_type_argument(thread, "floor", "number", arg, 1));
    }
    if arg.fixnump() {
        return Ok(arg);
    }
    Ok(Value::new(arg.get_number().floor()))
}

pub fn subr_num_nan_pred(thread: &mut SchemeThread, args: &[Value]) -> Result<Value, Value> {
    let arg = args[0];
    if !arg.is_number() {
        return Err(wrong_type_argument(thread, "nan?", "number", arg, 1));
    }
    Ok(Value::new(arg == Value::encode_nan_value()))
}

pub(crate) fn init(thread: &mut SchemeThread) {
    defun(thread, "+", subr_num_add, 0, true, false);
    defun(thread, "-", subr_num_sub, 0, true, false);
    defun(thread, "/", subr_num_div, 1, true, false);
    defun(thread, "*", subr_num_mul, 0, true, false);
    defun(thread, "=", subr_num_eq, 1, true, false);
    defun(thread, "<", subr_num_lt, 1, true, false);
    defun(thread, ">", subr_num_gt, 1, true, false);
    defun(thread, ">=", subr_num_ge, 1, true, false);
    defun(thread, "<=", subr_num_le, 1, true, false);
    defun(thread, "integer?", subr_num_integer_pred, 1, false, false);
    defun(thread, "fixnum?", subr_num_fixnum_pred, 1, false, false);
    defun(thread, "flonum?", subr_num_flonum_pred, 1, false, false);
    defun(thread, "number?", subr_num_flonum_pred, 1, false, false);
    defun(thread, "round", subr_num_round, 1, false, false);
    defun(thread, "floor", subr_num_floor, 1, false, false);
    defun(thread, "nan?", subr_num_nan_pred, 1, false, false);
}
