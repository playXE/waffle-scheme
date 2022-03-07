use crate::{
    sexp::{make_vector, CallResult, ContextRef, Value},
    vm::{defun, type_error},
};

pub fn subr_vector_make(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if !args[0].is_number() {
        return CallResult::Done(type_error(ctx, "make-vector", 1, "number", args[0]));
    }

    let v = if args.len() > 1 {
        args[1]
    } else {
        Value::new(0)
    };

    CallResult::Done(make_vector(ctx, args[0].as_number().round() as _, v))
}
pub fn subr_vector(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    let n = args.len();
    let v = make_vector(ctx, n, Value::new(0));

    for i in 0..args.len() {
        v.vector_set(i, args[i]);
    }

    CallResult::Done(v)
}

pub fn subr_vector_length(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if !args[0].vectorp() {
        return CallResult::Done(type_error(ctx, "vector-length", 1, "vector", args[0]));
    }

    CallResult::Done(Value::new(args[0].vector_length() as i32))
}
pub fn subr_vector_ref(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if !args[0].vectorp() {
        return CallResult::Done(type_error(ctx, "vector-ref!", 1, "vector", args[0]));
    }
    if !args[1].is_number() {
        return CallResult::Done(type_error(ctx, "vector-ref!", 2, "number", args[1]));
    }

    let ix = if args[1].is_int32() {
        args[1].as_int32() as usize
    } else {
        args[1].as_number().round() as usize
    };
    CallResult::Done(Value::new(args[0].vector_ref(ix)))
}

pub fn subr_vector_set(ctx: ContextRef, args: &[Value], _: Value) -> CallResult {
    if !args[0].vectorp() {
        return CallResult::Done(type_error(ctx, "vector-set!", 1, "vector", args[0]));
    }
    if !args[1].is_number() {
        return CallResult::Done(type_error(ctx, "vector-set!", 2, "number", args[1]));
    }

    let ix = if args[1].is_int32() {
        args[1].as_int32() as usize
    } else {
        args[1].as_number().round() as usize
    };
    args[0].vector_set(ix, args[2]);
    CallResult::Done(Value::new_null())
}

pub fn init_vector(ctx: ContextRef) {
    defun(ctx, "vector", subr_vector, 0, false);
    defun(ctx, "make-vector", subr_vector_make, 1, true);
    defun(ctx, "vector-ref", subr_vector_ref, 2, false);
    defun(ctx, "vector-set!", subr_vector_set, 3, false);
    defun(ctx, "vector-length", subr_vector_length, 1, false);
}
