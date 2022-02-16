use comet_extra::alloc::vector::Vector;

use crate::runtime::{
    cons, make_exception, make_list, make_string, make_symbol, make_vector,
    value::{Null, Value},
    SchemeThread,
};

fn parse_error(thread: &mut SchemeThread, msg: impl AsRef<str>) -> Value {
    let tag = thread
        .runtime
        .global_symbol(crate::runtime::Global::ScmRead);
    let message = make_string(thread, msg);
    Value::new(make_exception(thread, tag, message, Value::new(Null)))
}

fn parse_if(thread: &mut SchemeThread, rest: &lexpr::Value) -> Result<Value, Value> {
    if !rest.is_cons() {
        return Err(parse_error(
            thread,
            "incorrect if expression: expected predicate",
        ));
    }
    let rest = rest.as_cons().unwrap();
    let condition = parse(thread, rest.car())?;
    match rest.cdr().as_cons() {
        Some(lst) => {
            let consequent = parse(thread, lst.car())?;
            let alternate = match lst.cdr().as_cons() {
                Some(lst) => {
                    let alternate = parse(thread, lst.car())?;
                    if !lst.cdr().is_null() {
                        return Err(parse_error(
                            thread,
                            "incorrect if expression: no expression after alternate is allowed",
                        ));
                    }
                    alternate
                }
                None => Value::new(Null),
            };

            let mut exp = cons(thread, condition, Value::new(Null));
            let rest = cons(thread, consequent, alternate);
            exp.cdr = Value::new(rest);
            return Ok(Value::new(exp));
        }
        None => {
            return Err(parse_error(
                thread,
                "incorrect if expression: consequent expected",
            ))
        }
    }
}
fn parse_args(thread: &mut SchemeThread, args: &lexpr::Value) -> Result<Value, Value> {
    match args {
        lexpr::Value::Symbol(x) => Ok(Value::new(make_symbol(thread, x))),
        lexpr::Value::Null => Ok(Value::new(Null)),
        lexpr::Value::Cons(lst) => {
            let mut lst2 = Value::new(Null);
            let mut lst = lst;
            loop {
                let arg = lst.car();
                let next = lst.cdr();
                if !arg.is_symbol() {
                    return Err(parse_error(
                        thread,
                        format!("incorrect argument: expected symbol but found {}", arg),
                    ));
                }
                let arg = parse(thread, arg)?;
                if next.is_null() {
                    lst2 = Value::new(cons(thread, arg, lst2));
                    break;
                } else if let Some(sym) = next.as_symbol() {
                    let sym = Value::new(make_symbol(thread, sym));
                    lst2 = Value::new(cons(thread, arg, sym));
                    break;
                } else if let Some(next) = next.as_cons() {
                    lst2 = Value::new(cons(thread, arg, lst2));
                    lst = next;
                }
            }
            Ok(lst2)
        }
    }
}
fn parse_lambda(
    thread: &mut SchemeThread,
    args: &lexpr::Value,
    body: &lexpr::Value,
) -> Result<Value, Value> {
    let args = { match args {} };
}

fn parse_func(
    thread: &mut SchemeThread,
    first: &lexpr::Value,
    rest: &lexpr::Value,
) -> Result<Value, Value> {
    let func = parse(thread, first)?;
    let rest = parse(thread, rest)?;
    Ok(Value::new(cons(thread, func, rest)))
}
pub fn parse(thread: &mut SchemeThread, value: &lexpr::Value) -> Result<Value, Value> {
    match value {
        lexpr::Value::Number(x) => {
            if let Some(val) = x.as_i64() {
                if val as i32 as i64 == val {
                    return Ok(Value::new(val as i32));
                }
                return Ok(Value::new(val as f64));
            } else if let Some(val) = x.as_f64() {
                return Ok(Value::new(val));
            } else {
                return Err(parse_error(
                    thread,
                    format!("Unsupported number type: {:?}", value),
                ));
            }
        }

        lexpr::Value::Bool(x) => Ok(Value::new(*x)),
        lexpr::Value::Symbol(name) => Ok(Value::new(make_symbol(thread, name))),
        lexpr::Value::Null | lexpr::Value::Nil => Ok(Value::new(Null)),
        lexpr::Value::Vector(vals) => {
            let mut vec = make_vector(thread, vals.len());

            for val in vals.iter() {
                let val = parse(thread, val)?;
                vec.vec.push(&mut thread.mutator, val);
            }
            Ok(Value::new(vec))
        }
        lexpr::Value::Cons(cons) => {
            let lst = match value.to_vec() {
                Some(v) => v,
                None => return Err(parse_error(thread, "s-expr is not a valid list")),
            };

            if lst.is_empty() {
                return Err(parse_error(thread, "empty list found"));
            }

            let lst_parts = lst.split_at(1);
            let first = &(lst_parts.0)[0];
            let rest = lst_parts.1;
            match first.as_symbol() {
                Some(val) => match val {
                    _ => parse_func(thread, cons.car(), cons.cdr()),
                },
                None => parse_func(thread, cons.car(), cons.cdr()),
            }
        }
        _ => todo!(),
    }
}
