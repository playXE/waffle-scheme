use std::{
    mem::size_of,
    ptr::null_mut,
    sync::atomic::{AtomicPtr, AtomicUsize},
};

use comet::{
    api::{Collectable, Finalize, Trace, Visitor},
    letroot,
};
use comet_extra::alloc::{hash::HashMap, vector::Vector};

use crate::{
    runtime::{
        cons, convert_module_name, env_define, env_globalp, env_qualify_name, lexpr_to_value,
        load_module, make_blob, make_exception, make_string, make_symbol, make_table, make_vector,
        module_loaded, register_module_,
        value::{
            print_bytecode, Macro, Null, ScmPrototype, ScmString, ScmSymbol, ScmTable, Undefined,
            Value,
        },
        SchemeThread,
    },
    Heap, Managed,
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Op {
    PushInt(i32),
    PushTrue,
    PushFalse,
    PushNull,
    PushConstant(u32),
    Pop,
    GlobalSet,
    GlobalGet,
    LocalSet(u16),
    LocalGet(u16),
    UpvalueSet(u16),
    UpvalueGet(u16),
    CloseOver,
    Return,
    Apply(u16),
    TailApply(u16),
    JumpIfFalse(u32),
    Jump(u32),
    LoopHint,
}

unsafe impl Trace for Op {}
/// A structure describing the location of a free variable relative to the function it's being used in
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FreeVariableInfo {
    /// The lexical location of the variable
    pub lexical_level: usize,
    pub lexical_index: usize,
    /// The upvalue's index at runtime, either in the upvalues array of the
    /// preceding function, or in the locals array of the currently executing
    /// function
    pub index: usize,
    pub name: Value,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct UpvalLoc {
    pub local: bool,
    pub index: u16,
}

#[allow(dead_code)]
pub struct Compiler {
    parent: Option<*mut Compiler>,
    pub code: Vec<Op>,
    free_variables: Vec<FreeVariableInfo>,
    free_upvariables: Vec<FreeVariableInfo>,
    local_free_variable_count: usize,
    upvalue_count: usize,
    stack_max: usize,
    stack_size: isize,
    locals: usize,
    constants: Vector<Value, Heap>,

    closure: bool,
    name: Option<Managed<ScmString>>,
    env: Managed<ScmTable>,
    depth: usize,
    dump_bytecode: bool,
}
unsafe impl Trace for Compiler {
    fn trace(&mut self, vis: &mut dyn comet::api::Visitor) {
        match self.parent {
            Some(parent) => unsafe {
                (*parent).trace(vis);
            },
            _ => (),
        }
        self.constants.trace(vis);
        self.env.trace(vis);
        self.name.trace(vis);
    }
}

pub struct MacroInfo {
    name: Value,
    args: Value,
    body: Value,
}

unsafe impl Trace for MacroInfo {
    fn trace(&mut self, vis: &mut dyn Visitor) {
        self.name.trace(vis);
        self.args.trace(vis);
        self.body.trace(vis);
    }
}

impl Compiler {
    pub fn clear(&mut self) {
        self.code.clear();
        self.free_variables.clear();
        self.free_upvariables.clear();
        self.local_free_variable_count = 0;
        self.upvalue_count = 0;
        self.stack_max = 0;
        self.stack_size = 0;
        self.locals = 0;
        self.closure = false;
        self.name = None;
        self.constants.clear();
    }
    pub fn new(
        thread: &mut SchemeThread,
        parent: Option<*mut Self>,
        env: Option<Managed<ScmTable>>,
        depth: usize,
    ) -> Self {
        let constants = Vector::new(&mut thread.mutator);
        Self {
            free_upvariables: vec![],
            dump_bytecode: thread.runtime.inner().dump_bytecode,
            parent,
            code: vec![],
            free_variables: vec![],
            local_free_variable_count: 0,
            upvalue_count: 0,
            stack_max: 0,
            stack_size: 0,
            locals: 0,
            constants,
            closure: false,
            name: None,
            env: env.unwrap_or_else(|| thread.runtime.inner().core_module.unwrap()),
            depth,
        }
    }

    pub fn dump(&self, message: &str) {
        if self.dump_bytecode {
            for _ in 0..self.depth {
                eprint!(" ");
            }
            eprintln!("cc: {}", message);
        }
    }
    pub fn module(&mut self, thread: &mut SchemeThread, exp: &lexpr::Value) -> Result<(), Value> {
        let name = exp
            .as_cons()
            .map(|x| x.car())
            .ok_or_else(|| self.syntax_error(thread, "cons list expected for module name"))?;

        if !name.is_symbol() && !name.is_cons() {
            return Err(self.syntax_error(thread, "first argument to module must be a valid module name (a symbol or a list of one or more symbols)"));
        }

        let internal_name = convert_module_name(thread, name)?;

        self.enter_module(thread, internal_name)
    }

    pub fn import(&mut self, thread: &mut SchemeThread, exp: &lexpr::Value) -> Result<(), Value> {
        let module_name = convert_module_name(thread, exp)?;
        let module = load_module(thread, module_name.string())?;
        let unqualified = thread
            .runtime
            .global_symbol(crate::runtime::Global::UnqualifiedImports);
        let env = self.env.get(Value::new(unqualified)).unwrap();
        env.vector_push(thread, module);
        //thread.runtime.inner().unqualified_imports.push(module);
        Ok(())
    }

    pub fn parse_symbol(
        &mut self,
        thread: &mut SchemeThread,
        val: &lexpr::Value,
    ) -> Result<Managed<ScmSymbol>, Value> {
        match val {
            lexpr::Value::Symbol(x) => Ok(make_symbol(thread, x)),
            e => return Err(self.syntax_error(thread, format!("symbol expected but found {}", e))),
        }
    }

    pub fn parse_args(
        &mut self,
        thread: &mut SchemeThread,
        list: &lexpr::Value,
    ) -> Result<Value, Value> {
        if list.is_null() {
            return Ok(Value::new(Null));
        }

        match list {
            lexpr::Value::Cons(pair) => {
                if let Some(sym) = pair.car().as_symbol() {
                    let sym = Value::new(make_symbol(thread, sym));
                    let rest = self.parse_args(thread, pair.cdr())?;
                    Ok(Value::new(cons(thread, sym, rest)))
                } else {
                    Err(self
                        .syntax_error(thread, format!("expected argument name but found {}", list)))
                }
            }
            lexpr::Value::Symbol(sym) => Ok(Value::new(make_symbol(thread, sym))),
            _ => Err(self.syntax_error(
                thread,
                format!("expected list of arguments but found {}", list),
            )),
        }
    }
    pub fn parse_begin(
        &mut self,
        thread: &mut SchemeThread,
        body: &lexpr::Value,
        macros: &mut Vector<MacroInfo, Heap>,
    ) -> Result<Value, Value> {
        if body.is_null() {
            return Ok(Value::new(Null));
        }

        match body.as_cons() {
            Some(cons) => {
                if cons.cdr().is_null() {
                    let val = self.parse(thread, cons.car(), macros)?;

                    return Ok(Value::new(crate::runtime::cons(
                        thread,
                        val,
                        Value::new(Null),
                    )));
                } else {
                    let first = self.parse(thread, cons.car(), macros)?;
                    let second = self.parse_begin(thread, cons.cdr(), macros)?;
                    //let ls = crate::runtime::cons(thread, second, Value::new(Null));
                    return Ok(Value::new(crate::runtime::cons(
                        thread,
                        Value::new(first),
                        Value::new(second),
                    )));
                }
            }
            None => Err(self.syntax_error(thread, "malformed begin block")),
        }
    }
    pub fn parse_lambda(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        macros: &mut Vector<MacroInfo, Heap>,
    ) -> Result<Value, Value> {
        if let Some(list) = exp.as_cons() {
            let args = self.parse_args(thread, list.car())?;

            let body = if list.cdr().is_cons() {
                self.parse_begin(thread, list.cdr(), macros)?
            } else {
                let x = self.parse(thread, list.cdr(), macros)?;
                Value::new(cons(thread, x, Value::new(Null)))
            };
            Ok(Value::new(cons(thread, args, body)))
        } else {
            Err(self.syntax_error(thread, format!("malformed lambda: {}", exp)))
        }
    }

    pub fn expect_cons<'a>(
        &mut self,
        thread: &mut SchemeThread,
        exp: &'a lexpr::Value,
        message: impl AsRef<str>,
    ) -> Result<&'a lexpr::Cons, Value> {
        match exp {
            lexpr::Value::Cons(lst) => Ok(lst),
            exp => {
                return Err(self.syntax_error(
                    thread,
                    format!("expected cons but found {}: {}", exp, message.as_ref()),
                ))
            }
        }
    }
    pub fn parse_list(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        macros: &mut Vector<MacroInfo, Heap>,
    ) -> Result<Value, Value> {
        if exp.is_null() {
            return Ok(Value::new(Null));
        }
        match exp.as_cons() {
            Some(lst) => {
                let car = self.parse(thread, lst.car(), macros)?;
                let cdr = self.parse_list(thread, lst.cdr(), macros)?;
                Ok(Value::new(cons(thread, car, cdr)))
            }
            None => Err(self.syntax_error(thread, "list of expressions expected")),
        }
    }
    pub fn parse(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        macros: &mut Vector<MacroInfo, Heap>,
    ) -> Result<Value, Value> {
        match exp {
            lexpr::Value::Char(x) => Ok(Value::new(*x as i32)),
            lexpr::Value::Bool(x) => Ok(Value::new(*x)),
            lexpr::Value::Number(num) => {
                if let Some(i) = num.as_i64() {
                    if i as i32 as i64 == i {
                        return Ok(Value::new(i as i32));
                    } else {
                        return Ok(Value::new(i as f64));
                    }
                } else if let Some(f) = num.as_f64() {
                    return Ok(Value::new(f));
                } else {
                    todo!("bigint")
                }
            }
            lexpr::Value::Symbol(sym) => Ok(Value::new(make_symbol(thread, sym))),
            lexpr::Value::Vector(values) => {
                let mut vec = make_vector(thread, values.len());
                for val in values.iter() {
                    let parsed = self.parse(thread, val, macros)?;
                    vec.vec.push(&mut thread.mutator, parsed);
                }
                Ok(Value::new(vec))
            }
            lexpr::Value::Null | lexpr::Value::Nil => Ok(Value::new(Null)),
            lexpr::Value::String(string) => Ok(Value::new(make_string(thread, string))),
            lexpr::Value::Cons(pair) => {
                let first = pair.car();
                let rest = pair.cdr();
                match first {
                    lexpr::Value::Symbol(sym_name) => match &**sym_name {
                        "module" => {
                            let _ = self.parse_args(thread, rest)?;
                            let name = convert_module_name(thread, &rest)?;
                            self.enter_module(thread, name)?;
                            return Ok(Value::new(Undefined));
                        }
                        // TODO: (import (a) (b))
                        "import" => {
                            self.import(thread, rest)?;
                            return Ok(Value::new(Undefined));
                        }
                        // TODO: (rename x y)
                        "export" => {
                            self.compile_export(thread, rest)?;
                            return Ok(Value::new(Undefined));
                        }
                        "define" => {
                            let s_define = make_symbol(thread, "define");
                            if let Some(lst) = rest.as_cons() {
                                if let lexpr::Value::Symbol(name) = lst.car() {
                                    let value = self.parse(thread, lst.cdr(), macros)?;
                                    let name = make_symbol(thread, name);
                                    let define_body = cons(thread, Value::new(name), value);
                                    let define =
                                        cons(thread, Value::new(s_define), Value::new(define_body));
                                    return Ok(Value::new(define));
                                } else if let lexpr::Value::Cons(name_and_args) = lst.car() {
                                    let s_lambda = Value::new(make_symbol(thread, "lambda"));
                                    let name = self.parse_symbol(thread, name_and_args.car())?;

                                    let body = if lst.cdr().is_cons() {
                                        self.parse_begin(thread, lst.cdr(), macros)?
                                    } else {
                                        self.parse(thread, lst.cdr(), macros)?
                                    };
                                    let args = self.parse_args(thread, name_and_args.cdr())?;
                                    let body = body;
                                    let lambda_args_and_body =
                                        Value::new(cons(thread, args, Value::new(body)));
                                    let lambda =
                                        Value::new(cons(thread, s_lambda, lambda_args_and_body));
                                    let define_body = cons(thread, lambda, Value::new(Null));
                                    let define_body =
                                        cons(thread, Value::new(name), Value::new(define_body));
                                    let define = Value::new(cons(
                                        thread,
                                        Value::new(s_define),
                                        Value::new(define_body),
                                    ));
                                    return Ok(define);
                                }
                            }

                            return Err(self.syntax_error(thread, "malformed definition"));
                        }
                        "defmacro" => {
                            // (defmacro (name args) body)

                            if let Some(lst) = rest.as_cons() {
                                if let Some(name_and_args) = lst.car().as_cons() {
                                    let name = self.parse_symbol(thread, name_and_args.car())?;
                                    let args = self.parse_args(thread, name_and_args.cdr())?;
                                    let body = self.parse_begin(thread, lst.cdr(), macros)?;
                                    let s_defmacro = make_symbol(thread, "defmacro");
                                    let body = Value::new(cons(thread, body, Value::new(Null)));
                                    // let args = cons(thread, args, Value::new(Null));
                                    let name_and_args =
                                        cons(thread, Value::new(name), Value::new(args));
                                    let nargs_and_body =
                                        cons(thread, Value::new(name_and_args), body);
                                    return Ok(Value::new(cons(
                                        thread,
                                        Value::new(s_defmacro),
                                        Value::new(nargs_and_body),
                                    )));
                                }
                            }

                            return Err(self.syntax_error(thread, "malformed macro definition"));
                        }
                        "lambda" => {
                            let lambda = self.parse_lambda(thread, rest, macros)?;

                            let s_lambda = make_symbol(thread, "lambda");
                            return Ok(Value::new(cons(
                                thread,
                                Value::new(s_lambda),
                                Value::new(lambda),
                            )));
                        }
                        "if" => {
                            let lst = self.expect_cons(thread, rest, "malformed if")?;
                            let condition = self.parse(thread, lst.car(), macros)?;
                            let then_and_else =
                                self.expect_cons(thread, lst.cdr(), "<then> and <else> expected")?;
                            let then = self.parse(thread, then_and_else.car(), macros)?;
                            let else_ =
                                self.expect_cons(thread, then_and_else.cdr(), "<else> expected")?;
                            let else_ = self.parse(thread, else_.car(), macros)?;

                            let else_val = cons(thread, else_, Value::new(Null));
                            let then_and_else = cons(thread, then, Value::new(else_val));
                            let s_if = make_symbol(thread, "if");
                            let cond_and_then = cons(thread, condition, Value::new(then_and_else));
                            let if_ = cons(thread, Value::new(s_if), Value::new(cond_and_then));

                            return Ok(Value::new(if_));
                        }
                        "if*" => {
                            let list = self.parse_list(thread, rest, macros)?;

                            let s_ifstar = make_symbol(thread, "if*");
                            return Ok(Value::new(cons(thread, Value::new(s_ifstar), list)));
                        }
                        "set!" => {
                            let list = self.expect_cons(thread, rest, "(set! <name> <value>)")?;
                            let name = self.parse_symbol(thread, list.car())?;
                            let rest =
                                self.expect_cons(thread, list.cdr(), "(set! <name> <value>")?;
                            let value = self.parse(thread, rest.car(), macros)?;
                            let value = cons(thread, value, Value::new(Null));
                            let s_set = make_symbol(thread, "set!");
                            let list = cons(thread, Value::new(name), Value::new(value));
                            return Ok(Value::new(cons(
                                thread,
                                Value::new(s_set),
                                Value::new(list),
                            )));
                        }
                        "`" => {
                            let value = lexpr::Value::Cons(lexpr::Cons::new(
                                lexpr::Value::Symbol("quasiquote".to_string().into_boxed_str()),
                                rest.clone(),
                            ));

                            return self.parse(thread, &value, macros);
                        }
                        ",@" => {
                            let value = lexpr::Value::Cons(lexpr::Cons::new(
                                lexpr::Value::Symbol(
                                    "unquote-splicing".to_string().into_boxed_str(),
                                ),
                                rest.clone(),
                            ));

                            return self.parse(thread, &value, macros);
                        }
                        "," => {
                            let value = lexpr::Value::Cons(lexpr::Cons::new(
                                lexpr::Value::Symbol("unquote".to_string().into_boxed_str()),
                                rest.clone(),
                            ));

                            return self.parse(thread, &value, macros);
                        }
                        "'" => {
                            let value = lexpr::Value::Cons(lexpr::Cons::new(
                                lexpr::Value::Symbol("quote".to_string().into_boxed_str()),
                                rest.clone(),
                            ));

                            return self.parse(thread, &value, macros);
                        }
                        _ => (),
                    },

                    _ => {}
                }

                let exp = self.parse(thread, first, macros)?;
                let list = self.parse_list(thread, rest, macros)?;

                Ok(Value::new(cons(thread, exp, list)))
            }
            _ => todo!("{:?}", exp),
        }
    }

    pub fn compile(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        tail: bool,
    ) -> Result<(), Value> {
        match exp {
            lexpr::Value::Char(x) => {
                let x = *x as i32;
                self.emit(Op::PushInt(x));
                self.push(1);
            }
            lexpr::Value::Bool(x) => {
                if !*x {
                    self.emit(Op::PushFalse);
                } else {
                    self.emit(Op::PushTrue);
                }
                //self.dump(&format!("push-{}", x));
                self.push(1);
            }
            lexpr::Value::Number(x) => {
                if x.is_i64() && x.as_i64().unwrap() as i32 as i64 == x.as_i64().unwrap() {
                    self.emit(Op::PushInt(x.as_i64().unwrap() as i32));
                    self.push(1);
                    // self.dump(&format!("push-int {}", x.as_i64().unwrap()));
                } else {
                    let x = Value::new(x.as_f64().unwrap());
                    self.push_constant(thread, x);
                }
            }
            lexpr::Value::Symbol(sym) => {
                self.compile_ref(thread, sym)?;
            }

            lexpr::Value::Cons(cons) => {
                let function = cons.car();

                match function {
                    lexpr::Value::Symbol(x) => match &**x {
                        "set!" => {
                            self.compile_set(thread, cons.cdr())?;
                            return Ok(());
                        }
                        "define" => {
                            self.compile_define(thread, cons.cdr(), tail)?;
                            return Ok(());
                        }
                        "lambda" => {
                            self.compile_lambda(thread, cons.cdr(), Value::encode_null_value())?;
                            return Ok(());
                        }
                        "while" => {
                            let pred = cons.cdr().as_cons().unwrap().car();
                            let body = cons.cdr().as_cons().unwrap().cdr();
                            self.compile_while(thread, pred, body)?;
                            return Ok(());
                        }
                        "defun" => {
                            let name = cons.cdr().as_cons().unwrap().car();
                            let name = if let lexpr::Value::Symbol(x) = name {
                                make_symbol(thread, x)
                            } else {
                                return Err(self.syntax_error(
                                    thread,
                                    &format!("expected symbol in defun but found {:?}", name),
                                ));
                            };
                            let body = cons.cdr().as_cons().unwrap().cdr();
                            self.compile_defun(thread, Value::new(name), body)?;
                            return Ok(());
                        }
                        "module" => {
                            self.module(thread, cons.cdr())?;
                            return Ok(());
                        }
                        "quote" | "'" => {
                            let val = lexpr_to_value(thread, cons.cdr().as_cons().unwrap().car());
                            self.push_constant(thread, val);
                            return Ok(());
                        }
                        "`" => {
                            let value = lexpr::Value::Cons(lexpr::Cons::new(
                                lexpr::Value::Symbol("quasiquote".to_string().into_boxed_str()),
                                cons.cdr().clone(),
                            ));

                            self.compile(thread, &value, tail)?;
                            return Ok(());
                        }
                        ",@" => {
                            let value = lexpr::Value::Cons(lexpr::Cons::new(
                                lexpr::Value::Symbol(
                                    "unquote-splicing".to_string().into_boxed_str(),
                                ),
                                cons.cdr().clone(),
                            ));

                            self.compile(thread, &value, tail)?;
                            return Ok(());
                        }
                        "," => {
                            let value = lexpr::Value::Cons(lexpr::Cons::new(
                                lexpr::Value::Symbol("unquote".to_string().into_boxed_str()),
                                cons.cdr().clone(),
                            ));

                            self.compile(thread, &value, tail)?;
                            return Ok(());
                        }
                        "import" => {
                            self.import(thread, cons.cdr())?;
                            return Ok(());
                        }
                        "export" => {
                            self.compile_export(thread, cons.cdr())?;
                            return Ok(());
                        }
                        "if" => {
                            self.compile_if(thread, cons.cdr(), tail)?;
                            return Ok(());
                        }
                        "begin" => {
                            self.compile_begin(thread, cons.cdr(), tail)?;
                            return Ok(());
                        }
                        "defmacro" => {
                            let name = cons.cdr().as_cons().unwrap().car();
                            let name = if let lexpr::Value::Symbol(x) = name {
                                make_symbol(thread, x)
                            } else {
                                return Err(self.syntax_error(
                                    thread,
                                    &format!("expected symbol in defmacro but found {:?}", name),
                                ));
                            };
                            let body = cons.cdr().as_cons().unwrap().cdr();
                            self.compile_macro(thread, Value::new(name), body)?;
                            self.push_constant(thread, Value::new(Null));
                            return Ok(());
                        }
                        x => {
                            let sym = make_symbol(thread, x);
                            let x = env_lookup(thread, self.env, Value::new(sym), false);
                            if let Some(Lookup::Global { value, .. }) = x {
                                if value.is_object() && value.get_object().is::<Macro>() {
                                    let expanded =
                                        self.macro_expand_full(thread, value, cons.cdr())?;
                                    self.compile(thread, &expanded, tail)?;
                                    return Ok(());
                                }
                            }
                        }
                    },
                    _ => (),
                }

                self.compile_apply(thread, exp, tail)?;
            }
            lexpr::Value::Null => {
                self.emit(Op::PushNull);
                self.push(1);
            }
            lexpr::Value::String(x) => {
                let string = make_string(thread, x);
                self.push_constant(thread, Value::new(string));
            }
            _ => todo!("{:?}", exp),
        }
        Ok(())
    }

    pub fn compile_while(
        &mut self,
        thread: &mut SchemeThread,
        pred: &lexpr::Value,
        body: &lexpr::Value,
    ) -> Result<(), Value> {
        self.emit(Op::PushNull);
        self.push(1);
        let loop_start = self.code.len();

        self.compile(thread, pred, false)?;

        let patch = self.code.len();
        //self.dump("jump-if-false");
        self.emit(Op::JumpIfFalse(0));
        self.emit(Op::Pop);
        self.pop(2);

        let prev = self.stack_size;
        self.compile_begin(thread, body, false)?;
        if self.stack_size - prev == 0 {
            self.emit(Op::PushNull);
        }
        self.emit(Op::LoopHint);
        self.emit(Op::Jump(loop_start as _));
        let to = self.code.len();
        self.code[patch] = Op::JumpIfFalse(to as _);
        Ok(())
    }
    pub fn compile_begin(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        tail: bool,
    ) -> Result<(), Value> {
        if exp.is_null() {
            self.push_constant(thread, Value::new(Null));
            return Ok(());
        }

        match exp.as_cons() {
            Some(cons) => {
                if cons.cdr().is_null() {
                    self.compile(thread, cons.car(), tail)?;
                    Ok(())
                } else {
                    self.compile(thread, cons.car(), false)?;

                    self.compile_begin(thread, cons.cdr(), tail)
                }
            }
            None => Err(self.syntax_error(
                thread,
                &format!(
                    "Unexpected value passed to begin block instead of a cons: {}",
                    exp
                ),
            )),
        }
    }
    pub fn macro_expand_1_step(
        &mut self,
        thread: &mut SchemeThread,
        p: Value,
        exp: &lexpr::Value,
    ) -> Result<Value, Value> {
        let exp = lexpr_to_value(thread, exp).to_vec(thread)?;
        let p = p.downcast::<Macro>();

        crate::runtime::vm::apply(thread, Value::new(p.p), &exp)
    }

    pub fn macro_expand_full(
        &mut self,
        thread: &mut SchemeThread,
        p: Value,
        exp: &lexpr::Value,
    ) -> Result<lexpr::Value, Value> {
        let expanded = self.macro_expand_1_step(thread, p, exp)?;
        let mut expanded = crate::runtime::value_to_lexpr(thread, expanded);

        if let Some(cons) = expanded.as_cons_mut() {
            if !cons.car().is_symbol() {
                return Ok(expanded);
            }

            let mut cons = Some(cons);
            while let Some(c) = cons {
                let substitute = match c.car().as_cons() {
                    Some(elt) => {
                        if elt.car().is_symbol() {
                            let key = make_symbol(thread, elt.car().as_symbol().unwrap());
                            if let Some(Lookup::Global { value, .. }) =
                                env_lookup(thread, self.env, Value::new(key), false)
                            {
                                if value.is_object() && value.get_object().is::<Macro>() {
                                    let substitute =
                                        self.macro_expand_full(thread, value, elt.cdr())?;
                                    Some(substitute)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                    None => None,
                };
                if let Some(substitute) = substitute {
                    *c.car_mut() = substitute;
                }
                cons = c.cdr_mut().as_cons_mut();
            }
        }
        Ok(expanded)
    }

    pub fn compile_macro(
        &mut self,
        thread: &mut SchemeThread,
        name: Value,
        lambda: &lexpr::Value,
    ) -> Result<(), Value> {
        let exporting = self.exporting(thread);
        let mut closure = false;
        let proto = self.compile_lambda_no_push(thread, lambda, name, &mut closure)?;

        let proto = thread
            .mutator
            .allocate(Macro { p: proto }, comet::gc_base::AllocationSpace::New);
        env_define(
            thread,
            self.env,
            Value::new(name),
            Value::new(proto),
            exporting,
        );
        Ok(())
    }
    pub fn compile_export(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
    ) -> Result<(), Value> {
        let tag = thread
            .runtime
            .global_symbol(crate::runtime::Global::Exports);

        let mut exports = self.env.get(Value::new(tag)).unwrap().table();
        let mut lst = exp.as_cons();
        while let Some(l) = lst {
            let name = l.car();
            if let Some(sym) = name.as_symbol() {
                let sym = make_symbol(thread, sym);
                let qualified = env_qualify_name(thread, self.env, Value::new(sym));
                exports.set(thread, Value::new(sym), Value::new(qualified));
            }
            lst = l.cdr().as_cons();
        }
        Ok(())
    }
    pub fn compile_apply(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        tail: bool,
    ) -> Result<(), Value> {
        let old_stack_size = self.stack_size;
        let mut args = exp.as_cons().unwrap().cdr();
        while args.is_cons() {
            self.compile(thread, args.as_cons().unwrap().car(), false)?;
            args = args.as_cons().unwrap().cdr();
        }
        let argc = self.stack_size - old_stack_size;
        self.compile(thread, exp.as_cons().unwrap().car(), false)?;

        if tail {
            self.emit(Op::TailApply(argc as _));
            //   self.dump(&format!("tail-apply {}", argc));
        } else {
            self.emit(Op::Apply(argc as _));
            // self.dump(&format!("apply {}", argc));
        }

        self.pop(self.stack_size as usize - old_stack_size as usize);
        self.push(1);

        Ok(())
    }

    pub fn compile_set(
        &mut self,
        thread: &mut SchemeThread,
        rest: &lexpr::Value,
    ) -> Result<(), Value> {
        let rest = rest.as_cons().unwrap();

        let name = make_symbol(thread, rest.car().as_symbol().unwrap());
        let value = rest.cdr().as_cons().unwrap().car();

        self.compile(thread, value, false)?;
        if let Some(l) = env_lookup(thread, self.env, Value::new(name), false) {
            self.generate_set(thread, self.env, &l, Value::new(name));
        } else {
            panic!("undefined variable")
        }

        Ok(())
    }
    pub fn exporting(&self, thread: &mut SchemeThread) -> bool {
        let exporting = thread
            .runtime
            .global_symbol(crate::runtime::Global::Exporting);
        env_globalp(thread, self.env) && self.env.contains(Value::new(exporting))
    }
    pub fn compile_defun(
        &mut self,
        thread: &mut SchemeThread,
        name: Value,
        lambda: &lexpr::Value,
    ) -> Result<(), Value> {
        let value;
        let l = if env_globalp(thread, self.env) {
            value = Value::new(name);
            Lookup::Global {
                value: Value::new(Undefined),
                module: Value::new(Undefined),
            }
        } else {
            value = Value::new(self.locals as i32);
            self.locals += 1;
            Lookup::Local {
                index: self.locals - 1,
                level: 0,
                up: false,
                value: Value::new(self.locals as i32 - 1),
            }
        };
        let exporting = self.exporting(thread);
        env_define(thread, self.env, Value::new(name), value, exporting);
        self.compile_lambda(thread, lambda, name)?;
        self.generate_set(thread, self.env, &l, Value::new(name));
        Ok(())
    }

    pub fn compile_define(
        &mut self,
        thread: &mut SchemeThread,
        rest: &lexpr::Value,
        _tail: bool,
    ) -> Result<(), Value> {
        let rest = rest.as_cons().unwrap();
        let name = make_symbol(thread, rest.car().as_symbol().unwrap());
        let expr = rest.cdr().as_cons().unwrap().car();
        let value;
        let l = if env_globalp(thread, self.env) {
            value = Value::new(name);
            Lookup::Global {
                value: Value::new(Undefined),
                module: Value::new(Undefined),
            }
        } else {
            value = Value::new(self.locals as i32);
            self.locals += 1;
            Lookup::Local {
                index: self.locals - 1,
                level: 0,
                up: false,
                value: Value::new(self.locals as i32 - 1),
            }
        };
        let exporting = self.exporting(thread);
        env_define(thread, self.env, Value::new(name), value, exporting);
        self.compile(thread, expr, false)?;

        self.generate_set(thread, self.env, &l, Value::new(name));
        Ok(())
    }
    pub fn compile_lambda(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        name: Value,
    ) -> Result<(), Value> {
        let mut closure = false;
        let proto = self.generate_lambda(thread, 0, exp, false, name, &mut closure)?;
        self.push_constant(thread, proto);
        if closure {
            self.emit(Op::CloseOver);
        }
        Ok(())
    }
    pub fn compile_lambda_no_push(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        name: Value,
        closure: &mut bool,
    ) -> Result<Value, Value> {
        let proto = self.generate_lambda(thread, 0, exp, false, name, closure)?;

        Ok(proto)
    }
    pub fn compile_ref(&mut self, thread: &mut SchemeThread, exp: &Box<str>) -> Result<(), Value> {
        let name = make_symbol(thread, exp);
        let name = Value::new(name);

        let lookup = env_lookup(thread, self.env, name, false);
        if let Some(l) = lookup {
            self.generate_ref(thread, &l, name, name)
        } else {
            return Err(self.syntax_error(thread, format!("undefined variable '{}'", exp)));
        }
    }

    pub fn syntax_error(&mut self, thread: &mut SchemeThread, message: impl AsRef<str>) -> Value {
        let tag = thread
            .runtime
            .global_symbol(crate::runtime::Global::ScmCompile);
        let msg = make_string(thread, format!("syntax error: {}", message.as_ref()));
        Value::new(make_exception(thread, tag, msg, Value::new(Null)))
    }

    pub fn generate_lambda(
        &mut self,
        thread: &mut SchemeThread,
        _from_argc: usize,
        rest: &lexpr::Value,
        _tail: bool,
        name: Value,
        closure: &mut bool,
    ) -> Result<Value, Value> {
        let new_env = make_env(thread, Value::new(self.env), None);

        let mut args = rest.as_cons().unwrap().car();
        let mut variable_arity = false;
        let mut argc = 0i32;

        if let lexpr::Value::Symbol(ref x) = args {
            let arg = make_symbol(thread, x);
            env_define(thread, new_env, Value::new(arg), Value::new(argc), false);

            argc += 1;
            variable_arity = true;
        } else if args.is_cons() {
            while args.is_cons() {
                let args_ = args.as_cons().unwrap();
                let arg = args_.car();

                if !arg.is_symbol() {
                    return Err(self.syntax_error(
                        thread,
                        format!("lambda expects symbol as argument name, got '{:?}'", args),
                    ));
                }

                let arg = make_symbol(thread, arg.as_symbol().unwrap());

                env_define(thread, new_env, Value::new(arg), Value::new(argc), false);
                argc += 1;
                let rest = args_.cdr();
                if rest.is_symbol() {
                    let arg = make_symbol(thread, rest.as_symbol().unwrap());
                    env_define(thread, new_env, Value::new(arg), Value::new(argc), false);
                    argc += 1;
                    variable_arity = true;
                    break;
                } else {
                    args = rest;
                }
            }
        } else if args.is_null() {
        } else {
            return Err(self.syntax_error(
                thread,
                format!("lambda expects () or symbol, got '{:?}'", args),
            ));
        }
        self.dump(&format!("compiling subfunction {}", name));
        let stack = thread.mutator.shadow_stack();
        letroot!(
            cc = stack,
            Compiler::new(thread, Some(self), Some(new_env), self.depth + 1)
        );
        cc.locals = argc as _;

        if !name.is_null() {
            cc.name = Some(name.symbol_name());
        }

        cc.compile_begin(thread, rest.as_cons().unwrap().cdr(), true)?;

        let proto = cc.end(thread, argc as _, variable_arity);
        *closure = cc.closure;
        self.dump(&format!(
            "subfunction compiled {} (upvalues: {})",
            Value::new(proto),
            proto.upvalues.len() / size_of::<UpvalLoc>()
        ));
        Ok(Value::new(proto))
    }

    pub fn compile_if(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        tail: bool,
    ) -> Result<(), Value> {
        let condition = exp.as_cons().unwrap().car();

        let else_expr = exp
            .as_cons()
            .unwrap()
            .cdr()
            .as_cons()
            .unwrap()
            .cdr()
            .as_cons()
            .map(|x| x.car());

        self.compile(thread, condition, false)?;

        let jmp1 = self.code.len();
        self.emit(Op::JumpIfFalse(0));

        self.pop(1);
        //self.dump("jump-if-false");

        let old_stack = self.stack_size as usize;

        match exp.as_cons().unwrap().cdr().as_cons() {
            Some(x) => {
                self.compile(thread, x.car(), tail)?;
            }
            None => {
                self.compile(thread, exp.as_cons().unwrap().cdr(), tail)?;
            }
        }
        self.pop(self.stack_size as usize - old_stack);
        let jmp2 = self.code.len();
        self.emit(Op::Jump(0));
        // self.dump("jump");
        let lbl1 = self.code.len();
        match else_expr {
            Some(val) => {
                self.compile(thread, val, tail)?;
            }
            None => {
                self.push_constant(thread, Value::new(Null));
            }
        }
        self.pop(self.stack_size as usize - old_stack);
        let lbl2 = self.code.len();
        //self.dump(&format!("Patch jump-if-false {}", lbl1));
        //self.dump(&format!("Patch jump {}", lbl2));
        self.code[jmp1] = Op::JumpIfFalse(lbl1 as _);
        self.code[jmp2] = Op::Jump(lbl2 as _);
        Ok(())
    }

    pub fn register_free_variable(&mut self, lookup: &Lookup, name: Value) -> usize {
        let mut l = FreeVariableInfo {
            index: 0,
            lexical_index: 0,
            lexical_level: 0,
            name,
        };

        for i in 0..self.free_variables.len() {
            l = self.free_variables[i];
            if let Lookup::Local { level, index, .. } = lookup {
                if *level == l.lexical_level && l.lexical_index == *index {
                    return i;
                }
            }
        }

        for i in 0..self.free_upvariables.len() {
            l = self.free_upvariables[i];
            if let Lookup::Local { level, index, .. } = lookup {
                if *level == l.lexical_level && l.lexical_index == *index {
                    return i;
                }
            }
        }
        let mut lookup_copy = *lookup;

        if let Lookup::Local { level, index, .. } = lookup {
            l.lexical_level = *level;
            l.lexical_index = *index;

            if l.lexical_level != 0 {
                match &mut lookup_copy {
                    Lookup::Local { level, .. } => *level -= 1,
                    _ => unreachable!(),
                }
                self.closure = true;
                unsafe {
                    l.index = (**self.parent.as_mut().unwrap())
                        .register_free_variable(&lookup_copy, name);
                }
                self.upvalue_count += 1;
                self.free_upvariables.push(l);
                self.free_upvariables.len() - 1
            } else {
                l.index = l.lexical_index;
                self.local_free_variable_count += 1;
                self.free_variables.push(l);
                self.free_variables.len() - 1
            }
        } else {
            unreachable!()
        }
    }
    pub fn emit(&mut self, op: Op) {
        self.code.push(op);
    }
    pub fn emit_pop(&mut self) {
        self.emit(Op::Pop);
        self.pop(1);
    }
    pub fn enter_module(
        &mut self,
        thread: &mut SchemeThread,
        internal_name: Value,
    ) -> Result<(), Value> {
        self.dump(&format!("entering module {}", internal_name));
        if module_loaded(thread, internal_name.string()) {
            self.env = thread
                .runtime
                .inner()
                .modules
                .unwrap()
                .get(internal_name)
                .unwrap()
                .downcast();
            return Ok(());
        }
        let module_env = make_env(
            thread,
            Value::new(thread.runtime.inner().core_module.unwrap()),
            Some(&internal_name.string().to_string()),
        );
        register_module_(thread, internal_name.string(), Value::new(module_env))?;
        self.env = module_env;
        Ok(())
    }
    pub fn generate_ref(
        &mut self,
        thread: &mut SchemeThread,
        lookup: &Lookup,
        _exp: Value,
        name: Value,
    ) -> Result<(), Value> {
        match lookup {
            Lookup::Global { module, .. } => {
                let tmp = env_qualify_name(thread, module.table(), name);
                self.push_constant(thread, Value::new(tmp));
                self.emit(Op::GlobalGet);
                //self.dump("global-get");
                Ok(())
            }
            Lookup::Local { index, up, .. } => {
                if !*up {
                    self.emit(Op::LocalGet(*index as _));
                    self.push(1);
                    // self.dump(&format!("local-get {}", index));
                } else {
                    let index = self.register_free_variable(lookup, name);
                    self.emit(Op::UpvalueGet(index as _));
                    self.push(1);
                    //  self.dump(&format!("upvalue-get {} : {}", index, name));
                }
                Ok(())
            }
        }
    }

    pub fn generate_set(
        &mut self,
        thread: &mut SchemeThread,
        env: Managed<ScmTable>,
        lookup: &Lookup,
        name: Value,
    ) {
        match lookup {
            Lookup::Global { .. } => {
                let p = thread.runtime.global_symbol(crate::runtime::Global::Parent);
                let mut global = env;

                while !env_globalp(thread, global) {
                    global = global.get(Value::new(p)).unwrap().table();
                }
                let qualified_name = env_qualify_name(thread, global, name);

                self.push_constant(thread, Value::new(qualified_name));
                self.emit(Op::GlobalSet);
                //    self.dump("global-set");
                self.pop(1);
            }
            Lookup::Local { index, up, .. } => {
                if *up {
                    let index = self.register_free_variable(lookup, name);
                    self.emit(Op::UpvalueSet(index as _));
                    //  self.dump(&format!("upvalue-set {} : {}", index, name));
                } else {
                    self.emit(Op::LocalSet(*index as _));
                    //  self.dump(&format!("local-set {}", index));
                }
            }
        }
        self.pop(1);
    }

    pub fn push_constant(&mut self, thread: &mut SchemeThread, constant: Value) {
        self.push(1);
        for i in 0..self.constants.len() {
            if self.constants[i] == constant {
                self.emit(Op::PushConstant(i as _));
                // self.dump(&format!("push-constant {} : {}", i, constant));
                return;
            }
        }
        let i = self.constants.len();
        self.constants.push(&mut thread.mutator, constant);
        self.emit(Op::PushConstant(i as _));

        //assert!(i < self.constants.len());
        // self.dump(&format!("push-constant {} : {}", i, constant));
    }

    pub fn push(&mut self, i: usize) {
        self.stack_size += i as isize;
        if self.stack_size as usize > self.stack_max {
            self.stack_max = self.stack_size as _;
        }
    }

    pub fn pop(&mut self, i: usize) {
        self.stack_size -= i as isize;
        if self.stack_size < 0 {
            assert!(false, "stack underflow");
        }
    }

    pub fn end(
        &mut self,
        thread: &mut SchemeThread,
        arguments: usize,
        variable_arity: bool,
    ) -> Managed<ScmPrototype> {
        while self.stack_size > 1 {
            self.pop(1);
            self.emit(Op::Pop);
        }
        self.emit(Op::Return);
        let codeblob = make_blob::<Op>(thread, self.code.len());
        let b = Value::new(codeblob);
        for i in 0..self.code.len() {
            unsafe {
                // write raw opcode bytes
                b.blob_set(i, self.code[i]);
            }
        }

        let local_free_vars = make_blob::<usize>(thread, self.local_free_variable_count);
        let upvals = make_blob::<UpvalLoc>(thread, self.upvalue_count);

        let l = Value::new(local_free_vars);
        let u = Value::new(upvals);
        let mut freevar_i = 0;
        let mut upvalue_i = 0;
        for i in 0..self.free_variables.len() {
            if self.free_variables[i].lexical_level == 0 {
                unsafe {
                    l.blob_set(freevar_i, self.free_variables[i].index);
                    freevar_i += 1;
                }
            } else {
                unreachable!()
            }
        }
        for i in 0..self.free_upvariables.len() {
            let l = UpvalLoc {
                local: self.free_upvariables[i].lexical_level == 1,
                index: self.free_upvariables[i].index as _,
            };
            unsafe {
                u.blob_set(upvalue_i, l);
                upvalue_i += 1;
            }
        }
        let debuginfo = make_blob::<u8>(thread, 0);
        let constants = std::mem::replace(&mut self.constants, Vector::new(&mut thread.mutator));

        let p = thread.mutator.allocate(
            ScmPrototype {
                constants,
                local_free_variables: local_free_vars,
                local_free_variable_count: self.local_free_variable_count as _,
                upvalues: upvals,
                arguments: arguments as _,
                variable_arity,
                code: codeblob,
                debuginfo,
                entry_points: Default::default(),
                locals: self.locals as _,
                name: self.name,
                stack_max: self.stack_max as _,
                n_calls: AtomicUsize::new(0),
                jit_code: AtomicPtr::new(null_mut()),
            },
            comet::gc_base::AllocationSpace::Old,
        );
        if self.dump_bytecode {
            print_bytecode(p);
        }
        p
    }
}

pub fn make_env(
    thread: &mut SchemeThread,
    parent: Value,
    module_name: Option<&str>,
) -> Managed<ScmTable> {
    let mut table = make_table(thread, 4);
    if let Some(module_name) = module_name {
        let mut delegates = make_vector(thread, 2);
        if parent.is_object() {
            delegates.vec.push(&mut thread.mutator, parent);
        }
        let unqualified = thread
            .runtime
            .global_symbol(crate::runtime::Global::UnqualifiedImports);
        table.set(thread, Value::new(unqualified), Value::new(delegates));
        let qualified = thread
            .runtime
            .global_symbol(crate::runtime::Global::QualifiedImports);
        let delegates = make_vector(thread, 0);
        table.set(thread, Value::new(qualified), Value::new(delegates));
        let global = thread
            .runtime
            .global_symbol(crate::runtime::Global::GlobalEnvironment);
        let export_parent = thread
            .runtime
            .global_symbol(crate::runtime::Global::ExportParent);
        let exports_ = thread
            .runtime
            .global_symbol(crate::runtime::Global::Exports);
        let exporting = thread
            .runtime
            .global_symbol(crate::runtime::Global::Exporting);
        let mut exports = make_table(thread, 4);

        exports.set(thread, Value::new(global), Value::encode_bool_value(true));
        exports.set(thread, Value::new(export_parent), Value::new(table));

        table.set(thread, Value::new(exports_), Value::new(exports));

        let name = make_string(thread, module_name);
        let module_name = thread
            .runtime
            .global_symbol(crate::runtime::Global::ModuleName);
        table.set(thread, Value::new(module_name), Value::new(name));

        table.set(thread, Value::new(global), Value::new(true));
        table.set(thread, Value::new(exporting), Value::new(false));
    } else {
        let parent_ = thread.runtime.global_symbol(crate::runtime::Global::Parent);
        table.set(thread, Value::new(parent_), parent);
    }

    table
}

pub fn env_contains(env: Managed<ScmTable>, key: Value) -> bool {
    env.contains(key)
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Lookup {
    Global {
        value: Value,
        module: Value,
    },
    Local {
        index: usize,
        level: usize,
        value: Value,
        up: bool,
    },
}

pub fn env_lookup(
    thread: &mut SchemeThread,
    mut env: Managed<ScmTable>,
    key: Value,
    search_exports: bool,
) -> Option<Lookup> {
    let start_env = env;
    let mut level = 0;
    loop {
        let val = env.get(key);

        if let Some(val) = val {
            if env_globalp(thread, env) {
                let module = if search_exports {
                    loop {
                        if val.symbolp() {
                            let sym = val.downcast::<ScmSymbol>();
                            if sym.module.tablep() {
                                break sym.module;
                            }
                        }
                        let p = thread
                            .runtime
                            .global_symbol(crate::runtime::Global::ExportParent);
                        break env
                            .get(Value::new(p))
                            .unwrap_or_else(|| Value::encode_null_value());
                    }
                } else {
                    if val.symbolp() {
                        let sym = val.downcast::<ScmSymbol>();
                        if sym.module.tablep() {
                            sym.module
                        } else {
                            Value::new(env)
                        }
                    } else {
                        Value::new(env)
                    }
                };

                return Some(Lookup::Global { value: val, module });
            } else {
                let up = Value::new(start_env) != Value::new(env);

                return Some(Lookup::Local {
                    value: val,
                    index: if val.is_int32() {
                        val.get_int32() as _
                    } else {
                        0 // if variable is a macro then we do not store its index in VM Frame
                    },
                    level,
                    up,
                });
            }
        }
        level += 1;

        let parent = thread.runtime.global_symbol(crate::runtime::Global::Parent);
        if env.contains(Value::new(parent)) {
            let penv = env.get(Value::new(parent));
            if let Some(penv) = penv {
                if penv.tablep() {
                    env = penv.downcast();
                    continue;
                }
            }
        }
        break;
    }

    let unqualified = thread
        .runtime
        .global_symbol(crate::runtime::Global::UnqualifiedImports);
    if let Some(modules) = env.get(Value::new(unqualified)) {
        for i in 0..modules.vector_length() {
            let exports = thread
                .runtime
                .global_symbol(crate::runtime::Global::Exports);
            let exports = modules
                .vector_ref(i)
                .table()
                .get(Value::new(exports))
                .unwrap();

            if let Some(lookup) = env_lookup(thread, exports.table(), key, true) {
                return Some(lookup);
            }
        }
    }
    None
}
