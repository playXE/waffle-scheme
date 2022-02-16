use super::opcodes::Opcode;
use crate::compiler::{Lookup, UpvalLoc};
use crate::runtime::{
    convert_module_name, env_define, env_globalp, env_qualify_name, lexpr_to_value, load_module,
    make_blob, make_exception, make_string, make_symbol, make_table, make_vector, module_loaded,
    register_module_,
    value::{Macro, Null, ScmPrototype, Undefined},
};
use crate::{
    compiler::FreeVariableInfo,
    runtime::{
        value::{ScmString, ScmTable, Value},
        SchemeThread,
    },
    Heap, Managed,
};
use comet::api::Trace;
use comet::letroot;
use comet_extra::alloc::hash::HashMap;
use comet_extra::alloc::vector::Vector;
use std::{
    mem::size_of,
    ptr::null_mut,
    sync::atomic::{AtomicPtr, AtomicUsize},
};

pub struct Code {
    list: Vec<Opcode>,
    maxtemp: u8,
    ntemps: u8,
    nlocals: u8,
    error: bool,
    state: [bool; 256],
    skipclear: [bool; 256],
    registers: Vec<u8>,
    context: Vec<Vec<bool>>,
}

impl Code {
    pub fn clear(&mut self) {
        *self = Self::new(0);
    }
    pub fn new(nlocals: usize) -> Self {
        let mut this = Self {
            list: vec![],
            maxtemp: 0,
            ntemps: 0,
            nlocals: nlocals as _,
            error: false,
            state: [false; 256],
            skipclear: [false; 256],
            registers: vec![],
            context: vec![],
        };
        for i in 0..nlocals {
            this.state[i] = true;
        }

        this
    }
    pub fn emit(&mut self, op: Opcode) {
        self.list.push(op);
    }
    pub fn push_context(&mut self) {
        self.context.push(vec![false; 256]);
    }
    pub fn pop_context(&mut self) {
        let ctx = self.context.pop().unwrap();
        for i in 0..256 {
            if ctx[i] {
                self.state[i] = false;
            }
        }
    }

    pub fn register_protect_outside_context(&mut self, nreg: u8) -> bool {
        if nreg < self.nlocals {
            return true;
        }
        if !self.state[nreg as usize] {
            return false;
        }
        let ctx = self.context.last_mut().unwrap();
        ctx[nreg as usize] = false;
        true
    }

    pub fn register_protect_in_context(&mut self, nreg: u8) {
        let ctx = self.context.last_mut().unwrap();
        ctx[nreg as usize] = true;
    }

    pub fn register_new(&mut self) -> Option<u8> {
        for i in 0..256 {
            if !self.state[i] {
                self.state[i] = true;
                return Some(i as u8);
            }
        }
        self.error = true;
        None
    }

    pub fn register_push(&mut self, nreg: u8) -> u8 {
        self.registers.push(nreg);
        if self.is_temp(nreg) {
            self.ntemps += 1;
        }
        nreg
    }
    pub fn first_temp_available(&self) -> Option<u8> {
        for i in 0..256 {
            if !self.state[i] {
                return Some(i as u8);
            }
        }
        None
    }
    pub fn register_push_temp(&mut self) -> Option<u8> {
        let value = self.register_new()?;
        self.registers.push(value);
        if value > self.maxtemp as u8 {
            self.maxtemp = value as _;
            self.ntemps += 1;
        }
        Some(value)
    }

    pub fn register_push_temp_protected(&mut self) -> Option<u8> {
        let val = self.register_push_temp()?;
        self.register_temp_protect(val);
        Some(val)
    }

    pub fn register_clear(&mut self, nreg: u8) {
        if nreg >= self.nlocals {
            self.state[nreg as usize] = false;
        }
    }

    pub fn register_temps_clear(&mut self) {
        for i in self.nlocals..=self.maxtemp {
            if !self.skipclear[i as usize] {
                self.state[i as usize] = false;
            }
        }
    }
    pub fn register_temp_protect(&mut self, nreg: u8) {
        self.skipclear[nreg as usize] = true;
    }
    pub fn register_temp_unprotect(&mut self, nreg: u8) {
        self.skipclear[nreg as usize] = false;
    }
    pub fn register_count(&self) -> usize {
        self.registers.len()
    }

    pub fn register_last(&self) -> Option<u8> {
        self.registers.last().copied()
    }

    pub fn register_set(&mut self, nreg: u8) {
        if nreg >= self.nlocals {
            self.state[nreg as usize] = true;
        }
    }
    pub fn register_pop(&mut self) -> Option<u8> {
        self.register_pop_context_protect(false)
    }
    pub fn register_pop_context_protect(&mut self, protect: bool) -> Option<u8> {
        let value = self.registers.pop()?;
        if protect {
            self.state[value as usize] = true;
        } else if value >= self.nlocals {
            self.state[value as usize] = false;
        }

        if protect && value >= self.nlocals {
            let ctx = self.context.last_mut().unwrap();
            ctx[value as usize] = true;
        }
        Some(value)
    }
    pub fn is_temp(&self, nreg: u8) -> bool {
        nreg >= self.nlocals as u8
    }
}

pub struct Compiler {
    parent: Option<*mut Self>,
    pub code: Code,
    free_variables: Vec<FreeVariableInfo>,
    free_upvariables: Vec<FreeVariableInfo>,
    local_free_variable_count: usize,
    upvalue_count: usize,

    constants: Vector<Value, Heap>,
    closure: bool,
    name: Option<Managed<ScmString>>,
    env: Managed<ScmTable>,
    depth: usize,
    locals: usize,
    dump: bool,
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

impl Compiler {
    pub fn clear(&mut self) {
        self.code.clear();
        self.free_variables.clear();
        self.free_upvariables.clear();
        self.local_free_variable_count = 0;
        self.upvalue_count = 0;

        self.closure = false;
        self.name = None;
        self.constants.clear();
    }
    pub fn new(
        thread: &mut SchemeThread,
        parent: Option<*mut Self>,
        env: Option<Managed<ScmTable>>,
        nlocals: usize,

        depth: usize,
    ) -> Self {
        let constants = Vector::new(&mut thread.mutator);
        Self {
            free_upvariables: vec![],
            dump: thread.runtime.inner().dump_bytecode,
            parent,
            code: Code::new(nlocals),
            free_variables: vec![],
            local_free_variable_count: 0,
            upvalue_count: 0,
            locals: 0,
            constants,
            closure: false,
            name: None,
            env: env.unwrap_or_else(|| thread.runtime.inner().core_module.unwrap()),
            depth,
        }
    }
    pub fn syntax_error(&mut self, thread: &mut SchemeThread, message: impl AsRef<str>) -> Value {
        let tag = thread
            .runtime
            .global_symbol(crate::runtime::Global::ScmCompile);
        let msg = make_string(thread, format!("syntax error: {}", message.as_ref()));
        Value::new(make_exception(thread, tag, msg, Value::new(Null)))
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
    pub fn compile_set(
        &mut self,
        thread: &mut SchemeThread,
        rest: &lexpr::Value,
    ) -> Result<(), Value> {
        let rest = rest.as_cons().unwrap();

        let name = make_symbol(thread, rest.car().as_symbol().unwrap());
        let value = rest.cdr().as_cons().unwrap().car();

        self.compile(thread, value, false)?;
        let r = self.code.register_pop().unwrap();
        if let Some(l) = env_lookup(thread, self.env, Value::new(name), false) {
            self.generate_set(thread, self.env, &l, Value::new(name), r);
        } else {
            panic!("undefined variable")
        }

        Ok(())
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
        let r = self.code.register_pop().unwrap();
        self.generate_set(thread, self.env, &l, Value::new(name), r);
        Ok(())
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
                let r = self.code.register_push_temp().unwrap();
                self.code.emit(Opcode::LoadI(r, x));
            }
            lexpr::Value::Bool(x) => {
                let r = self.code.register_push_temp().unwrap();
                if !*x {
                    self.code.emit(Opcode::LoadF(r));
                } else {
                    self.code.emit(Opcode::LoadT(r));
                }
            }
            lexpr::Value::Number(x) => {
                let r = self.code.register_push_temp().unwrap();
                if let Some(x) = x.as_i64() {
                    if x as i32 as i64 == x {
                        self.code.emit(Opcode::LoadI(r, x as i32));
                    } else {
                        let c = self.new_constant(thread, Value::new(x as f64));
                        self.code.emit(Opcode::LoadK(r, c));
                    }
                } else if let Some(x) = x.as_f64() {
                    let c = self.new_constant(thread, Value::new(x));
                    self.code.emit(Opcode::LoadK(r, c));
                } else {
                    todo!()
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
                            let c = self.new_constant(thread, val);
                            let r = self.code.register_push_temp().unwrap();
                            self.code.emit(Opcode::LoadK(r, c));
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
                            let r = self.code.register_push_temp().unwrap();
                            self.code.emit(Opcode::LoadN(r));
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
                let r = self.code.register_push_temp().unwrap();
                self.code.emit(Opcode::LoadN(r));
            }
            lexpr::Value::String(x) => {
                let string = make_string(thread, x);
                let c = self.new_constant(thread, Value::new(string));
                let r = self.code.register_push_temp().unwrap();
                self.code.emit(Opcode::LoadK(r, c));
            }
            _ => todo!("{:?}", exp),
        }
        Ok(())
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
        let mut args = exp.as_cons().unwrap().cdr();
        self.code.push_context();
        self.compile(thread, exp.as_cons().unwrap().car(), false)?;

        let target_register = self.code.register_pop_context_protect(true).unwrap();

        let mut dest_register = target_register;

        if !self.code.is_temp(dest_register) {
            dest_register = self.code.register_push_temp().unwrap();
        }

        let temp_target_register = self.code.register_push_temp().unwrap();
        self.code
            .emit(Opcode::Move(temp_target_register, target_register));
        let _treg = self.code.register_pop_context_protect(true).unwrap();

        let mut args_r = vec![];
        let mut n = 0;
        let mut j = 0;
        while args.is_cons() {
            n += 1;
            let arg = args.as_cons().unwrap().car();
            self.compile(thread, arg, false)?;
            let mut nreg = self.code.register_pop_context_protect(true).unwrap();
            if nreg != temp_target_register + j + 1 {
                let temp = self.code.register_push_temp().unwrap();
                self.code.emit(Opcode::Move(temp, nreg));
                self.code.register_clear(nreg);
                nreg = self.code.register_pop_context_protect(true).unwrap();
            }
            if nreg != temp_target_register + j + 1 {
                panic!("regalloc for call failed");
            }
            args_r.push(nreg);
            args = args.as_cons().unwrap().cdr();
            j += 1;
        }

        if tail {
            self.code.emit(Opcode::TailApply(temp_target_register, n));
        } else {
            self.code
                .emit(Opcode::Apply(dest_register, temp_target_register, n));
        }

        self.code.register_clear(temp_target_register);
        for arg in args_r {
            self.code.register_clear(arg);
        }
        self.code.register_push(dest_register);
        self.code.register_protect_outside_context(dest_register);
        self.code.pop_context();
        /*while args.is_cons() {
            self.compile(thread, args.as_cons().unwrap().car(), false)?;
            args = args.as_cons().unwrap().cdr();
        }
        let argc = self.stack_size - old_stack_size;
        self.compile(thread, exp.as_cons().unwrap().car(), false)?;

        if tail {
            self.emit(Op::TailApply(argc as _));
            self.dump(&format!("tail-apply {}", argc));
        } else {
            self.emit(Op::Apply(argc as _));
            self.dump(&format!("apply {}", argc));
        }

        self.pop(self.stack_size as usize - old_stack_size as usize);
        self.push(1);
        */
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
        let val = self.code.register_pop().unwrap();
        let merge_register = self.code.register_push_temp().unwrap();
        let jmp1 = self.code.list.len();
        self.code.emit(Opcode::JumpIfFalse(val, 0));

        match exp.as_cons().unwrap().cdr().as_cons() {
            Some(x) => {
                self.compile(thread, x.car(), tail)?;
            }
            None => {
                self.compile(thread, exp.as_cons().unwrap().cdr(), tail)?;
            }
        }
        let r = self.code.register_pop();
        self.code.emit(Opcode::Move(merge_register, r.unwrap()));
        let jmp2 = self.code.list.len();
        self.code.emit(Opcode::Jump(0));
        let lbl1 = self.code.list.len();
        match else_expr {
            Some(val) => {
                self.compile(thread, val, tail)?;
                let r = self.code.register_pop();
                self.code.emit(Opcode::Move(merge_register, r.unwrap()));
            }
            None => {
                let c = self.new_constant(thread, Value::new(Null));

                self.code.emit(Opcode::LoadK(merge_register, c));
            }
        }

        let lbl2 = self.code.list.len();

        self.code.list[jmp1] = Opcode::JumpIfFalse(val, lbl1 as _);
        self.code.list[jmp2] = Opcode::Jump(lbl2 as _);
        Ok(())
    }
    pub fn exporting(&self, thread: &mut SchemeThread) -> bool {
        let exporting = thread
            .runtime
            .global_symbol(crate::runtime::Global::Exporting);
        env_globalp(thread, self.env) && self.env.contains(Value::new(exporting))
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
        let p = thread.runtime.global_symbol(crate::runtime::Global::Parent);
        let mut global = self.env;

        while !env_globalp(thread, global) {
            global = global.get(Value::new(p)).unwrap().table();
        }
        let l = {
            value = Value::new(name);
            Lookup::Global {
                value: Value::new(Undefined),
                module: Value::new(Undefined),
            }
        };

        let exporting = self.exporting(thread);
        env_define(thread, self.env, Value::new(name), value, exporting);
        self.compile(thread, expr, false)?;
        let r = self.code.register_pop().unwrap();
        self.generate_set(thread, self.env, &l, Value::new(name), r);
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
        let x = self.new_constant(thread, proto);
        let r = self.code.register_push_temp().unwrap();
        self.code.emit(Opcode::LoadK(r, x));
        if closure {
            self.code.emit(Opcode::Closure(r, r));
        }
        Ok(())
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

        let stack = thread.mutator.shadow_stack();

        letroot!(
            cc = stack,
            Compiler::new(
                thread,
                Some(self),
                Some(new_env),
                argc as usize,
                self.depth + 1,
            )
        );

        if !name.is_null() {
            cc.name = Some(name.symbol_name());
        }

        cc.compile_begin(thread, rest.as_cons().unwrap().cdr(), true)?;

        let proto = cc.end(thread, argc as _, variable_arity);
        *closure = cc.closure;

        Ok(Value::new(proto))
    }
    pub fn new_constant(&mut self, thread: &mut SchemeThread, constant: Value) -> u16 {
        for i in 0..self.constants.len() {
            if self.constants[i] == constant {
                return i as u16;
            }
        }
        let i = self.constants.len();
        self.constants.push(&mut thread.mutator, constant);
        i as _
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
                let c = self.new_constant(thread, Value::new(tmp));
                let nreg = self.code.register_push_temp().unwrap();
                self.code.emit(Opcode::LoadG(nreg, c));
                Ok(())
            }
            Lookup::Local { index, up, .. } => {
                if !*up {
                    self.code.register_push(*index as _);
                } else {
                    let index = self.register_free_variable(lookup, name);
                    let nreg = self.code.register_push_temp().unwrap();
                    self.code.emit(Opcode::LoadU(nreg, index as _));
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
        r: u8,
    ) {
        match lookup {
            Lookup::Global { .. } => {
                let p = thread.runtime.global_symbol(crate::runtime::Global::Parent);
                let mut global = env;

                while !env_globalp(thread, global) {
                    global = global.get(Value::new(p)).unwrap().table();
                }
                let qualified_name = env_qualify_name(thread, global, name);

                let c = self.new_constant(thread, Value::new(qualified_name));

                self.code.emit(Opcode::StoreG(c, r));
            }
            Lookup::Local { index, up, .. } => {
                if *up {
                    let index = self.register_free_variable(lookup, name);
                    self.code.emit(Opcode::StoreU(index as _, r));
                } else {
                    self.code.emit(Opcode::Move(*index as u8, r));
                }
            }
        }
    }
    pub fn enter_module(
        &mut self,
        thread: &mut SchemeThread,
        internal_name: Value,
    ) -> Result<(), Value> {
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
    pub fn compile_begin(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        tail: bool,
    ) -> Result<(), Value> {
        if exp.is_null() {
            let r = self.code.register_push_temp().unwrap();
            self.code.emit(Opcode::LoadN(r));
            return Ok(());
        }

        match exp.as_cons() {
            Some(cons) => {
                if cons.cdr().is_null() {
                    self.compile(thread, cons.car(), tail)?;
                    Ok(())
                } else {
                    self.compile(thread, cons.car(), false)?;
                    self.code.register_pop().unwrap();
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
    pub fn end(
        &mut self,
        thread: &mut SchemeThread,
        arguments: usize,
        variable_arity: bool,
    ) -> Managed<ScmPrototype> {
        let r = self.code.register_pop();
        match r {
            Some(r) => {
                self.code.emit(Opcode::Return(r));
            }
            None => self.code.emit(Opcode::Return0),
        }
        let codeblob = make_blob::<Opcode>(thread, self.code.list.len());
        let b = Value::new(codeblob);
        for i in 0..self.code.list.len() {
            unsafe {
                // write raw opcode bytes
                b.blob_set(i, self.code.list[i]);
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
        let entry_points = HashMap::new(&mut thread.mutator);
        let proto = thread.mutator.allocate(
            ScmPrototype {
                constants: constants,
                local_free_variables: local_free_vars,
                local_free_variable_count: self.local_free_variable_count as _,
                upvalues: upvals,
                arguments: arguments as _,
                variable_arity,
                code: codeblob,
                entry_points,
                debuginfo,
                locals: self.code.nlocals as _,
                name: self.name,
                stack_max: self.code.ntemps as u16 + self.code.nlocals as u16,
                n_calls: AtomicUsize::new(0),
                jit_code: AtomicPtr::new(null_mut()),
            },
            comet::gc_base::AllocationSpace::Old,
        );

        if self.dump {
            let d = BytecodeDisplay { proto };
            println!("{}", d);
        }

        proto
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
                    let p = thread
                        .runtime
                        .global_symbol(crate::runtime::Global::ExportParent);
                    env.get(Value::new(p))
                        .unwrap_or_else(|| Value::encode_null_value())
                } else {
                    Value::new(env)
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

pub struct BytecodeDisplay {
    proto: Managed<ScmPrototype>,
}
impl std::fmt::Display for BytecodeDisplay {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "bytecode for function '")?;
        match self.proto.name {
            Some(name) => {
                write!(f, "{}'", name.string)?;
            }
            None => {
                write!(f, "<anonymous>'")?;
            }
        }
        writeln!(f, " at {:p}", self.proto)?;
        writeln!(f, " constant pool:")?;
        for (i, constant) in self.proto.constants.iter().enumerate() {
            writeln!(f, "  {}: {}", i, constant)?;
        }

        let code = unsafe {
            std::slice::from_raw_parts::<Opcode>(
                self.proto.code.as_ptr().cast(),
                self.proto.code.len() / size_of::<Opcode>(),
            )
        };
        writeln!(f, " code: ")?;
        for (ip, op) in code.iter().enumerate() {
            write!(f, "  {:04}: ", ip)?;

            let _ = match op {
                &Opcode::Apply(dest, callee, nargs) => {
                    writeln!(f, "apply r{}, r{}, {}", dest, callee, nargs)
                }
                &Opcode::Closure(x, y) => {
                    writeln!(f, "closure r{}, r{}", x, y)
                }
                &Opcode::Jump(x) => {
                    writeln!(f, "jump {}", x)
                }
                &Opcode::JumpIfFalse(x, y) => writeln!(f, "jump_if_false r{}, {}", x, y),
                &Opcode::JumpIfTrue(x, y) => writeln!(f, "jump_if_true r{}, {}", x, y),
                &Opcode::LoadF(x) => writeln!(f, "load.#f r{}", x),
                &Opcode::LoadT(x) => writeln!(f, "load.#t r{}", x),
                &Opcode::LoadN(x) => writeln!(f, "load.null r{}", x),
                &Opcode::LoadG(x, c) => writeln!(f, "load.global r{}, c{}", x, c),
                &Opcode::LoadU(x, i) => writeln!(f, "load.upvalue r{},u{}", x, i),
                Opcode::LoadK(x, c) => writeln!(f, "load.constant r{}, c{}", x, c),
                Opcode::LoadI(x, c) => writeln!(f, "load.int r{}, {}", x, c),
                Opcode::StoreG(x, c) => writeln!(f, "store.global c{}, r{}", x, c),
                Opcode::StoreU(x, i) => writeln!(f, "store.upvalue u{}, r{}", x, i),
                Opcode::TailApply(callee, nargs) => {
                    writeln!(f, "tail.apply r{}, {}", callee, nargs)
                }
                Opcode::Move(x, y) => writeln!(f, "move r{}, r{}", x, y),
                Opcode::Return(x) => writeln!(f, "return r{}", x),
                Opcode::Return0 => writeln!(f, "return undef"),
            }?;
        }
        Ok(())
    }
}
