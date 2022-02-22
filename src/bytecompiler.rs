use std::{
    ptr::null_mut,
    sync::atomic::{AtomicPtr, AtomicUsize},
};

use comet::{
    api::{Trace, Visitor},
    letroot,
};
use comet_extra::alloc::vector::Vector;

use crate::{
    compiler::{env_lookup, make_env, FreeVariableInfo, Lookup, Op, UpvalLoc},
    runtime::{
        convert_module_name, env_define, env_globalp, env_qualify_name, lexpr_to_value,
        load_module, make_blob, make_exception, make_string, make_symbol, module_loaded,
        register_module_,
        value::{
            print_bytecode, Macro, Null, ScmPrototype, ScmString, ScmSymbol, ScmTable, Undefined,
            Value,
        },
        value_to_lexpr,
        vm::apply,
        SchemeThread,
    },
    Heap, Managed,
};

pub struct ByteCompiler {
    parent: Option<*mut ByteCompiler>,
    free_variables: Vec<FreeVariableInfo>,
    free_upvariables: Vec<FreeVariableInfo>,
    local_free_variable_count: usize,
    upvalue_count: usize,
    nlocals: u16,
    pub code: Vec<Op>,
    stack: usize,
    constants: Vector<Value, Heap>,
    stack_max: usize,
    closure: bool,
    name: Option<Managed<ScmString>>,
    pub env: Managed<ScmTable>,
    depth: usize,
    dump_bytecode: bool,
}

unsafe impl Trace for ByteCompiler {
    fn trace(&mut self, vis: &mut dyn Visitor) {
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

impl ByteCompiler {
    fn push(&mut self, n: usize) {
        self.stack += n;
        if self.stack > self.stack_max {
            self.stack_max = self.stack;
        }
    }
    pub fn pop_(&mut self) {
        self.code.push(Op::Pop);
        self.pop(1);
    }
    pub fn pop(&mut self, n: usize) {
        self.stack = self
            .stack
            .checked_sub(n)
            .unwrap_or_else(|| panic!("stack underflow {} - {}", self.stack, n));
    }

    pub fn variable_set(&mut self, thread: &mut SchemeThread, name: Managed<ScmSymbol>) -> bool {
        if let Some(l) = env_lookup(thread, self.env, Value::new(name), false) {
            self.generate_set(thread, self.env, &l, Value::new(name));
            true
        } else {
            false
        }
    }

    pub fn variabe_ref(&mut self, thread: &mut SchemeThread, name: Managed<ScmSymbol>) -> bool {
        let lookup = env_lookup(thread, self.env, Value::new(name), false);
        if let Some(lookup) = lookup {
            self.generate_ref(thread, &lookup, Value::new(name));
            true
        } else {
            false
        }
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

    pub fn generate_ref(&mut self, thread: &mut SchemeThread, lookup: &Lookup, name: Value) {
        match lookup {
            Lookup::Global { module, .. } => {
                let name = env_qualify_name(thread, module.table(), name);
                self.global_get(thread, name);
            }
            Lookup::Local { index, up, .. } => {
                if !*up {
                    self.local_get(*index as _);
                } else {
                    let index = self.register_free_variable(lookup, name);
                    self.upvalue_get(index as _);
                }
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

                self.global_set(thread, qualified_name)
            }
            Lookup::Local { index, up, .. } => {
                if *up {
                    let index = self.register_free_variable(lookup, name);
                    self.upvalue_set(index as _);
                } else {
                    self.local_set(*index as _);
                }
            }
        }
    }

    pub fn set_local(&mut self, l: Lookup) {
        match l {
            Lookup::Local { index, up, .. } => {
                if up {
                    let index = self.register_free_variable(&l, Value::new(index as i32));
                    self.upvalue_set(index as _);
                } else {
                    self.local_set(index as _);
                }
            }
            _ => panic!("trying to set non local variable"),
        }
    }

    pub fn get_local(&mut self, l: Lookup) {
        match l {
            Lookup::Local { index, up, .. } => {
                if !up {
                    self.local_get(index as _);
                } else {
                    let index = self.register_free_variable(&l, Value::new(index as i32));
                    self.upvalue_get(index as _);
                }
            }
            _ => panic!("trying to get non local variable"),
        }
    }

    pub fn global_set(&mut self, thread: &mut SchemeThread, name: Managed<ScmSymbol>) {
        self.constant(thread, Value::new(name));
        self.code.push(Op::GlobalSet);
        self.pop(2);
    }

    pub fn global_get(&mut self, thread: &mut SchemeThread, name: Managed<ScmSymbol>) {
        self.constant(thread, Value::new(name));
        self.code.push(Op::GlobalGet);
    }
    pub fn local_get(&mut self, i: u16) {
        self.code.push(Op::LocalGet(i));
        self.push(1);
    }

    pub fn local_set(&mut self, i: u16) {
        self.pop(1);
        self.code.push(Op::LocalSet(i));
    }
    pub fn upvalue_get(&mut self, i: u16) {
        self.code.push(Op::UpvalueGet(i));
        self.push(1);
    }

    pub fn upvalue_set(&mut self, i: u16) {
        self.pop(1);
        self.code.push(Op::UpvalueSet(i));
    }

    pub fn define(&mut self, thread: &mut SchemeThread, name: Managed<ScmTable>) -> Lookup {
        let value;
        let l = if env_globalp(thread, self.env) {
            value = Value::new(name);
            Lookup::Global {
                value: Value::new(Undefined),
                module: Value::new(Undefined),
            }
        } else {
            value = Value::new(self.nlocals as i32);
            self.nlocals += 1;
            Lookup::Local {
                index: self.nlocals as usize - 1,
                level: 0,
                up: false,
                value: Value::new(self.nlocals as i32 - 1),
            }
        };
        let exporting = self.exporting(thread);
        env_define(thread, self.env, Value::new(name), value, exporting);

        self.generate_set(thread, self.env, &l, Value::new(name));

        l
    }
    pub fn exporting(&self, thread: &mut SchemeThread) -> bool {
        let exporting = thread
            .runtime
            .global_symbol(crate::runtime::Global::Exporting);
        env_globalp(thread, self.env)
            && self
                .env
                .get(Value::new(exporting))
                .map(|x| x.to_boolean())
                .unwrap_or_else(|| false)
    }
    pub fn new_local(&mut self) -> Lookup {
        let l = self.nlocals;
        self.nlocals += 1;
        Lookup::Local {
            index: l as _,
            level: 0,
            up: false,
            value: Value::new(l as i32),
        }
    }

    pub fn apply(&mut self, nargs: u16) {
        self.pop(nargs as _);
        self.pop(1);
        self.code.push(Op::Apply(nargs));
        self.push(1);
    }

    pub fn tail_apply(&mut self, nargs: u16) {
        self.pop(nargs as _);
        self.pop(1);
        self.code.push(Op::TailApply(nargs));
    }

    pub fn ret(&mut self) {
        self.pop(1);
        self.code.push(Op::Return);
    }

    pub fn int32(&mut self, imm: i32) {
        self.code.push(Op::PushInt(imm));
        self.push(1);
    }

    pub fn boolean(&mut self, x: bool) {
        if x {
            self.code.push(Op::PushTrue);
        } else {
            self.code.push(Op::PushFalse);
        }
        self.push(1);
    }

    pub fn null(&mut self) {
        self.code.push(Op::PushNull);
        self.push(1);
    }

    pub fn constant(&mut self, thread: &mut SchemeThread, value: Value) {
        for (i, c) in self.constants.iter().copied().enumerate() {
            if c == value {
                self.code.push(Op::PushConstant(i as _));
                self.push(1);
                return;
            }
        }
        let i = self.constants.len();
        self.constants.push(&mut thread.mutator, value);
        self.code.push(Op::PushConstant(i as _));
        self.push(1);
    }
    pub fn loophint(&mut self) {
        self.code.push(Op::LoopHint);
    }

    pub fn enter_parent<E>(
        &mut self,
        thread: &mut SchemeThread,
        argument_count: usize,
        variable_arity: bool,
        nlocals: usize,
        is_closure: &mut bool,
        mut closure: impl FnMut(&mut SchemeThread, &mut ByteCompiler) -> Result<(), E>,
    ) -> Result<Managed<ScmPrototype>, E> {
        let new_env = make_env(thread, Value::new(self.env), None);
        let mut subcompiler = Self::new(thread, Some(self), Some(new_env), self.depth + 1);
        subcompiler.nlocals += argument_count as u16 + nlocals as u16;
        let stack = thread.mutator.shadow_stack();
        letroot!(subcompiler = stack, subcompiler);

        match closure(thread, &mut subcompiler) {
            Ok(()) => {
                let proto = subcompiler.end(thread, argument_count, variable_arity);
                *is_closure = self.closure;
                Ok(proto)
            }
            Err(e) => Err(e),
        }
    }

    pub fn clear(&mut self) {
        self.code.clear();
        self.free_variables.clear();
        self.free_upvariables.clear();
        self.local_free_variable_count = 0;
        self.upvalue_count = 0;
        self.stack_max = 0;
        self.stack = 0;
        self.nlocals = 0;
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
            stack: 0,
            nlocals: 0,
            constants,
            closure: false,
            name: None,
            env: env.unwrap_or_else(|| thread.runtime.inner().core_module.unwrap()),
            depth,
        }
    }

    pub fn end(
        &mut self,
        thread: &mut SchemeThread,
        arguments: usize,
        variable_arity: bool,
    ) -> Managed<ScmPrototype> {
        while self.stack > 1 {
            self.pop(1);
            self.code.push(Op::Pop);
        }
        if self.stack == 0 {
            self.code.push(Op::PushNull);
        } else {
            self.pop(1);
        }
        self.code.push(Op::Return);

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
                locals: self.nlocals as _,
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
    pub fn while_loop<E, F, F2>(
        &mut self,
        thread: &mut SchemeThread,
        mut cond: F,
        mut body: F2,
    ) -> Result<(), E>
    where
        F: FnMut(&mut SchemeThread, &mut Self) -> Result<(), E>,
        F2: FnMut(&mut SchemeThread, &mut Self) -> Result<(), E>,
    {
        self.null();
        let loop_start = self.code.len();
        cond(thread, self)?;

        let patch = self.code.len();
        self.code.push(Op::JumpIfFalse(0));

        self.pop_();
        let old_stack = self.stack;
        body(thread, self)?;
        if self.stack - old_stack == 0 {
            self.null();
        }
        self.pop(self.stack - old_stack);

        self.code.push(Op::LoopHint);
        self.code.push(Op::Jump(loop_start as _));
        let end = self.code.len();
        self.code[patch] = Op::JumpIfFalse(end as _);

        Ok(())
    }
    pub fn if_<F, F2, E>(
        &mut self,
        thread: &mut SchemeThread,
        mut if_true: F,
        mut if_false: F2,
    ) -> Result<(), E>
    where
        F: FnMut(&mut SchemeThread, &mut Self) -> Result<(), E>,
        F2: FnMut(&mut SchemeThread, &mut Self) -> Result<(), E>,
    {
        self.pop(1);
        let patch_1 = self.code.len();
        self.code.push(Op::JumpIfFalse(0));
        let old_stack = self.stack;
        if_true(thread, self)?;
        if self.stack - old_stack == 0 {
            self.null();
        }
        self.pop(self.stack - old_stack);
        let patch_2 = self.code.len();
        self.code.push(Op::Jump(0));

        let if_false_ip = self.code.len();
        if_false(thread, self)?;

        if self.stack - old_stack == 0 {
            self.null();
        }
        self.pop(self.stack - old_stack);
        let end_ip = self.code.len();
        self.code[patch_1] = Op::JumpIfFalse(if_false_ip as _);
        self.code[patch_2] = Op::Jump(end_ip as _);
        self.push(1);
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
        apply(thread, Value::new(p.p), &exp)
    }

    pub fn macro_expand_full(
        &mut self,
        thread: &mut SchemeThread,
        p: Value,
        exp: &lexpr::Value,
    ) -> Result<lexpr::Value, Value> {
        let expanded = self.macro_expand_1_step(thread, p, exp)?;

        let mut expanded = value_to_lexpr(thread, expanded);

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
        let old_stack_size = self.stack;
        let mut args = exp.as_cons().unwrap().cdr();
        while args.is_cons() {
            self.compile(thread, args.as_cons().unwrap().car(), false)?;
            args = args.as_cons().unwrap().cdr();
        }
        let argc = self.stack - old_stack_size;
        if tail {
            self.tail_apply(argc as _);
        } else {
            self.apply(argc as _)
        }
        Ok(())
    }

    pub fn compile(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        tail: bool,
    ) -> Result<(), Value> {
        Ok(())
    }

    pub fn expect_symbol<'a>(
        &mut self,
        thread: &mut SchemeThread,
        exp: &'a lexpr::Value,
    ) -> Result<&'a str, Value> {
        exp.as_symbol().ok_or_else(|| {
            self.syntax_error(thread, format!("symbol expected but `{}` found", exp))
        })
    }

    pub fn expect_cons<'a>(
        &mut self,
        thread: &mut SchemeThread,
        exp: &'a lexpr::Value,
    ) -> Result<&'a lexpr::Cons, Value> {
        exp.as_cons()
            .ok_or_else(|| self.syntax_error(thread, format!("cons expected but `{}` found", exp)))
    }
    pub fn syntax_error(&mut self, thread: &mut SchemeThread, message: impl AsRef<str>) -> Value {
        let tag = thread
            .runtime
            .global_symbol(crate::runtime::Global::ScmCompile);
        let msg = make_string(thread, format!("syntax error: {}", message.as_ref()));
        Value::new(make_exception(thread, tag, msg, Value::new(Null)))
    }

    pub fn compute_globals_in_begin(
        &mut self,
        thread: &mut SchemeThread,
        exp: &mut lexpr::Value,
    ) -> Result<(), Value> {
        if exp.is_null() {
            return Ok(());
        }

        match exp.as_cons_mut() {
            Some(cons) => {
                if cons.cdr().is_null() {
                    self.compute_globals(thread, cons.car_mut())?;
                    Ok(())
                } else {
                    self.compute_globals(thread, cons.car_mut())?;

                    self.compute_globals_in_begin(thread, cons.cdr_mut())
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
    pub fn compute_globals(
        &mut self,
        thread: &mut SchemeThread,
        exp: &mut lexpr::Value,
    ) -> Result<bool, Value> {
        match exp {
            lexpr::Value::Cons(pair) => {
                match pair.car() {
                    lexpr::Value::Symbol(proc) => {
                        match &**proc {
                            "define" => {
                                let rest = self.expect_cons(thread, pair.cdr())?;
                                let name = if let Some(name) = rest.car().as_symbol() {
                                    let name = make_symbol(thread, name);
                                    name
                                } else if let Some(pair) = rest.car().as_cons() {
                                    let name = self.expect_symbol(thread, pair.car())?;
                                    let name = make_symbol(thread, name);
                                    name
                                } else {
                                    return Err(self
                                        .syntax_error(thread, "malformed define: expected name"));
                                };

                                let exporting = self.exporting(thread);
                                env_define(
                                    thread,
                                    self.env,
                                    Value::new(name),
                                    Value::new(name),
                                    exporting,
                                );
                                Ok(true)
                            }
                            "defmacro" => {
                                let rest = self.expect_cons(thread, pair.cdr())?;
                                let name = if let Some(name) = rest.car().as_symbol() {
                                    make_symbol(thread, name)
                                } else {
                                    return Err(self.syntax_error(
                                thread,
                                format!("(defmacro <name> <args> <body>) expected but found `{}`", pair.cdr())));
                                };
                                // will actually compile macro in the next pass.
                                let exporting = self.exporting(thread);
                                env_define(
                                    thread,
                                    self.env,
                                    Value::new(name),
                                    Value::new(name),
                                    exporting,
                                );
                                Ok(true)
                            }

                            "begin" => {
                                self.compute_globals_in_begin(thread, pair.cdr_mut())?;
                                Ok(true)
                            }
                            "`" => {
                                let value = lexpr::Value::Cons(lexpr::Cons::new(
                                    lexpr::Value::Symbol("quasiquote".to_string().into_boxed_str()),
                                    pair.cdr().clone(),
                                ));
                                *exp = value;

                                //self.compile(thread, &value, tail)?;
                                return Ok(true);
                            }
                            ",@" => {
                                let value = lexpr::Value::Cons(lexpr::Cons::new(
                                    lexpr::Value::Symbol(
                                        "unquote-splicing".to_string().into_boxed_str(),
                                    ),
                                    pair.cdr().clone(),
                                ));
                                *exp = value;
                                //self.compile(thread, &value, tail)?;
                                return Ok(true);
                            }
                            "," => {
                                let value = lexpr::Value::Cons(lexpr::Cons::new(
                                    lexpr::Value::Symbol("unquote".to_string().into_boxed_str()),
                                    pair.cdr().clone(),
                                ));

                                *exp = value;
                                return Ok(true);
                            }
                            "module" => {
                                let name = convert_module_name(thread, pair.cdr())?;
                                self.enter_module(thread, name)?;
                                return Ok(false);
                            }

                            "export" => {
                                self.compile_export(thread, pair.cdr())?;
                                return Ok(false);
                            }
                            "import" => {
                                self.import(thread, pair.cdr())?;
                                return Ok(false);
                            }
                            _ => return Ok(true),
                        }
                    }
                    _ => return Ok(true),
                }
            }
            // no global symbol possible
            _ => return Ok(true),
        }
    }

    pub fn compile_code<'a, R>(
        &mut self,
        thread: &mut SchemeThread,
        mut parser: lexpr::Parser<R>,
    ) -> Result<(), Value>
    where
        R: lexpr::parse::Read<'a>,
    {
        // 1) Read s-expressions, resolve module exports/imports, create global symbols for top-level `define` and `defmacro`.
        let mut to_be_compiled = vec![];
        for expression in parser.datum_iter() {
            match expression {
                Ok(expression) => {
                    let mut value = expression.value().clone();
                    match self.compute_globals(thread, &mut value) {
                        Ok(retain) => {
                            if retain {
                                to_be_compiled.push(value);
                            }
                        }
                        Err(err) => {
                            return Err(err);
                        }
                    }
                }
                Err(err) => {
                    return Err(self.syntax_error(thread, format!("failed to read code: {}", err)))
                }
            }
        }

        // 2) Compile expressions from to_be_compiled vector
        // in 2) we walk all expressions, compile them and at the same time expand macros.
        // I could try to make macro expansion pass but it is too complex for my brain so we just expand them
        // as we compile code
        // TBD

        Ok(())
    }
}
