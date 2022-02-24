use std::{
    ptr::null_mut,
    sync::atomic::{AtomicPtr, AtomicUsize},
};

use comet::{
    api::{Collectable, Finalize, Trace, Visitor},
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct State {
    val: bool,
    more: bool,
}
impl State {
    pub const fn is_unused(&self) -> bool {
        !self.val
    }
    pub const fn is_final(&self) -> bool {
        !self.more
    }

    pub const USED_FINAL: Self = Self {
        val: true,
        more: false,
    };
    pub const USED_NON_FINAL: Self = Self {
        val: true,
        more: true,
    };
    pub const NOT_USED_NON_FINAL: Self = Self {
        val: false,
        more: true,
    };
}

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
    pub fn pop_if_possible(&mut self) {
        if self.stack != 0 {
            self.pop_();
        }
    }
    pub fn pop(&mut self, n: usize) {
        self.stack = self
            .stack
            .checked_sub(n)
            .unwrap_or_else(|| panic!("stack underflow {} - {}", self.stack, n));
    }

    pub fn variable_set(&mut self, thread: &mut SchemeThread, name: Managed<ScmSymbol>) -> bool {
        if let Some(l) = env_lookup(thread, self.env, Value::new(name), false) {
            self.generate_set(thread, self.env, &l, Value::new(name), None);
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
        comptime_set: Option<Value>,
    ) {
        match lookup {
            Lookup::Global { .. } => {
                let p = thread.runtime.global_symbol(crate::runtime::Global::Parent);
                let mut global = env;

                while !env_globalp(thread, global) {
                    global = global.get(Value::new(p)).unwrap().table();
                }
                let mut qualified_name = env_qualify_name(thread, global, name);

                if let Some(val) = comptime_set {
                    qualified_name.value = val;
                } else {
                    self.global_set(thread, qualified_name)
                }
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

        self.generate_set(thread, self.env, &l, Value::new(name), None);

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
        new_env: Managed<ScmTable>,
        mut closure: impl FnMut(&mut SchemeThread, &mut ByteCompiler) -> Result<(), E>,
    ) -> Result<Managed<ScmPrototype>, E> {
        let mut subcompiler = Self::new(thread, Some(self), Some(new_env), self.depth + 1);
        subcompiler.nlocals += argument_count as u16 + nlocals as u16;
        let stack = thread.mutator.shadow_stack();
        letroot!(subcompiler = stack, subcompiler);

        match closure(thread, &mut subcompiler) {
            Ok(()) => {
                *is_closure = subcompiler.closure;
                let proto = subcompiler.end(thread, argument_count, variable_arity);

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
        println!("=> {}", expanded);
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
                                let value = if value.symbolp() {
                                    let sym = value.downcast::<ScmSymbol>();
                                    sym.value
                                } else {
                                    value
                                };
                                if value.is_cell::<Macro>() {
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

    fn unify_import(&mut self, thread: &mut SchemeThread, name: Value) -> Managed<ScmSymbol> {
        let unqualified = thread
            .runtime
            .global_symbol(crate::runtime::Global::UnqualifiedImports);
        let exports = thread
            .runtime
            .global_symbol(crate::runtime::Global::Exports);
        let env = self.env.get(Value::new(unqualified)).unwrap();
        for i in 0..env.vector_length() {
            let module = env.vector_ref(i);
            let exports = module.table().get(Value::new(exports)).unwrap();
            if let Some(sym) = exports.table().get(name) {
                return sym.downcast();
            }
        }
        let name = env_qualify_name(thread, self.env, name);

        name
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
                let qualified = self.unify_import(thread, Value::new(sym));

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

        st: State,
    ) -> Result<(), Value> {
        let old_stack_size = self.stack;
        let exp = self.expect_cons(thread, exp)?;
        let mut args = exp.cdr();
        while args.is_cons() {
            self.compile(thread, args.as_cons().unwrap().car(), State::USED_NON_FINAL)?;
            args = args.as_cons().unwrap().cdr();
        }
        let argc = self.stack - old_stack_size;
        self.compile(thread, exp.car(), State::USED_NON_FINAL)?;
        if st.is_final() {
            self.tail_apply(argc as _);
        } else {
            self.apply(argc as _);
            if st.is_unused() {
                self.pop_();
            }
        }
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

    pub fn compile(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,

        st: State,
    ) -> Result<(), Value> {
        match exp {
            lexpr::Value::Bool(x) => {
                if !st.is_unused() {
                    self.boolean(*x);
                }
                Ok(())
            }
            lexpr::Value::Char(x) => {
                if !st.is_unused() {
                    self.int32(*x as i32);
                }
                Ok(())
            }
            lexpr::Value::Bytes(bytes) => {
                if !st.is_unused() {
                    let mut blob = make_blob::<u8>(thread, bytes.len());
                    unsafe {
                        std::ptr::copy_nonoverlapping(
                            bytes.as_ptr(),
                            blob.as_mut_ptr(),
                            bytes.len(),
                        );
                    }
                    self.constant(thread, Value::new(blob));
                }
                Ok(())
            }
            lexpr::Value::Vector(values) => {
                if !st.is_unused() {
                    let sym = make_symbol(thread, "#waffle#core#vector");

                    for value in values.iter() {
                        self.compile(thread, value, State::USED_NON_FINAL)?;
                    }
                    self.constant(thread, Value::new(sym));
                    if st.is_final() {
                        self.tail_apply(values.len() as _)
                    } else {
                        self.apply(values.len() as u16)
                    }
                }
                Ok(())
            }
            lexpr::Value::Nil | lexpr::Value::Null => {
                if !st.is_unused() {
                    self.null();
                }
                Ok(())
            }
            lexpr::Value::Number(number) => {
                if !st.is_unused() {
                    if let Some(i) = number.as_i64() {
                        if i as i32 as i64 == i {
                            self.int32(i as _);
                        } else {
                            self.constant(thread, Value::new(i as f64));
                        }
                    } else if let Some(f) = number.as_f64() {
                        self.constant(thread, Value::new(f));
                    } else {
                        todo!()
                    }
                }
                Ok(())
            }
            lexpr::Value::Symbol(symbol_) => {
                if !st.is_unused() {
                    let symbol = make_symbol(thread, symbol_);
                    if !self.variabe_ref(thread, symbol) {
                        return Err(
                            self.syntax_error(thread, format!("variable `{}` not found", symbol_,))
                        );
                    }
                }
                Ok(())
            }

            lexpr::Value::Cons(pair) => {
                let first = pair.car();
                let rest = pair.cdr();
                match first {
                    lexpr::Value::Symbol(name) => match &**name {
                        "set!" => {
                            self.compile_set(thread, rest)?;
                            if !st.is_unused() {
                                self.null();
                            }
                            return Ok(());
                        }

                        "define" => {
                            self.compile_define(thread, exp, rest)?;
                            if !st.is_unused() {
                                self.null();
                            }
                            return Ok(());
                        }
                        "export" => {
                            self.compile_export(thread, pair.cdr())?;
                            return Ok(());
                        }
                        "if" => return self.compile_if(thread, rest, st),
                        "begin" => return self.compile_begin(thread, rest, st),
                        "define-macro" => {
                            let rest = self.expect_cons(thread, rest)?;
                            let name = rest.car();
                            let name = if let lexpr::Value::Symbol(x) = name {
                                make_symbol(thread, x)
                            } else {
                                return Err(self.syntax_error(
                                    thread,
                                    &format!("expected symbol in defmacro but found {:?}", name),
                                ));
                            };
                            let body = rest.cdr();
                            self.compile_macro(thread, Value::new(name), body)?;
                            if !st.is_unused() {
                                self.null();
                            }
                            return Ok(());
                        }
                        "define-syntax" => {
                            self.compile_syntax(thread, exp)?;
                            if !st.is_unused() {
                                self.null();
                            }

                            return Ok(());
                        }
                        "quote" | "'" => {
                            if !st.is_unused() {
                                let rest = self.expect_cons(thread, pair.cdr())?;
                                let value = lexpr_to_value(thread, rest.car());
                                self.constant(thread, value)
                            }
                            return Ok(());
                        }
                        "lambda" => {
                            if !st.is_unused() {
                                let lambda = self.expect_cons(thread, rest)?;
                                let args = lambda.car();
                                let body = lambda.cdr();
                                let mut closure = false;
                                let f = self.generate_lambda(
                                    thread,
                                    Value::new(Null),
                                    args,
                                    body,
                                    &mut closure,
                                )?;
                                self.constant(thread, Value::new(f));

                                if closure {
                                    self.code.push(Op::CloseOver);
                                }
                            }
                            return Ok(());
                        }
                        x => {
                            let sym = make_symbol(thread, x);
                            let x = env_lookup(thread, self.env, Value::new(sym), false);
                            if let Some(Lookup::Global { value, .. }) = x {
                                let value = if value.symbolp() {
                                    let sym = value.downcast::<ScmSymbol>();
                                    sym.value
                                } else {
                                    value
                                };
                                if value.is_cell::<Macro>() {
                                    let expanded = self.macro_expand_full(thread, value, rest)?;
                                    self.compile(thread, &expanded, st)?;
                                    return Ok(());
                                } else if value.is_cell::<Transform>() {
                                    let expansion =
                                        value.downcast::<Transform>().transform(thread, exp)?;
                                    println!("=> {}", expansion);
                                    self.compile(thread, &expansion, st)?;
                                    return Ok(());
                                }
                            }
                        }
                    },
                    _ => (),
                }

                self.compile_apply(thread, exp, st)
            }
            lexpr::Value::String(x) => {
                if !st.is_unused() {
                    let str = make_string(thread, x);
                    self.constant(thread, Value::new(str));
                }
                Ok(())
            }
            _ => todo!(),
        }
    }

    pub fn compile_if(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        st: State,
    ) -> Result<(), Value> {
        let exp = self.expect_cons(thread, exp)?;
        let cond = exp.car();
        let then_and_else = self.expect_cons(thread, exp.cdr())?;
        let else_ = self.expect_cons(thread, then_and_else.cdr())?.car();
        self.compile(thread, cond, State::USED_NON_FINAL)?;
        self.if_(
            thread,
            |thread, cc| cc.compile(thread, then_and_else.car(), st),
            |thread, cc| cc.compile(thread, else_, st),
        )
    }

    pub fn compile_define(
        &mut self,
        thread: &mut SchemeThread,
        original: &lexpr::Value,
        rest: &lexpr::Value,
    ) -> Result<(), Value> {
        let rest = self.expect_cons(thread, rest)?;
        let value = rest.cdr();
        let name;
        match rest.car() {
            // (define (name arg0 arg1 arg2) body)
            lexpr::Value::Cons(name_and_args) => {
                let name_ = self.expect_symbol(thread, name_and_args.car())?;
                name = make_symbol(thread, name_);
                let args = name_and_args.cdr();
                let body = value;
                let mut closure = false;
                let lambda =
                    self.generate_lambda(thread, Value::new(name), args, body, &mut closure)?;
                if env_globalp(thread, self.env) {
                    assert!(!closure, "closure cannot be created at top-level");
                    let l = Lookup::Global {
                        value: Value::new(Undefined),
                        module: Value::new(Undefined),
                    };
                    let exporting = self.exporting(thread);
                    env_define(
                        thread,
                        self.env,
                        Value::new(name),
                        Value::new(name),
                        exporting,
                    );
                    self.generate_set(
                        thread,
                        self.env,
                        &l,
                        Value::new(name),
                        Some(Value::new(lambda)),
                    );
                } else {
                    self.constant(thread, Value::new(lambda));
                    self.code.push(Op::CloseOver);
                    self.nlocals += 1;
                    let l = Lookup::Local {
                        index: self.nlocals as usize - 1,
                        level: 0,
                        up: false,
                        value: Value::new(self.nlocals as i32 - 1),
                    };
                    env_define(
                        thread,
                        self.env,
                        Value::new(name),
                        Value::new(self.nlocals as i32 - 1),
                        false,
                    );
                    self.generate_set(thread, self.env, &l, Value::new(name), None);
                }
                return Ok(());
            }
            lexpr::Value::Symbol(name_) => {
                name = make_symbol(thread, name_);

                match rest.cdr() {
                    lexpr::Value::Cons(pair) => match pair.car() {
                        lexpr::Value::Cons(pair) => match pair.car() {
                            lexpr::Value::Symbol(x) => match &**x {
                                "lambda" => {
                                    let args_and_body = self.expect_cons(thread, pair.cdr())?;
                                    let args = args_and_body.car();
                                    let body = args_and_body.cdr();
                                    let mut closure = false;
                                    let lambda = self.generate_lambda(
                                        thread,
                                        Value::new(name),
                                        args,
                                        body,
                                        &mut closure,
                                    )?;
                                    if env_globalp(thread, self.env) {
                                        assert!(!closure, "closure cannot be created at top-level");
                                        let l = Lookup::Global {
                                            value: Value::new(Undefined),
                                            module: Value::new(Undefined),
                                        };
                                        let exporting = self.exporting(thread);
                                        env_define(
                                            thread,
                                            self.env,
                                            Value::new(name),
                                            Value::new(name),
                                            exporting,
                                        );
                                        self.generate_set(
                                            thread,
                                            self.env,
                                            &l,
                                            Value::new(name),
                                            Some(Value::new(lambda)),
                                        );
                                    } else {
                                        self.constant(thread, Value::new(lambda));
                                        self.code.push(Op::CloseOver);
                                        self.nlocals += 1;
                                        let l = Lookup::Local {
                                            index: self.nlocals as usize - 1,
                                            level: 0,
                                            up: false,
                                            value: Value::new(self.nlocals as i32 - 1),
                                        };
                                        env_define(
                                            thread,
                                            self.env,
                                            Value::new(name),
                                            Value::new(self.nlocals as i32 - 1),
                                            false,
                                        );
                                        self.generate_set(
                                            thread,
                                            self.env,
                                            &l,
                                            Value::new(name),
                                            None,
                                        );
                                    }
                                    return Ok(());
                                }
                                _ => (),
                            },
                            _ => (),
                        },
                        _ => (),
                    },
                    _ => (),
                };
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
                let rest = self.expect_cons(thread, rest.cdr())?;
                self.compile(thread, rest.car(), State::USED_NON_FINAL)?;
                let exporting = self.exporting(thread);
                env_define(thread, self.env, Value::new(name), value, exporting);
                self.generate_set(thread, self.env, &l, Value::new(name), None);
                Ok(())
            }

            _ => {
                return Err(self.syntax_error(
                    thread,
                    format!("failed to match any pattern in form {}", original),
                ))
            }
        }
    }
    pub fn generate_lambda(
        &mut self,
        thread: &mut SchemeThread,
        name: Value,
        mut args: &lexpr::Value,
        body: &lexpr::Value,
        closure: &mut bool,
    ) -> Result<Managed<ScmPrototype>, Value> {
        let new_env = make_env(thread, Value::new(self.env), None);
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
        self.enter_parent(
            thread,
            argc as _,
            variable_arity,
            0,
            closure,
            new_env,
            |thread, cc| {
                if !name.is_null() {
                    cc.name = Some(name.symbol_name());
                }

                cc.compile_begin(thread, body, State::USED_FINAL)?;
                cc.code.push(Op::Return);

                Ok(())
            },
        )
    }
    pub fn compile_begin(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        st: State,
    ) -> Result<(), Value> {
        if exp.is_null() {
            if !st.is_unused() {
                self.null();
            }
            return Ok(());
        }

        match exp.as_cons() {
            Some(cons) => {
                if cons.cdr().is_null() {
                    self.compile(thread, cons.car(), st)?;
                    Ok(())
                } else {
                    self.compile(thread, cons.car(), State::NOT_USED_NON_FINAL)?;

                    self.compile_begin(thread, cons.cdr(), st)
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
    pub fn compile_syntax(
        &mut self,
        thread: &mut SchemeThread,
        expr: &lexpr::Value,
    ) -> Result<(), Value> {
        let transform = Transform::try_new(thread, expr)?;
        let symbol = transform.keyword().clone();
        let transform = thread
            .mutator
            .allocate(transform, comet::gc_base::AllocationSpace::New);
        let mut env = self.env;
        let parent = thread.runtime.global_symbol(crate::runtime::Global::Parent);
        while !env_globalp(thread, env) {
            env = env.get(Value::new(parent)).unwrap().table();
        }
        let name = make_symbol(thread, symbol.as_symbol().unwrap());
        let mut qualified_name = env_qualify_name(thread, env, Value::new(name));

        let exporting = self.exporting(thread);

        env_define(
            thread,
            env,
            Value::new(name),
            Value::new(transform),
            exporting,
        );
        env_define(
            thread,
            env,
            Value::new(qualified_name),
            Value::new(transform),
            exporting,
        );
        qualified_name.value = Value::new(transform);
        Ok(())
    }
    pub fn compile_macro(
        &mut self,
        thread: &mut SchemeThread,
        name: Value,
        lambda: &lexpr::Value,
    ) -> Result<(), Value> {
        let exporting = self.exporting(thread);
        let mut closure = false;
        let args_and_body = self.expect_cons(thread, lambda)?;
        let args = args_and_body.car();
        let body = args_and_body.cdr();
        let mut env = self.env;
        let parent = thread.runtime.global_symbol(crate::runtime::Global::Parent);
        while !env_globalp(thread, env) {
            env = env.get(Value::new(parent)).unwrap().table();
        }
        let mut qualified_name = env_qualify_name(thread, env, name);
        let proto = self.generate_lambda(thread, name, args, body, &mut closure)?;

        let proto = thread.mutator.allocate(
            Macro {
                p: Value::new(proto),
            },
            comet::gc_base::AllocationSpace::New,
        );
        env_define(thread, env, Value::new(name), Value::new(proto), exporting);
        env_define(
            thread,
            env,
            Value::new(qualified_name),
            Value::new(proto),
            exporting,
        );
        qualified_name.value = Value::new(proto);
        Ok(())
    }
    pub fn compile_set(
        &mut self,
        thread: &mut SchemeThread,
        rest: &lexpr::Value,
    ) -> Result<(), Value> {
        let rest = self.expect_cons(thread, rest)?;
        let name = self.expect_symbol(thread, rest.car())?;
        let name = make_symbol(thread, name);
        let value = self.expect_cons(thread, rest.cdr())?.car();

        self.compile(thread, value, State::USED_NON_FINAL)?;
        if !self.variable_set(thread, name) {
            Err(self.syntax_error(thread, format!("variable `{}` not found", Value::new(name))))
        } else {
            Ok(())
        }
    }

    pub fn compile_code<'a, R>(
        &mut self,
        thread: &mut SchemeThread,
        mut parser: lexpr::Parser<R>,
    ) -> Result<Managed<ScmPrototype>, Value>
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
        for (i, expr) in to_be_compiled.iter().enumerate() {
            let is_last = i == to_be_compiled.len() - 1;

            self.compile(
                thread,
                expr,
                if is_last {
                    State::USED_NON_FINAL
                } else {
                    State::NOT_USED_NON_FINAL
                },
            )?;
        }

        self.code.push(Op::Return);
        //self.pop(1);

        Ok(self.end(thread, 0, false))
    }
}

macro_rules! car {
    ($thread: expr,$cell: expr) => {
        if $cell.consp() {
            $cell.car()
        } else {
            return Err();
        }
    };
}
fn syntax_error(thread: &mut SchemeThread, message: impl AsRef<str>) -> Value {
    let tag = thread
        .runtime
        .global_symbol(crate::runtime::Global::ScmCompile);
    let msg = make_string(thread, format!("syntax error: {}", message.as_ref()));
    Value::new(make_exception(thread, tag, msg, Value::new(Null)))
}

pub fn expect_cons<'a>(
    thread: &mut SchemeThread,
    exp: &'a lexpr::Value,
) -> Result<&'a lexpr::Cons, Value> {
    exp.as_cons()
        .ok_or_else(|| syntax_error(thread, format!("cons expected but `{}` found", exp)))
}

#[derive(Debug, Clone)]
pub struct Pattern {
    expr: lexpr::Value,
    variables: Vec<lexpr::Value>,
    expanded_variables: Vec<lexpr::Value>,
    ellipsis: lexpr::Value,
    literals: Vec<lexpr::Value>,
    underscore: lexpr::Value,
}

impl Pattern {
    pub fn new(
        thread: &mut SchemeThread,
        expr: &lexpr::Value,
        ellipsis: &lexpr::Value,
        literals: &[lexpr::Value],
    ) -> Result<Self, Value> {
        let mut pattern = Self {
            expr: expr.clone(),
            variables: vec![],
            expanded_variables: vec![],
            ellipsis: ellipsis.clone(),
            literals: literals.to_vec(),
            underscore: lexpr::Value::symbol("_"),
        };
        Self::build(thread, expr.as_cons().unwrap().cdr(), &mut pattern)?;
        Ok(pattern)
    }

    pub fn is_ellipsis(&self, cell: &lexpr::Value) -> bool {
        self.ellipsis == *cell
    }

    pub fn is_literal(&self, cell: &lexpr::Value) -> bool {
        self.literals.iter().any(|it| it == cell)
    }

    pub fn is_variable(&self, cell: &lexpr::Value) -> bool {
        self.variables.iter().any(|it| it == cell)
    }

    pub fn is_expanded_variable(&self, cell: &lexpr::Value) -> bool {
        self.expanded_variables.iter().any(|it| it == cell)
    }

    fn is_variable_candidate(&self, cell: &lexpr::Value) -> bool {
        cell.is_symbol()
            && !self.is_literal(cell)
            && !self.is_ellipsis(cell)
            && *cell != self.underscore
    }

    fn build(
        thread: &mut SchemeThread,
        expr: &lexpr::Value,
        pattern: &mut Self,
    ) -> Result<(), Value> {
        let improper = expr.is_dotted_list();
        let len = expr.list_iter().map(|x| x.count()).unwrap_or_else(|| 0);

        let mut iter = expr
            .list_iter()
            .unwrap_or_else(|| lexpr::Value::Null.list_iter().unwrap())
            .enumerate()
            .peekable();

        let mut ellipsis_ct = 0;
        while let Some((idx, it)) = iter.next() {
            let ellipsis_next = match iter.peek() {
                Some((_, cell)) => pattern.is_ellipsis(cell),
                _ => false,
            };

            match it {
                lexpr::Value::Symbol(_) => {
                    if pattern.is_ellipsis(it) {
                        if idx == 0 || (idx == len - 1 && improper) {
                            return Err(syntax_error(
                                thread,
                                format!("invalid ellipsis placement in {}", expr),
                            ));
                        }

                        ellipsis_ct += 1;

                        if ellipsis_ct > 1 {
                            return Err(syntax_error(
                                thread,
                                format!("duplicate ellipsis in {}", expr),
                            ));
                        }
                        continue;
                    }

                    if pattern.is_variable_candidate(it) {
                        if pattern.is_variable(it) {
                            return Err(syntax_error(
                                thread,
                                format!("duplicate pattern variable `{}`", it),
                            ));
                        }

                        pattern.variables.push(it.clone());
                    } else if ellipsis_next {
                        return Err(syntax_error(
                            thread,
                            format!("ellipsis must follow pattern variable (in {})", expr),
                        ));
                    }
                    if ellipsis_next {
                        Self::find_expanded_variables(it, pattern);
                    }
                }
                lexpr::Value::Cons(_) => {
                    if ellipsis_next {
                        Self::find_expanded_variables(it, pattern);
                    }
                    Self::build(thread, it, pattern)?;
                }
                _ => (),
            }
        }

        Ok(())
    }

    fn find_expanded_variables(expr: &lexpr::Value, pattern: &mut Pattern) {
        match expr {
            lexpr::Value::Symbol(_) => {
                if pattern.is_variable_candidate(expr)
                    && !pattern.expanded_variables.iter().any(|it| it == expr)
                {
                    pattern.expanded_variables.push(expr.clone());
                }
            }
            lexpr::Value::Cons(_) => {
                for it in expr
                    .list_iter()
                    .unwrap_or_else(|| lexpr::Value::Null.list_iter().unwrap())
                {
                    Self::find_expanded_variables(it, pattern);
                }
            }
            _ => {}
        }
    }
}

pub fn car<'a>(thread: &mut SchemeThread, val: &'a Cell) -> Result<&'a Cell, Value> {
    Ok(expect_cons(thread, val)?.car())
}
pub fn cdr<'a>(thread: &mut SchemeThread, val: &'a Cell) -> Result<&'a Cell, Value> {
    Ok(expect_cons(thread, val)?.cdr())
}

type Cell = lexpr::Value;

#[derive(Debug)]
pub struct Transform {
    keyword: lexpr::Value,
    ellipsis: lexpr::Value,
    syntax_rules: Vec<(Pattern, lexpr::Value)>,
    literals: Vec<lexpr::Value>,
}

impl Transform {
    pub fn try_new(thread: &mut SchemeThread, expr: &lexpr::Value) -> Result<Self, Value> {
        let expr = expr.to_vec().unwrap_or_else(|| vec![]);
        let (keyword, syntax_rules) = match expr.as_slice() {
            [_, keyword, syntax_rules] => (keyword.clone(), syntax_rules.clone()),
            _ => return Err(syntax_error(thread, "expected keyword and syntax-rules")),
        };
        if !keyword.is_symbol() {
            return Err(syntax_error(thread, "keyword must be an identifier"));
        }

        let syntax_rules = expect_cons(thread, &syntax_rules)?.clone();

        if *syntax_rules.car() != lexpr::Value::symbol("syntax-rules") {
            return Err(syntax_error(thread, "expected syntax-rules"));
        }
        let syntax_rules = expect_cons(thread, syntax_rules.cdr())?;

        let (syntax_rules, ellipsis) = match syntax_rules.car() {
            lexpr::Value::Symbol(_) => {
                let ellipsis = syntax_rules.car().clone();
                let syntax_rules = syntax_rules.cdr().clone();
                (syntax_rules, ellipsis)
            }
            _ => (
                lexpr::Value::Cons(syntax_rules.clone()),
                lexpr::Value::symbol("..."),
            ),
        };

        let syntax_rules = expect_cons(thread, &syntax_rules)?;

        let literals = syntax_rules.car().to_vec().unwrap_or_else(|| vec![]);

        if literals.iter().any(|it| !it.is_symbol()) {
            return Err(syntax_error(thread, "literals must be identifiers"));
        }

        let syntax_rules = syntax_rules.cdr();

        let syntax_rules = syntax_rules.to_vec().unwrap_or_else(|| vec![]);

        let mut syntax_rules_vec = vec![];

        for it in syntax_rules {
            let it = expect_cons(thread, &it)?;
            let pattern = it.car();
            let template = expect_cons(thread, it.cdr())?.car().clone();
            let pattern = Pattern::new(thread, pattern, &ellipsis, &literals)?;
            syntax_rules_vec.push((pattern, template));
        }

        let this = Transform {
            keyword: keyword.clone(),
            ellipsis,
            syntax_rules: syntax_rules_vec,
            literals,
        };

        Ok(this)
    }
    /// Transform
    ///
    /// Transform the input expression given the syntax-rules defined in
    /// this transformer. An error is returned if none of the input expressions
    /// match the patterns specified in the syntax-rules of this transformer.
    ///
    /// # Arguments
    /// `expr` - The expression to transform
    pub fn transform(&self, thread: &mut SchemeThread, expr: &Cell) -> Result<Cell, Value> {
        let mut invalid_syntax = || Err(syntax_error(thread, format!("{}", self.keyword)));
        if !expr.is_cons() {
            invalid_syntax()?;
        }

        for rule in &self.syntax_rules {
            let mut env = PatternEnvironment::new(&rule.0);
            if self.pattern_match(cdr(thread, &rule.0.expr)?, cdr(thread, expr)?, &mut env) {
                return self
                    .expand(&rule.1, &rule.0, &mut env)
                    .ok_or_else(|| syntax_error(thread, format!("{}", self.keyword)));
            }
        }

        return Err(syntax_error(
            thread,
            format!("no matching syntax for {}", self.keyword),
        ));
    }

    /// Pattern Match
    ///
    /// Attempt to match the input expression against one of the syntax-rules pattern,
    /// returning a pattern environment if successful.
    ///
    /// # Arguments
    /// `pattern` - The pattern to attempt to apply
    /// `expr` - The expression to match
    /// `bindings` - The set of matched variable bindings
    fn pattern_match<'a, 'b>(
        &self,
        pattern: &'a Cell,
        expr: &'a Cell,
        env: &'b mut PatternEnvironment<'a>,
    ) -> bool {
        // expr and pattern must either both be lists or improper lists
        if (pattern.is_cons() || pattern.is_null()) && !(expr.is_cons() || expr.is_null()) {
            return false;
        }
        if expr.is_cons() && pattern.is_cons() && (expr.is_list() != pattern.is_list()) {
            return false;
        }

        let expr_iter_c = expr
            .list_iter()
            .unwrap_or_else(|| lexpr::Value::Null.list_iter().unwrap())
            .peekable()
            .count();
        let pattern_iter_c = pattern
            .list_iter()
            .unwrap_or_else(|| lexpr::Value::Null.list_iter().unwrap())
            .peekable()
            .count();

        let mut expr_iter = expr
            .list_iter()
            .unwrap_or_else(|| lexpr::Value::Null.list_iter().unwrap())
            .peekable();
        let mut pattern_iter = pattern
            .list_iter()
            .unwrap_or_else(|| lexpr::Value::Null.list_iter().unwrap())
            .peekable();

        let mut expr;
        let mut pattern = &Cell::Nil;

        let mut in_ellipsis = false;

        loop {
            // Get the next expression
            // If there is no next expression, then:
            //   * If we are in an ellipsis expansion, move the pattern iterator
            //     past it so we can see if more pattern remains.
            //   * If any pattern remains, there is no match.
            //   * If pattern was exhausted, then the match is complete.
            expr = match expr_iter.next() {
                Some(expr) => expr,
                None => {
                    if in_ellipsis {
                        pattern_iter.next();
                    }
                    return match pattern_iter.next() {
                        Some(_) => {
                            if pattern_iter.peek() == Some(&&self.ellipsis) {
                                pattern_iter.next();
                                pattern_iter.peek().is_none()
                            } else {
                                false
                            }
                        }
                        None => true,
                    };
                }
            };

            // Get the next pattern.
            // * Reuse the same pattern if we're in an ellipsis expansion
            //   and based on the expression length there's more to capture.
            pattern = match in_ellipsis {
                true => {
                    if pattern_iter_c == expr_iter_c + 2 {
                        pattern_iter.next();
                        match pattern_iter.next() {
                            Some(pattern) => pattern,
                            None => return expr_iter.peek().is_none(),
                        }
                    } else {
                        pattern
                    }
                }
                false => match pattern_iter.next() {
                    Some(pattern) => pattern,
                    None => {
                        return false;
                    }
                },
            };

            in_ellipsis = pattern_iter.peek() == Some(&&self.ellipsis);

            match pattern {
                Cell::Symbol(_) => {
                    if self.is_literal(pattern) {
                        if pattern != expr {
                            return false;
                        }
                    } else if pattern != &lexpr::Value::symbol("_") {
                        env.add_binding(pattern, expr);
                    }
                }
                Cell::Cons(_) => {
                    if !self.pattern_match(pattern, expr, env) {
                        return false;
                    }
                }
                pattern => {
                    if pattern != expr {
                        return false;
                    }
                }
            }
        }
    }

    /// Is Literal
    ///
    /// Is cell in the set of literals?
    pub fn is_literal(&self, cell: &Cell) -> bool {
        self.literals.iter().any(|it| it == cell)
    }

    pub fn keyword(&self) -> &Cell {
        &self.keyword
    }

    /// Expand
    ///
    /// Given a list of bindings created from a pattern match, and a template, expand
    /// the template with the bindings.
    ///
    /// # Arguments
    /// `template` - The template to use for expansion
    /// `pattern` - The pattern associated with the template being expanded.
    /// `bindings` The matched bindings from the pattern
    fn expand(
        &self,
        template: &Cell,
        pattern: &Pattern,
        env: &mut PatternEnvironment,
    ) -> Option<Cell> {
        match template {
            Cell::Symbol(_) => {
                return if pattern.is_variable(template) {
                    env.get_binding(template).cloned()
                } else {
                    Some(template.clone())
                }
            }
            Cell::Cons(_) => {
                let mut v = vec![];
                let mut template_iter = template
                    .list_iter()
                    .unwrap_or_else(|| lexpr::Value::Null.list_iter().unwrap())
                    .peekable();
                let mut template = template_iter.next().unwrap();

                loop {
                    let in_ellipsis = template_iter.peek() == Some(&&self.ellipsis);
                    match self.expand(template, pattern, env) {
                        Some(cell) => {
                            v.push(cell);
                            if in_ellipsis {
                                continue;
                            }
                        }
                        None => {
                            if !in_ellipsis {
                                return None;
                            }
                            template_iter.next();
                        }
                    }

                    template = match template_iter.next() {
                        Some(template) => template,
                        None => {
                            break;
                        }
                    };
                }
                Some(lexpr::Value::list(v))
            }
            cell => Some(cell.clone()),
        }
    }
}

/// Pattern Environment
///
/// Pattern environment is the result of a successful pattern,
/// containing all of the information needed to apply the template
/// portion of the pattern rule.
#[derive(Debug, Clone)]
struct PatternEnvironment<'a> {
    /// Bindings are pairs of matched (pattern expr)
    bindings: Vec<(&'a Cell, &'a Cell)>,

    /// A copy of the pattern, which is used to determine what
    /// type of bindings a variable is
    pattern: &'a Pattern,

    /// Position of expanded bindings (bindings that were captured
    /// and expanded with the ellipsis)
    iters: Vec<(&'a Cell, Option<usize>)>,
}

impl<'a> PatternEnvironment<'a> {
    fn new(pattern: &'a Pattern) -> PatternEnvironment<'a> {
        PatternEnvironment {
            bindings: vec![],
            pattern,
            iters: pattern
                .expanded_variables
                .iter()
                .map(|it| (it, None))
                .collect(),
        }
    }

    fn add_binding(&mut self, pattern: &'a Cell, expr: &'a Cell) {
        self.bindings.push((pattern, expr));
    }

    fn get_binding(&mut self, symbol: &Cell) -> Option<&'a Cell> {
        if !self.pattern.is_variable(symbol) {
            None
        } else if self.pattern.is_expanded_variable(symbol) {
            self.get_expanded_binding(symbol)
        } else {
            self.bindings
                .iter()
                .find(|it| it.0 == symbol)
                .map(|it| it.1)
        }
    }

    fn get_expanded_binding(&mut self, symbol: &Cell) -> Option<&'a Cell> {
        let iter = match self.iters.iter_mut().find(|it| it.0 == symbol) {
            Some((_, iter)) => iter,
            None => {
                return None;
            }
        };

        let start = match iter {
            Some(position) => *position,
            None => 0_usize,
        };

        match self.bindings[start..self.bindings.len()]
            .iter()
            .enumerate()
            .find(|it| it.1 .0 == symbol)
        {
            Some(binding) => {
                *iter = Some(start + binding.0 + 1);
                Some(binding.1 .1)
            }
            None => {
                *iter = None;
                None
            }
        }
    }
}

unsafe impl Trace for Transform {}
unsafe impl Finalize for Transform {}

impl Collectable for Transform {}
