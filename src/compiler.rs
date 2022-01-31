use comet::{api::Trace, letroot};
use comet_extra::alloc::vector::Vector;

use crate::{
    runtime::{
        convert_module_name, env_define, env_globalp, env_qualify_name, lexpr_to_value,
        load_module, make_blob, make_exception, make_string, make_symbol, make_table, make_vector,
        module_loaded, register_module_,
        value::{Null, ScmPrototype, ScmString, ScmTable, Undefined, Value},
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
}

unsafe impl Trace for Op {}
/// A structure describing the location of a free variable relative to the function it's being used in
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct FreeVariableInfo {
    /// The lexical location of the variable
    lexical_level: usize,
    lexical_index: usize,
    /// The upvalue's index at runtime, either in the upvalues array of the
    /// preceding function, or in the locals array of the currently executing
    /// function
    index: usize,
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

impl Compiler {
    pub fn clear(&mut self) {
        self.code.clear();
        self.free_variables.clear();
        self.local_free_variable_count = 0;
        self.upvalue_count = 0;
        self.stack_max = 0;
        self.stack_size = 0;
        self.locals = 0;
        self.closure = false;
        self.name = None;
    }
    pub fn new(
        thread: &mut SchemeThread,
        parent: Option<*mut Self>,
        env: Option<Managed<ScmTable>>,
        depth: usize,
    ) -> Self {
        let constants = Vector::new(&mut thread.mutator);
        Self {
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

    pub fn compile(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        tail: bool,
    ) -> Result<(), Value> {
        match exp {
            lexpr::Value::Bool(x) => {
                if !*x {
                    self.emit(Op::PushFalse);
                } else {
                    self.emit(Op::PushTrue);
                }
                self.dump(&format!("push-{}", x));
                self.push(1);
            }
            lexpr::Value::Number(x) => {
                if x.is_i64() && x.as_i64().unwrap() as i32 as i64 == x.as_i64().unwrap() {
                    self.emit(Op::PushInt(x.as_i64().unwrap() as i32));
                    self.push(1);
                    self.dump(&format!("push-int {}", x.as_i64().unwrap()));
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
                        _ => (),
                    },
                    _ => (),
                }

                self.compile_apply(thread, exp, tail)?;
            }

            _ => todo!("{:?}", exp),
        }
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
            self.dump(&format!("tail-apply {}", argc));
        } else {
            self.emit(Op::Apply(argc as _));
            self.dump(&format!("apply {}", argc));
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
        self.dump("compiling subfunction");
        let stack = thread.mutator.shadow_stack();
        letroot!(
            cc = stack,
            Compiler::new(thread, Some(self), Some(new_env), self.depth + 1)
        );
        cc.locals = argc as _;

        if !name.is_null() {
            cc.name = Some(name.symbol_name());
        }

        cc.compile(
            thread,
            rest.as_cons().unwrap().cdr().as_cons().unwrap().car(),
            true,
        )?;

        let proto = cc.end(thread, argc as _, variable_arity);
        *closure = cc.closure;

        Ok(Value::new(proto))
    }

    pub fn compile_if(
        &mut self,
        thread: &mut SchemeThread,
        exp: &lexpr::Value,
        tail: bool,
    ) -> Result<(), Value> {
        let condition = exp.as_cons().unwrap().car();
        let then_expr = exp.as_cons().unwrap().cdr().as_cons().unwrap().car();
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
        self.dump("jump-if-false");

        let old_stack = self.stack_size as usize;

        self.compile(thread, then_expr, tail)?;
        self.pop(self.stack_size as usize - old_stack);
        let jmp2 = self.code.len();
        self.emit(Op::Jump(0));
        self.dump("jump");
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
        self.dump(&format!("Patch jump-if-false {}", lbl1));
        self.dump(&format!("Patch jump {}", lbl2));
        self.code[jmp1] = Op::JumpIfFalse(lbl1 as _);
        self.code[jmp2] = Op::Jump(lbl2 as _);
        Ok(())
    }

    pub fn register_free_variable(&mut self, lookup: &Lookup) -> usize {
        let mut l = FreeVariableInfo {
            index: 0,
            lexical_index: 0,
            lexical_level: 0,
        };

        for i in 0..self.free_variables.len() {
            l = self.free_variables[i];
            if let Lookup::Local { level, index, .. } = lookup {
                if *level == l.lexical_level && l.lexical_index == *index {
                    return i;
                }
            }
        }
        if let Lookup::Local { level, index, .. } = lookup {
            l.lexical_level = *level;
            l.lexical_index = *index;

            let mut lookup_copy = *lookup;
            match &mut lookup_copy {
                Lookup::Local { level, .. } => *level -= 1,
                _ => unreachable!(),
            }
            if l.lexical_level != 0 {
                self.closure = true;
                unsafe {
                    l.index =
                        (**self.parent.as_mut().unwrap()).register_free_variable(&lookup_copy);
                }
                self.upvalue_count += 1;
            } else {
                l.index = l.lexical_index;
                self.local_free_variable_count += 1;
            }
            self.free_variables.push(l);
            self.free_variables.len() - 1
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
                self.dump("global-get");
                Ok(())
            }
            Lookup::Local { index, up, .. } => {
                if !*up {
                    self.emit(Op::LocalGet(*index as _));
                    self.push(1);
                    self.dump(&format!("local-get {}", index));
                } else {
                    let index = self.register_free_variable(lookup);
                    self.emit(Op::UpvalueGet(index as _));
                    self.push(1);
                    self.dump(&format!("upvalue-get {}", index));
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
                let qualified_name = env_qualify_name(thread, env, name);

                self.push_constant(thread, Value::new(qualified_name));
                self.emit(Op::GlobalSet);
                self.dump("global-set");
                self.pop(1);
            }
            Lookup::Local { index, up, .. } => {
                if *up {
                    let index = self.register_free_variable(lookup);
                    self.emit(Op::UpvalueGet(index as _));
                    self.dump(&format!("upvalue-get {}", index));
                } else {
                    self.emit(Op::LocalSet(*index as _));
                    self.dump(&format!("local-set {}", index));
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
                self.dump(&format!("push-constant {} : {}", i, constant));
                return;
            }
        }
        let i = self.constants.len();
        self.constants.push(&mut thread.mutator, constant);
        self.emit(Op::PushConstant(i as _));
        self.dump(&format!("push-constant {} : {}", i, constant));
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
                let l = UpvalLoc {
                    local: self.free_variables[i].lexical_level == 1,
                    index: self.free_variables[i].index as _,
                };
                unsafe {
                    u.blob_set(upvalue_i, l);
                    upvalue_i += 1;
                }
            }
        }
        let debuginfo = make_blob::<u8>(thread, 0);
        let constants = std::mem::replace(&mut self.constants, Vector::new(&mut thread.mutator));
        thread.mutator.allocate(
            ScmPrototype {
                constants: constants,
                local_free_variables: local_free_vars,
                local_free_variable_count: self.local_free_variable_count as _,
                upvalues: upvals,
                arguments: arguments as _,
                variable_arity,
                code: codeblob,
                debuginfo,
                locals: self.locals as _,
                name: self.name,
                stack_max: self.stack_max as _,
            },
            comet::gc_base::AllocationSpace::Old,
        )
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
        } else if env_globalp(thread, env) {
            let rt = thread.runtime;
            for module in rt.inner().qualified_imports.iter() {
                let module = module.table();

                let exports = thread
                    .runtime
                    .global_symbol(crate::runtime::Global::Exports);
                if let Some(exports) = module.get(Value::new(exports)) {
                    if exports.tablep() {
                        let table = exports.table();

                        if let Some(val) = table.get(Value::new(key)) {
                            return Some(Lookup::Global {
                                value: val,
                                module: Value::new(module),
                            });
                        }
                    }
                }
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
