use std::mem::size_of;

use crate::{
    disasm::disasm,
    gc::Gc,
    sexp::{
        intern, make_bytes, make_bytes2, make_env, make_exception, make_pair, make_string,
        make_synclo, make_vector, r5rs_equal_pred, CallResult, Closure, Context, ContextRef,
        Global, NativeCallback, NativeProcedure, Op, Procedure, Symbol, Upvalue, UpvaluerInner,
        Value, ValueType,
    },
    vec::GcVec,
};

fn check_arguments(ctx: ContextRef, argc: usize, expected: usize, variable: bool) -> Value {
    if argc < expected && (!variable && argc != argc - 1) {
        return arity_error_least(ctx, expected, argc);
    } else if argc > expected as usize && !variable {
        return arity_error_most(ctx, expected, argc);
    }
    Value::new_bool(true)
}

fn arity_error_least(ctx: ContextRef, expected: usize, argc: usize) -> Value {
    let kind = ctx.global(Global::ScmEval);
    let message = make_string(
        ctx,
        format!(
            "function expected at least {} arguments but found {}",
            expected, argc
        ),
    );

    make_exception(
        ctx,
        kind,
        message,
        Value::new_null(),
        Value::new_null(),
        Value::new_null(),
    )
}
fn arity_error_most(ctx: ContextRef, expected: usize, argc: usize) -> Value {
    let kind = ctx.global(Global::ScmEval);
    let message = make_string(
        ctx,
        format!(
            "function expected at most {} arguments but found {}",
            expected, argc
        ),
    );

    make_exception(
        ctx,
        kind,
        message,
        Value::new_null(),
        Value::new_null(),
        Value::new_null(),
    )
}

fn stack_overflow(ctx: ContextRef, f: Value) -> Value {
    let kind = ctx.global(Global::ScmEval);
    let message = make_string(ctx, format!("stack overflow when trying to invoke {}", f,));
    make_exception(
        ctx,
        kind,
        message,
        Value::new_null(),
        Value::new_null(),
        Value::new_null(),
    )
}

fn not_a_function(ctx: ContextRef, f: Value) -> Value {
    let kind = ctx.global(Global::ScmEval);
    let message = make_string(ctx, format!("{} is not applicable", f,));
    make_exception(
        ctx,
        kind,
        message,
        Value::new_null(),
        Value::new_null(),
        Value::new_null(),
    )
}

pub fn apply(mut ctx: ContextRef, function: Value, args: &[Value]) -> Value {
    ctx.trampoline_arguments.clear();
    let mut c = ctx;
    ctx.trampoline_arguments.extend_from_slice(c.heap(), args);
    ctx.trampoline_function = function;
    unsafe { vm_apply(ctx) }
}

unsafe fn vm_apply(mut ctx: ContextRef) -> Value {
    let mut procedure;
    let mut closure;
    'apply: loop {
        let function = ctx.trampoline_function;
        let argc = ctx.trampoline_arguments.len();
        if function.procedurep() || function.closurep() {
            let (proc, clos) = if function.procedurep() {
                (function, Value::new_null())
            } else {
                (function.closure_procedure(), function)
            };

            procedure = proc;
            closure = clos;
        } else if function.nativep() {
            let native = function.downcast::<NativeProcedure>(ValueType::NativeFunction as _);

            let res = check_arguments(
                ctx,
                ctx.trampoline_arguments.len(),
                native.argc,
                native.variable,
            );
            if res.exceptionp() {
                return res;
            }
            let prev = ctx.stack.current;
            let frame = ctx.stack.make_frame(function, Value::new_null(), argc);
            if frame.is_null() {
                return stack_overflow(ctx, function);
            }
            for i in 0..argc {
                (*frame).push(ctx.trampoline_arguments[i]);
            }
            let args = (*frame).slice(argc);

            match (native.callback)(ctx, args, native.closure) {
                CallResult::Done(val) => {
                    ctx.stack.leave_frame(frame);
                    debug_assert_eq!(prev, ctx.stack.current);
                    return val;
                }
                CallResult::Trampoline => {
                    ctx.stack.leave_frame(frame);
                    continue 'apply;
                }
            }
        } else {
            panic!("{}", function);
            return not_a_function(ctx, function);
        }

        let procedure = procedure.downcast::<Procedure>(ValueType::Function as _);
        let res = check_arguments(
            ctx,
            argc,
            procedure.arguments as _,
            procedure.variable_arity,
        );
        if res.exceptionp() {
            return res;
        }

        let frame = ctx.stack.make_frame(Value::new_cell(procedure), closure, 0);
        if frame.is_null() {
            return stack_overflow(ctx, function);
        }

        let mut ip = (*frame).ip;
        let start = ip;
        let mut si = (*frame).si;
        let bp = (*frame).bp;
        let locals = (*frame).locals;
        let c = ctx;
        for i in 0..procedure.arguments {
            if procedure.variable_arity && i == procedure.arguments - 1 {
                locals
                    .add(i as _)
                    .write(make_list(c, &ctx.trampoline_arguments[i as usize..]));
                break;
            } else {
                locals
                    .add(i as _)
                    .write(ctx.trampoline_arguments[i as usize]);
            }
        }

        let lupvalues = (*frame).upvalues;

        for i in 0..procedure.local_free_variable_count {
            let ix = procedure.local_free_variables.bvector_ref::<u16>(i as _);
            lupvalues
                .add(i as _)
                .write(Value::new_cell(ctx.heap().allocate_tagged(
                    Upvalue {
                        converted: false,
                        inner: UpvaluerInner {
                            local_ref: locals.add(ix as _),
                        },
                    },
                    ValueType::Upvalue as _,
                    false,
                    false,
                )));
        }

        macro_rules! pop {
            () => {{
                si -= 1;
                bp.add(si as usize).read()
            }};
        }
        macro_rules! push {
            ($val: expr) => {{
                bp.add(si as _).write($val);
                si += 1;
            }};
        }

        macro_rules! slice {
            ($size: expr) => {{
                std::slice::from_raw_parts(bp.add(si as usize - $size), $size)
            }};
        }
        loop {
            let op = ip.cast::<Op>().read();

            ip = ip.add(1);

            match op {
                Op::Pop => {
                    pop!();
                }
                Op::Dup => {
                    let x = pop!();
                    push!(x);
                    push!(x);
                }
                Op::LoadN => {
                    push!(Value::new_null());
                }
                Op::LoadI => {
                    let i = ip.cast::<i32>().read();
                    ip = ip.add(4);
                    push!(Value::new_i32(i));
                }

                Op::LoadF => {
                    let f = ip.cast::<u64>().read();
                    ip = ip.add(8);
                    push!(Value::new_f64(f64::from_bits(f)));
                }
                Op::LoadC => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);
                    let c = procedure.constants.vector_ref(ix as _);
                    push!(c);
                }

                Op::LocalRef => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);

                    let value = locals.add(ix as _).read();
                    push!(value);
                }

                Op::LocalSet => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);

                    let value = pop!();

                    locals.add(ix as _).write(value);
                }

                Op::GlobalRef => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);
                    let c = procedure.constants.vector_ref(ix as _);
                    let global = c.downcast::<Symbol>(ValueType::Symbol as _).value;
                    push!(global);
                }
                Op::GlobalSet => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);
                    let c = procedure.constants.vector_ref(ix as _);

                    c.downcast::<Symbol>(ValueType::Symbol as _).value = pop!();
                }

                Op::ClosureRef => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);

                    let value = closure
                        .closure_upvalues()
                        .vector_ref(ix as _)
                        .upvalue_value();

                    push!(value);
                }
                Op::ClosureSet => {
                    let ix = ip.cast::<u16>().read();
                    ip = ip.add(2);
                    let value = pop!();

                    closure
                        .closure_upvalues()
                        .vector_ref(ix as _)
                        .upvalue_set_value(value);
                }

                Op::Jump => {
                    let new_ip = ip.cast::<u32>().read();

                    ip = start.add(new_ip as _);
                }
                Op::JumpIfFalse => {
                    let new_ip = ip.cast::<u32>().read();
                    ip = ip.add(4);
                    let value = pop!();

                    if value.is_false() || value.is_null() {
                        ip = start.add(new_ip as _);
                    }
                }

                Op::JumpIfTrue => {
                    let new_ip = ip.cast::<u32>().read();
                    ip = ip.add(4);
                    let value = pop!();
                    if !(value.is_false() || value.is_null()) {
                        ip = start.add(new_ip as _);
                    }
                }

                Op::Apply => {
                    let nargs = ip.cast::<u16>().read() as usize;
                    ip = ip.add(2);
                    let func = pop!();
                    let args = slice!(nargs);
                    //println!("{:p} apply {}", ip.sub(3), func,);
                    let res = apply(ctx, func, args);
                    for _ in 0..nargs {
                        pop!();
                    }
                    if res.exceptionp() {
                        ctx.stack.leave_frame(frame);
                        return res;
                    }
                    push!(res);
                }
                Op::TailApply => {
                    let nargs = ip.cast::<u16>().read() as usize;
                    let func = pop!();
                    let args = slice!(nargs);
                    let mut c = ctx;

                    ctx.trampoline_arguments.clear();
                    ctx.trampoline_arguments.extend_from_slice(c.heap(), args);
                    ctx.trampoline_function = func;
                    ctx.stack.leave_frame(frame);
                    continue 'apply;
                }

                Op::Return => {
                    let value = if si == 0 { Value::new_null() } else { pop!() };

                    ctx.stack.leave_frame(frame);
                    return value;
                }

                Op::MakeClosure => {
                    let proc = pop!().downcast::<Procedure>(ValueType::Function as _);

                    let locals = proc.upvalues;

                    let upvalues =
                        make_vector(ctx, locals.bvector_length::<UpvalLoc>(), Value::new_null());

                    for i in 0..locals.bvector_length::<UpvalLoc>() {
                        let l = locals.bvector_ref::<UpvalLoc>(i);
                        if l.local {
                            upvalues.vector_set(i, lupvalues.add(l.index as _).read());
                        } else {
                            upvalues
                                .vector_set(i, closure.closure_upvalues().vector_ref(l.index as _));
                        }
                    }

                    let closure = ctx.heap().allocate_tagged(
                        Closure {
                            procedure: Value::new_cell(proc),
                            upvalues,
                            data: Value::new_null(),
                        },
                        ValueType::Closure as _,
                        false,
                        false,
                    );
                    push!(Value::new_cell(closure));
                }
            }
        }
    }
}

pub fn listp(mut lst: Value) -> bool {
    if lst.is_null() {
        return true;
    }

    if !lst.pairp() {
        return false;
    }
    while lst.pairp() {
        lst = lst.cdr();
    }
    lst.is_null()
}

pub fn remove_memq(ctx: ContextRef, lst: Value, item: Value) -> Value {
    if lst.is_null() {
        return Value::new_null();
    } else if lst.car() == item {
        return lst.cdr();
    } else {
        make_pair(ctx, lst.car(), remove_memq(ctx, lst.cdr(), item))
    }
}

pub fn memq(mut lst: Value, x: Value) -> bool {
    while lst.pairp() {
        if lst.car() == x {
            return true;
        }
        lst = lst.cdr()
    }

    false
}

pub fn make_list(ctx: ContextRef, values: &[Value]) -> Value {
    let mut first = Value::new_null();
    let mut last = Value::new_null();
    for &val in values {
        let newcell = make_pair(ctx, val, Value::new_null());
        if first.is_null() {
            first = newcell;
        } else {
            last.set_cdr(newcell);
        }
        last = newcell;
    }
    first
}

fn append_m(ctx: ContextRef, head: &mut Value, tail: &mut Value, value: Value) {
    let h = *head;
    let t = *tail;
    let swap = make_pair(ctx, value, Value::new_null());
    if h.is_null() {
        *head = swap;
        *tail = swap;
    } else {
        t.set_cdr(swap);
        *tail = swap;
    }
}

pub fn list_copy(ctx: ContextRef, mut lst: Value) -> Value {
    let mut lst2head = Value::new_null();
    let mut lst2tail = lst2head;
    while lst.pairp() {
        append_m(ctx, &mut lst2head, &mut lst2tail, lst.car());
        lst = lst.cdr();
    }

    lst2head
}

fn convert_module_name(ctx: ContextRef, mut spec: Value) -> Value {
    let mut out = String::new();
    out.push('#');
    if spec.symbolp() {
        out.push_str(spec.symbol_name().string_data());
        return make_string(ctx, out);
    }

    if !listp(spec) {
        let kind = ctx.global(Global::ScmEval);
        let message = make_string(ctx, "module name must be a list of symbols");

        return make_exception(
            ctx,
            kind,
            message,
            Value::new_null(),
            Value::new_null(),
            Value::new_null(),
        );
    }
    while spec.pairp() {
        if !spec.car().symbolp() {
            let kind = ctx.global(Global::ScmEval);
            let message = make_string(ctx, "module name must be a symbol");

            return make_exception(
                ctx,
                kind,
                message,
                Value::new_null(),
                Value::new_null(),
                Value::new_null(),
            );
        }

        out.push_str(spec.car().symbol_name().string_data());
        if !spec.cdr().is_null() {
            out.push('#');
        }
        spec = spec.cdr();
    }

    make_string(ctx, out)
}

/// A structure describing the location of a free variable relative to the function it's being used in
#[derive(Clone, Copy, PartialEq, Eq)]
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

pub fn env_define(ctx: ContextRef, table: Value, key: Value, value: Value, exported: bool) {
    let mut exports = Value::new_null();

    if exported {
        exports = table.hash_get(ctx, ctx.global(Global::Exports), Value::new_null());
    }
    let chk;
    chk = table.hash_set(ctx, key, value);
    if exported {
        exports.hash_set(ctx, key, value);
    }

    assert!(!chk.exceptionp(), "cannot throw exception in env_define");
}

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

pub struct Compiler {
    parent: Option<Gc<Self>>,
    ctx: Gc<Context>,
    free_variables: GcVec<FreeVariableInfo>,
    free_upvariables: GcVec<FreeVariableInfo>,

    code: GcVec<u8>,

    local_free_variable_count: usize,
    upvalue_count: usize,
    stack_max: usize,
    stack_size: usize,
    locals: usize,

    constants: GcVec<Value>,
    closure: bool,

    name: Value,
    env: Value,

    synclo_env: Value,
    synclo_fv: Value,
}

fn env_qualify_name(ctx: ContextRef, env: Value, name: Value) -> Value {
    let sym = ctx.global(Global::ModuleName);

    let mname = env.hash_get(ctx, sym, Value::empty());
    if mname.is_empty() {
        todo!()
    }
    let name = format!("{}#{}", mname, name);

    let sym = intern(ctx, name);
    sym.set_symbol_module(env);
    sym
}

fn env_globalp(ctx: ContextRef, env: Value) -> bool {
    env.hash_get(ctx, ctx.global(Global::GlobalEnvironment), Value::empty()) != Value::empty()
}

impl Gc<Compiler> {
    pub fn emit(&mut self, code: &[u8]) {
        let mut c = self.ctx;
        self.code.extend_from_slice(c.heap(), code);
    }

    pub fn jump<'a>(&'a mut self) -> impl FnOnce(&mut Self) {
        self.emit(&[Op::Jump as u8]);
        let at = self.code.len();
        self.emit(&[0, 0, 0, 0]);
        move |cc| {
            let target = (cc.code.len() as u32).to_ne_bytes();
            cc.code[at] = target[0];
            cc.code[at + 1] = target[1];
            cc.code[at + 2] = target[2];
            cc.code[at + 3] = target[3];
        }
    }

    pub fn cjump<'a>(&'a mut self, cond: bool) -> impl FnOnce(&mut Self) {
        self.emit(&[Op::Jump as _]);
        let at = self.code.len();
        self.emit(&[0, 0, 0, 0]);
        move |cc| {
            cc.code[at - 1] = if cond {
                Op::JumpIfTrue as u8
            } else {
                Op::JumpIfFalse as u8
            };
            let target = (cc.code.len() as u32).to_ne_bytes();
            cc.code[at] = target[0];
            cc.code[at + 1] = target[1];
            cc.code[at + 2] = target[2];
            cc.code[at + 3] = target[3];
        }
    }

    pub fn strip_syntax(&mut self, exp: Value) -> Value {
        if exp.synclop() {
            return exp.synclo_expr();
        } else if exp.pairp() {
            let car = self.strip_syntax(exp.car());
            let cdr = self.strip_syntax(exp.cdr());
            return make_pair(self.ctx, car, cdr);
        } else {
            exp
        }
    }

    pub fn macro_application(&mut self, exp: Value, state: State, lookup: &Lookup) -> Value {
        let exp = self.strip_syntax(exp);
        let env = self.env;

        let function = if let Lookup::Global { value, .. } = lookup {
            *value
        } else if let Lookup::Local { value, .. } = lookup {
            *value
        } else {
            unreachable!()
        };

        let mut result = apply(self.ctx, function, &[exp, env]);
        if result.exceptionp() {
            return result;
        }
        let mut other_env = function
            .downcast::<Closure>(ValueType::Closure as _)
            .data
            .vector_ref(0);

        std::mem::swap(&mut self.env, &mut other_env);

        result = self.compile(result, state);

        std::mem::swap(&mut self.env, &mut other_env);
        result
    }

    pub fn unify_import(&mut self, name: Value) -> Value {
        let unqualified = self.ctx.global(Global::UnqualifiedImports);
        let exports = self.ctx.global(Global::Exports);

        let mut delegates = self.env.hash_get(self.ctx, unqualified, Value::new_null());

        while delegates.pairp() {
            let module = delegates.car();
            let exports = module.hash_get(self.ctx, exports, Value::new_null());
            let sym = exports.hash_get(self.ctx, name, Value::new_null());

            if !sym.is_null() {
                return sym;
            }
            delegates = delegates.cdr();
        }

        let sym = env_qualify_name(self.ctx, self.env, name);

        sym.set_symbol_module(self.env);
        sym
    }
    pub fn compile_error(&mut self, s: impl AsRef<str>) -> Value {
        let kind = self.ctx.global(Global::ScmCompile);
        let message = make_string(self.ctx, s);

        make_exception(
            self.ctx,
            kind,
            message,
            Value::new_null(),
            Value::new_null(),
            Value::new_null(),
        )
    }

    pub fn syntax_error(&mut self, s: impl AsRef<str>) -> Value {
        let kind = self.ctx.global(Global::ScmRead);
        let message = make_string(self.ctx, s);

        make_exception(
            self.ctx,
            kind,
            message,
            Value::new_null(),
            Value::new_null(),
            Value::new_null(),
        )
    }
    pub fn compile_export(&mut self, mut exp: Value) -> Value {
        let exports = self.ctx.global(Global::Exports);

        let exports = self.env.hash_get(self.ctx, exports, Value::new_null());
        while exp.pairp() {
            let name = exp.car();

            if name.symbolp() {
                let qualified = self.unify_import(name);

                exports.hash_set(self.ctx, name, qualified);
            } else {
                return self.syntax_error(format!("export name must be a symbol, found {}", name));
            }

            exp = exp.cdr();
        }

        Value::new_null()
    }

    pub fn import(&mut self, exp: Value) -> Value {
        let module_name = convert_module_name(self.ctx, exp.cdr());

        let module = self.ctx.load_module(module_name)?;

        let unqualified = self.ctx.global(Global::UnqualifiedImports);

        let env = self.env.hash_get(self.ctx, unqualified, Value::empty());
        if env.is_empty() {
            return self.syntax_error("you can use import only at top-level");
        }

        let env = make_pair(self.ctx, module, env);

        self.env.hash_set(self.ctx, unqualified, env);

        Value::new_null()
    }

    pub fn compile_apply(&mut self, exp: Value, state: State) -> Value {
        let mut args = exp.cdr();
        let mut argc = 0;
        while !args.is_null() {
            self.compile(args.car(), State::USED_NON_FINAL)?;
            argc += 1;
            args = args.cdr();
        }

        self.compile(exp.car(), State::USED_NON_FINAL)?;

        self.emit(&[if state.is_final() {
            Op::TailApply as u8
        } else {
            Op::Apply as u8
        }]);
        self.pop(argc);
        self.pop(1);
        if !state.is_final() {
            self.push(1);
        }
        let mut c = self.ctx;
        self.code
            .extend_from_slice(c.heap(), &(argc as u16).to_ne_bytes());

        Value::new_null()
    }

    pub fn compile_begin(&mut self, exp: Value, state: State) -> Value {
        if exp.is_null() {
            if !state.is_unused() {
                self.emit(&[Op::LoadN as u8]);
                self.push(1);
            }
            return Value::new_null();
        }

        if exp.pairp() {
            if exp.cdr().is_null() {
                self.compile(exp.car(), state)
            } else {
                self.compile(exp.car(), State::USED_NON_FINAL)?;

                self.compile_begin(exp.cdr(), state)
            }
        } else {
            self.syntax_error(format!("malformed begin: {}", exp))
        }
    }
    pub fn compile_define(&mut self, exp: Value) -> Value {
        let rest = self.expect_pair(exp)?;
        if rest.is_null() {
            return self.syntax_error(format!("malformed define: {}", rest));
        }
        let value = rest.cdr();
        let mut lambda = Value::new_null();
        let mut clos = false;

        let symbol = if rest.car().symbolp() {
            self.compile(value.car(), State::USED_NON_FINAL);

            rest.car()
        } else if rest.car().pairp() {
            let lambda_ = rest.car();
            let args = lambda_.cdr();
            let name = self.expect_symbol(lambda_.car())?;

            lambda = self.generate_lambda(name, args, value, &mut clos)?;

            name
        } else {
            return self.syntax_error(format!("define expects symbol or (variable formals)"));
        };
        let val;

        let l;
        if env_globalp(self.ctx, self.env) {
            l = Lookup::Global {
                value: Value::new_null(),
                module: self.env,
            };
            val = symbol;
        } else {
            l = Lookup::Local {
                index: self.locals,
                up: false,
                value: Value::new_i32(self.locals as _),
                level: 0,
            };
            val = Value::new_i32(self.locals as _);
            self.locals += 1;
        };
        self.env_define(self.env, symbol, val, false);
        let lambda = if env_globalp(self.ctx, self.env) {
            lambda
        } else if !lambda.is_null() {
            let ix = self.add_constant(lambda).to_ne_bytes();
            self.emit(&[Op::LoadC as _]);
            let mut c = self.ctx;
            self.code.extend_from_slice(c.heap(), &ix);
            if clos {
                self.emit(&[Op::MakeClosure as _]);
            }
            self.push(1);
            Value::new_null()
        } else {
            // self.compile(value.car(), State::USED_NON_FINAL)
            Value::new_null()
        }?;
        self.generate_set(&l, exp, symbol, lambda);
        Value::new_null()
    }
    pub fn generate_lambda(
        &mut self,
        name: Value,
        mut args: Value,
        body: Value,
        closure: &mut bool,
    ) -> Value {
        let new_env = make_env(self.ctx, self.env, None);
        let mut variable_arity = false;
        let mut argc = 0;
        if args.symbolp() {
            self.env_define(new_env, args, Value::new_i32(argc), false);

            argc += 1;
            variable_arity = true;
        } else if args.pairp() {
            while args.pairp() {
                let arg = args.car();
                if !arg.symbolp() {
                    return self.syntax_error("lambda expects symbol as argument name");
                }

                self.env_define(new_env, arg, Value::new_i32(argc), false);
                argc += 1;
                let rest = args.cdr();

                if rest.symbolp() {
                    self.env_define(new_env, arg, Value::new_i32(argc), false);
                    argc += 1;
                    variable_arity = true;
                    break;
                } else {
                    args = rest;
                }
            }
        } else if args.is_null() {
        } else {
            return self.syntax_error(format!("lambda expects () or symbol, got {}", args));
        }
        self.enter_parent(argc as _, variable_arity, 0, closure, new_env, |mut cc| {
            if !name.is_null() {
                cc.name = name;
            }
            cc.compile_begin(body, State::USED_FINAL)?;
            cc.emit(&[Op::Return as _]);
            Value::new_null()
        })
    }

    pub fn compile(&mut self, exp: Value, state: State) -> Value {
        if exp.pairp() {
            let first = exp.car();
            let rest = exp.cdr();
            let mut syntax = false;
            let mut transformer = Value::new_null();
            let mut lookup = Lookup::Global {
                value: Value::new_null(),
                module: Value::new_null(),
            };
            if first.symbolp() {
                if self.env_lookup(self.env, first, &mut lookup, false) {
                    (transformer, syntax) = self.lookup_syntaxp(&lookup);
                }
            }

            if syntax {
                match first.symbol_name().string_data() {
                    "quote" => {
                        let c = self.add_constant(rest).to_ne_bytes();
                        self.emit(&[Op::LoadC as _]);
                        let mut ct = self.ctx;
                        self.code.extend_from_slice(ct.heap(), &c);
                        self.push(1);
                        return Value::new_null();
                    }
                    "set!" => {
                        self.compile_set(rest)?;
                        if !state.is_unused() {
                            self.emit(&[Op::LoadN as _]);
                            self.push(1);
                        }
                        return Value::new_null();
                    }
                    "begin" => return self.compile_begin(rest, state),
                    "lambda" => {
                        if !state.is_unused() {
                            let lambda = self.expect_pair(rest)?;
                            let args = lambda.car();
                            let body = lambda.cdr();
                            let mut closure = false;
                            let f =
                                self.generate_lambda(Value::new_null(), args, body, &mut closure)?;
                            let x = self.add_constant(f);

                            self.emit(&[Op::LoadC as _]);
                            let mut c = self.ctx;
                            self.code.extend_from_slice(c.heap(), &x.to_ne_bytes());

                            if closure {
                                self.emit(&[Op::MakeClosure as _]);
                            }
                            self.push(1);
                        }
                        return Value::new_null();
                    }
                    "define" => {
                        self.compile_define(rest)?;
                        if !state.is_unused() {
                            self.emit(&[Op::LoadN as _]);
                            self.push(1);
                        }
                        return Value::new_null();
                    }
                    "%define-syntax" => {
                        self.compile_define_syntax(exp, state)?;
                        if !state.is_unused() {
                            self.emit(&[Op::LoadN as _]);
                            self.push(1);
                        }
                        return Value::new_null();
                    }
                    "if" => {
                        return self.compile_if(exp.cdr(), state);
                    }
                    "export" => {
                        self.compile_export(exp.cdr());
                        return Value::new_null();
                    }
                    _ if !transformer.is_null() => {
                        return self.compile_macro_application(
                            transformer,
                            exp.cdr(),
                            state,
                            &lookup,
                        )
                    }
                    _ => (),
                }
            }

            self.compile_apply(exp, state)?;
        } else if exp.symbolp() {
            self.compile_ref(exp)?;
        } else if exp.vectorp() {
            let sym = intern(self.ctx, "#waffle#core#vector");

            for i in 0..exp.vector_length() {
                let exp = exp.vector_ref(i);
                self.compile(exp, State::USED_NON_FINAL)?;
            }
            let ix = self.add_constant(sym).to_ne_bytes();
            self.emit(&[Op::GlobalRef as _, ix[0], ix[1]]);
            if state.is_final() {
                self.emit(&[Op::TailApply as _]);
            } else {
                self.emit(&[Op::Apply as _]);
            }
            let mut c = self.ctx;
            self.code
                .extend_from_slice(c.heap(), &(exp.vector_length() as u16).to_ne_bytes());
            self.pop(exp.vector_length());
            self.push(1);
            if state.is_unused() {
                self.emit(&[Op::Pop as _]);
                self.pop(1);
            }
        } else if exp.synclop() {
            let mut senv = exp.synclo_env();
            let expr = exp.synclo_expr();

            let mut vars = list_copy(self.ctx, exp.synclo_vars());
            std::mem::swap(&mut senv, &mut self.synclo_env);
            std::mem::swap(&mut vars, &mut self.synclo_fv);

            let chk = self.compile(expr, state);
            std::mem::swap(&mut senv, &mut self.synclo_env);
            std::mem::swap(&mut vars, &mut self.synclo_fv);
            return chk;
        } else {
            if !state.is_unused() {
                if exp.is_int32() {
                    let b = exp.as_int32().to_ne_bytes();
                    self.emit(&[Op::LoadI as _, b[0], b[1], b[2], b[3]]);
                } else if exp.is_double() {
                    self.emit(&[Op::LoadF as _]);
                    let b = exp.as_double().to_bits().to_ne_bytes();
                    let mut ct = self.ctx;
                    self.code.extend_from_slice(ct.heap(), &b);
                } else {
                    let ix = self.add_constant(exp).to_ne_bytes();
                    self.emit(&[Op::LoadC as _, ix[0], ix[1]]);
                }
                self.push(1);
            }
        }
        Value::new_null()
    }

    pub fn compile_define_syntax(&mut self, exp: Value, _state: State) -> Value {
        let exp = exp.cdr();
        let name = exp.car().car();
        let expr_name = exp.car().cdr().car();
        let env_name = exp.car().cdr().cdr().car();
        let macro_env_name = exp.car().cdr().cdr().cdr().car();

        let body = exp.cdr();

        let args = make_pair(self.ctx, macro_env_name, Value::new_null());
        let args = make_pair(self.ctx, env_name, args);
        let args = make_pair(self.ctx, expr_name, args);

        let mut clos = false;

        let transformer = self.generate_lambda(name, args, body, &mut clos)?;
        let clos = make_vector(self.ctx, 2, Value::new_null());
        clos.vector_set(0, self.env);
        clos.vector_set(1, transformer);

        let apply_macro = self.ctx.heap().allocate_tagged(
            NativeProcedure {
                closure: clos,
                callback: apply_macro,
                variable: true,
                argc: 0,
                macrop: true,
                name,
            },
            ValueType::NativeFunction as _,
            false,
            false,
        );

        self.env_define(self.env, name, Value::new_cell(apply_macro), false);
        if env_globalp(self.ctx, self.env) {
            let qualified = env_qualify_name(self.ctx, self.env, name);

            qualified.set_symbol_value(Value::new_cell(apply_macro));
        }
        Value::new_null()
    }

    fn check_macro(&self, val: Value) -> (Value, bool) {
        if val.nativep() {
            let x = val.downcast::<NativeProcedure>(ValueType::NativeFunction as _);
            if x.macrop {
                (val, true)
            } else {
                (Value::new_null(), false)
            }
        } else if val.symbolp() {
            self.check_macro(val.symbol_value())
        } else {
            (Value::new_null(), false)
        }
    }
    pub fn lookup_syntaxp(&self, l: &Lookup) -> (Value, bool) {
        match l {
            Lookup::Local { value, .. } => (Value::new_null(), value.applicablep()),
            Lookup::Global { value, .. } => {
                if *value == self.ctx.global(Global::Special) {
                    (*value, true)
                } else {
                    self.check_macro(*value)
                }
            }
        }
    }

    pub fn compile_if(&mut self, exp: Value, state: State) -> Value {
        let exp = self.expect_pair(exp)?;
        let cond = exp.car();
        let then_and_else = self.expect_pair(exp.cdr())?;
        let else_ = self.expect_pair(then_and_else.cdr())?.car();
        let then = then_and_else.car();

        self.compile(cond, State::USED_NON_FINAL);
        self.pop(1);
        let cjmp = self.cjump(false);
        self.compile(then, state)?;
        let jmp = self.jump();
        cjmp(self);
        self.compile(else_, state)?;
        jmp(self);
        Value::new_null()
    }

    pub fn compile_macro_application(
        &mut self,
        transformer: Value,
        exp: Value,
        state: State,
        _lookup: &Lookup,
    ) -> Value {
        let function = transformer;
        let first = self.strip_syntax(exp);

        let second = self.env;
        let result = apply(self.ctx, function, &[first, second])?;
        println!("=> {}", result);
        let mut other_env = function
            .downcast::<NativeProcedure>(ValueType::NativeFunction as _)
            .closure
            .vector_ref(0);
        std::mem::swap(&mut self.env, &mut other_env);
        let result = self.compile(result, state);
        std::mem::swap(&mut self.env, &mut other_env);

        result
    }

    pub fn enter_parent(
        &mut self,
        argument_count: usize,
        variable_arity: bool,
        nlocals: usize,
        is_closure: &mut bool,
        new_env: Value,
        mut clos: impl FnMut(Gc<Compiler>) -> Value,
    ) -> Value {
        let mut subcompiler = Compiler::new(self.ctx, new_env);
        subcompiler.locals += argument_count + nlocals;
        subcompiler.parent = Some(*self);
        clos(subcompiler)?;
        *is_closure = subcompiler.closure;
        subcompiler.end(argument_count, variable_arity)
    }

    pub fn end(&mut self, arguments: usize, variable_arity: bool) -> Value {
        let code = make_bytes(self.ctx, &self.code);

        let local_free_vars = make_bytes2(
            self.ctx,
            size_of::<usize>() * self.local_free_variable_count,
            0,
        );
        let upvals = make_bytes2(
            self.ctx,
            self.free_upvariables.len() * size_of::<UpvalLoc>(),
            0,
        );

        let mut freevar_i = 0;
        let mut upvar_i = 0;

        for i in 0..self.free_variables.len() {
            if self.free_variables[i].lexical_level == 0 {
                local_free_vars.bvector_set::<usize>(freevar_i, self.free_variables[i].index);
                freevar_i += 1;
            } else {
                unreachable!()
            }
        }

        for i in 0..self.free_upvariables.len() {
            let l = UpvalLoc {
                local: self.free_upvariables[i].lexical_level == 1,
                index: self.free_upvariables[i].index as _,
            };
            upvals.bvector_set(upvar_i, l);
            upvar_i += 1;
        }

        let constants = make_vector(self.ctx, self.constants.len(), Value::new_null());
        for (i, c) in self.constants.iter().enumerate() {
            constants.vector_set(i, *c);
        }
        let mut c = self.ctx;
        let p = c.heap().allocate_tagged(
            Procedure {
                constants,
                local_free_variable_count: self.local_free_variable_count as _,
                local_free_variables: local_free_vars,
                upvalues: upvals,
                arguments: arguments as _,
                variable_arity,
                code,
                name: self.name,
                stack_max: self.stack_max as _,
                locals: self.locals as _,
            },
            ValueType::Function as _,
            false,
            false,
        );
        //   println!("{}", disasm(self.ctx, Value::new_cell(p)));
        Value::new_cell(p)
    }

    pub fn env_define(&mut self, table: Value, key: Value, value: Value, exported: bool) {
        if !self.synclo_fv.is_null() && memq(self.synclo_fv, key) {
            let lst = list_copy(self.ctx, self.synclo_fv);
            let lst = remove_memq(self.ctx, lst, key);
            self.synclo_fv = lst;
        }

        env_define(self.ctx, table, key, value, exported);
    }

    pub fn env_lookup(
        &mut self,
        mut env: Value,
        key: Value,
        lookup: &mut Lookup,
        search_exports: bool,
    ) -> bool {
        if self.env == env {
            if !self.synclo_env.is_null() {
                if !(self.synclo_fv.pairp() && memq(self.synclo_fv, key)) {
                    env = self.synclo_env;
                }
            }
        }

        let start_env = env;
        let mut level = 0;
        while env.hashtablep() {
            let cell = env.hash_get(self.ctx, key, Value::empty());

            if !cell.is_empty() {
                if env_globalp(self.ctx, env) {
                    *lookup = Lookup::Global {
                        value: cell,
                        module: if search_exports {
                            let env = env.hash_get(
                                self.ctx,
                                self.ctx.global(Global::ExportParent),
                                Value::new_null(),
                            );
                            if cell.symbolp() {
                                if !cell.symbol_module().is_null() {
                                    cell.symbol_module()
                                } else {
                                    env
                                }
                            } else {
                                env
                            }
                        } else {
                            if cell.symbolp() {
                                if !cell.symbol_module().is_null() {
                                    cell.symbol_module()
                                } else {
                                    env
                                }
                            } else {
                                env
                            }
                        },
                    };
                    return true;
                } else {
                    *lookup = Lookup::Local {
                        index: if cell.is_int32() {
                            cell.as_int32() as _
                        } else {
                            0
                        },
                        value: cell,
                        up: env != start_env,
                        level,
                    };
                    return true;
                }
            }

            level += 1;

            let parent = env.hash_get(self.ctx, self.ctx.global(Global::Parent), Value::new_null());
            if !parent.is_null() {
                env = parent;
                continue;
            }
            break;
        }

        let mut imports = env.hash_get(
            self.ctx,
            self.ctx.global(Global::UnqualifiedImports),
            Value::new_null(),
        );
        if !imports.is_null() {
            while imports.pairp() {
                let module = imports.car();
                let exports =
                    module.hash_get(self.ctx, self.ctx.global(Global::Exports), Value::empty());
                let res = self.env_lookup(exports, key, lookup, true);
                if res {
                    return true;
                }
                imports = imports.cdr();
            }
        }

        false
    }
    pub fn add_constant(&mut self, constant: Value) -> u16 {
        for (i, c) in self.constants.iter().enumerate() {
            if *c == constant {
                return i as _;
            }
        }
        let ix = self.constants.len();
        let mut ctx = self.ctx;
        self.constants.push(ctx.heap(), constant);
        ix as _
    }

    pub fn generate_ref(&mut self, lookup: &Lookup, _exp: Value, name: Value) {
        match *lookup {
            Lookup::Global { module, .. } => {
                let tmp = env_qualify_name(self.ctx, module, name);
                let c = self.add_constant(tmp).to_ne_bytes();
                self.emit(&[Op::GlobalRef as u8, c[0], c[1]]);
            }

            Lookup::Local { index, up, .. } => {
                let ix = (index as u16).to_ne_bytes();
                if !up {
                    self.emit(&[Op::LocalRef as _, ix[0], ix[1]])
                } else {
                    let index = self.register_free_variable(lookup, name) as u16;
                    let ix = index.to_ne_bytes();
                    self.emit(&[Op::ClosureRef as _, ix[0], ix[1]]);
                }
            }
        }
        self.push(1);
    }

    pub fn generate_set(&mut self, lookup: &Lookup, _exp: Value, name: Value, comptime_set: Value) {
        match *lookup {
            Lookup::Global { module, .. } => {
                let tmp = env_qualify_name(self.ctx, module, name);

                if !comptime_set.is_null() {
                    tmp.set_symbol_value(comptime_set);
                } else {
                    let c = self.add_constant(tmp).to_ne_bytes();
                    self.emit(&[Op::GlobalSet as u8, c[0], c[1]]);
                    self.pop(1);
                }
            }

            Lookup::Local { index, up, .. } => {
                let ix = (index as u16).to_ne_bytes();
                if !up {
                    self.emit(&[Op::LocalSet as _, ix[0], ix[1]])
                } else {
                    let index = self.register_free_variable(lookup, name) as u16;
                    let ix = index.to_ne_bytes();
                    self.emit(&[Op::ClosureSet as _, ix[0], ix[1]]);
                }
                self.pop(1);
            }
        }
    }

    pub fn compile_ref(&mut self, exp: Value) -> Value {
        let mut lookup = Lookup::Local {
            index: 0,
            level: 0,
            up: false,
            value: exp,
        };

        if !self.env_lookup(self.env, exp, &mut lookup, false) {
            return self.syntax_error(format!("undefined variable '{}' in {}", exp, self.env));
        }
        self.generate_ref(&lookup, exp, exp);
        Value::new_null()
    }

    pub fn compile_set(&mut self, exp: Value) -> Value {
        let rest = self.expect_pair(exp)?;
        let name = self.expect_symbol(rest.car())?;
        let value = self.expect_pair(rest.cdr()).car();

        self.compile(value, State::USED_NON_FINAL)?;

        let mut lookup = Lookup::Local {
            index: 0,
            level: 0,
            up: false,
            value: exp,
        };

        if !self.env_lookup(self.env, name, &mut lookup, false) {
            return self.syntax_error(format!("undefiend variable '{}'", name));
        }

        self.generate_set(&lookup, exp, name, Value::new_null());
        Value::new_null()
    }

    pub fn expect_pair(&mut self, exp: Value) -> Value {
        if exp.pairp() {
            return exp;
        }
        self.syntax_error(format!("pair expected but found {}", exp))
    }

    pub fn expect_symbol(&mut self, exp: Value) -> Value {
        if exp.symbolp() {
            return exp;
        }
        self.syntax_error(format!("symbol expected but found {}", exp))
    }

    pub fn push(&mut self, x: usize) {
        self.stack_size += x;
        self.stack_max = self.stack_max.max(self.stack_size);
    }

    pub fn pop(&mut self, x: usize) {
        self.stack_size = self.stack_size.checked_sub(x).expect("stack underflow");
    }
    pub fn compute_globals_in_begin(&mut self, exp: &mut Value) -> Value {
        if exp.is_null() {
            return Value::new_null();
        }
        if exp.pairp() {
            if exp.cdr().is_null() {
                self.compute_globals(exp.car_mut())?;
            } else {
                self.compute_globals(exp.car_mut())?;
                self.compute_globals_in_begin(exp.cdr_mut());
            }
        } else {
            return self.syntax_error(&format!(
                "Unexpected value passed to begin block instead of a cons: {}",
                exp
            ));
        }
        Value::new_null()
    }

    pub fn enter_module(&mut self, name: Value) -> Value {
        if self.ctx.module_loaded(name) {
            self.env = self.ctx.load_module(name);
            return Value::new_null();
        }

        let menv = make_env(
            self.ctx,
            self.ctx.core_module,
            if name.is_null() {
                None
            } else {
                Some(name.string_data())
            },
        );

        self.ctx.register_module(name, menv);
        self.env = menv;
        Value::new_null()
    }
    pub fn compute_globals(&mut self, exp: &mut Value) -> Value {
        let cexp = *exp;
        match cexp {
            x if x.pairp() => match x.car() {
                x if x.symbolp() => match x.symbol_name().string_data() {
                    "import" => {
                        self.import(cexp);
                        Value::new_bool(false)
                    }
                    "export" => Value::new_bool(true),
                    "module" => {
                        let name = convert_module_name(self.ctx, cexp.cdr());
                        self.enter_module(name)?;
                        Value::new_bool(false)
                    }
                    "," => {
                        let value = make_pair(self.ctx, intern(self.ctx, "unquote"), cexp.cdr());
                        *exp = value;
                        Value::new_bool(true)
                    }
                    ",@" => {
                        let value =
                            make_pair(self.ctx, intern(self.ctx, "unquote-splicing"), cexp.cdr());
                        *exp = value;
                        Value::new_bool(true)
                    }
                    "`" => {
                        let value = make_pair(self.ctx, intern(self.ctx, "quasiquote"), cexp.cdr());
                        *exp = value;
                        Value::new_bool(true)
                    }

                    "'" => {
                        let value = make_pair(self.ctx, intern(self.ctx, "quote"), cexp.cdr());
                        *exp = value;
                        Value::new_bool(true)
                    }
                    "begin" => self.compute_globals_in_begin(exp.cdr_mut()),
                    "define" => {
                        let rest = self.expect_pair(cexp.cdr())?;

                        let name = if rest.car().symbolp() {
                            self.expect_symbol(rest.car())?
                        } else if rest.car().pairp() {
                            self.expect_symbol(rest.car().car())?
                        } else {
                            return self.syntax_error("malformed define: expected name");
                        };

                        self.env_define(self.env, name, name, false);

                        Value::new_bool(true)
                    }

                    "%define-syntax" => {
                        let rest = self.expect_pair(cexp.cdr())?;
                        let p = self.expect_pair(rest.car())?;

                        let name = self.expect_symbol(p.car())?;

                        self.env_define(self.env, name, name, false);
                        Value::new_bool(true)
                    }

                    _ => Value::new_bool(true),
                },
                _ => Value::new_bool(true),
            },
            _ => Value::new_bool(true),
        }
    }
    pub fn clear(&mut self) {
        self.locals = 0;
        self.upvalue_count = 0;
        self.free_upvariables.clear();
        self.free_variables.clear();
        self.synclo_env = Value::new_null();
        self.synclo_fv = Value::new_null();
        self.stack_max = 0;
        self.stack_size = 0;
        self.constants.clear();
        self.closure = false;
        self.name = Value::new_null();
    }
    pub fn compile_code<'a, R>(&mut self, mut p: lexpr::Parser<R>) -> Value
    where
        R: lexpr::parse::Read<'a>,
    {
        let mut code = GcVec::with_capacity(self.ctx.heap(), 4);

        loop {
            let next = p.next();
            match next {
                Some(res) => match res {
                    Ok(val) => {
                        let mut exp = crate::sexp::lexpr_to_sexp(self.ctx, &val);

                        if self.compute_globals(&mut exp)?.as_boolean() {
                            code.push(self.ctx.heap(), exp);
                        }
                    }
                    Err(e) => {
                        return self.syntax_error(format!("failed to parse code: {}", e));
                    }
                },
                None => break,
            }
        }
        for (i, x) in code.iter().enumerate() {
            let last = i == code.len() - 1;
            self.compile(
                *x,
                if last {
                    State::USED_FINAL
                } else {
                    State::NOT_USED_NON_FINAL
                },
            )?;
        }
        self.emit(&[Op::Return as _]);
        self.end(0, false)
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
            let mut ctx = self.ctx;
            if l.lexical_level != 0 {
                match &mut lookup_copy {
                    Lookup::Local { level, .. } => *level -= 1,
                    _ => unreachable!(),
                }

                self.closure = true;

                l.index =
                    (self.parent.as_mut().unwrap()).register_free_variable(&lookup_copy, name);

                self.upvalue_count += 1;
                self.free_upvariables.push(ctx.heap(), l);
                self.free_upvariables.len() - 1
            } else {
                l.index = l.lexical_index;
                self.local_free_variable_count += 1;
                self.free_variables.push(ctx.heap(), l);
                self.free_variables.len() - 1
            }
        } else {
            unreachable!()
        }
    }
}

impl Compiler {
    pub fn new(mut ctx: ContextRef, env: Value) -> Gc<Self> {
        let c = ctx;
        let constants = GcVec::with_capacity(ctx.heap(), 4);
        let free_upvariables = GcVec::new(ctx.heap());
        let free_variables = GcVec::new(ctx.heap());
        let code = GcVec::new(ctx.heap());
        let cc = ctx.heap().allocate_tagged(
            Self {
                parent: None,
                ctx: c,
                local_free_variable_count: 0,
                locals: 0,
                free_upvariables,
                free_variables,
                constants,
                env: if env.is_null() { c.core_module } else { env },
                synclo_fv: Value::new_null(),
                stack_max: 0,
                stack_size: 0,
                synclo_env: Value::new_null(),
                code,
                upvalue_count: 0,
                closure: false,
                name: Value::new_null(),
            },
            ValueType::Compiler as _,
            false,
            false,
        );
        unsafe {
            //   ctx.heap().add_drop(cc);
        }
        cc
    }
}

fn apply_macro(ctx: ContextRef, args: &[Value], closure: Value) -> CallResult {
    let macro_env = closure.vector_ref(0);
    let transformer = closure.vector_ref(1);
    let exp = args[0];
    let other_env = args[1];
    //  println!("MACRO ENV {}\nUSE ENV {}", macro_env, other_env);
    let res = apply(ctx, transformer, &[exp, other_env, macro_env]);

    CallResult::Done(res)
}

pub fn defun(mut ctx: ContextRef, name: &str, p: NativeCallback, arguments: usize, variable: bool) {
    let name = intern(ctx, name);
    let f = ctx.heap().allocate_tagged(
        NativeProcedure {
            callback: p,
            name,
            variable,
            argc: arguments,
            macrop: false,
            closure: Value::new_null(),
        },
        ValueType::NativeFunction as _,
        false,
        false,
    );
    env_define(ctx, ctx.core_module, name, name, true);

    let qualified = env_qualify_name(ctx, ctx.core_module, name);
    qualified.set_symbol_value(Value::new_cell(f));
}

pub fn type_error(ctx: ContextRef, in_: &str, pos: u32, expected: &str, found: Value) -> Value {
    let kind = ctx.global(Global::ScmEval);
    let message = make_string(
        ctx,
        format!(
            "in procedure {}: Wrong type argument in position {} (expecting {}): {}",
            in_, pos, expected, found
        ),
    );

    make_exception(
        ctx,
        kind,
        message,
        Value::new_null(),
        Value::new_null(),
        Value::new_null(),
    )
}

pub(crate) fn init_primitives(ctx: ContextRef) {
    defun(
        ctx,
        "pair?",
        |_, args, _| CallResult::Done(Value::new_bool(args[0].pairp())),
        1,
        false,
    );

    defun(
        ctx,
        "car",
        |ctx, args, _| {
            CallResult::Done(if args[0].pairp() {
                args[0].car()
            } else {
                type_error(ctx, "car", 1, "pair", args[0])
            })
        },
        1,
        false,
    );

    defun(
        ctx,
        "cdr",
        |ctx, args, _| {
            CallResult::Done(if args[0].pairp() {
                args[0].cdr()
            } else {
                type_error(ctx, "cdr", 1, "pair", args[0])
            })
        },
        1,
        false,
    );

    /* defun(
        ctx,
        "list",
        |ctx, args, _| CallResult::Done(make_list(ctx, args)),
        0,
        true,
    );*/

    defun(
        ctx,
        "null?",
        |_, args, _| CallResult::Done(Value::new_bool(args[0].is_null())),
        1,
        false,
    );

    defun(
        ctx,
        "eq?",
        |_, args, _| CallResult::Done(Value::new_bool(args[0] == args[1])),
        2,
        false,
    );
    defun(
        ctx,
        "equal?",
        |_, args, _| CallResult::Done(Value::new_bool(r5rs_equal_pred(args[0], args[1]))),
        2,
        false,
    );

    defun(
        ctx,
        "print",
        |_, args, _| {
            for (i, arg) in args.iter().enumerate() {
                print!("{}", arg);
                if i != args.len() - 1 {
                    print!(" ");
                }
            }
            println!();
            CallResult::Done(Value::new_null())
        },
        0,
        true,
    );

    defun(
        ctx,
        "synclo",
        |ctx, args, _| {
            let env = args[0];
            let expr = args[1];
            let vars = if args.len() > 2 {
                args[2]
            } else {
                Value::new_null()
            };

            if !env.hashtablep() {
                return CallResult::Done(type_error(ctx, "synclo", 1, "hashtable", env));
            }
            let vars = if vars.is_null() {
                vars
            } else {
                if !listp(vars) {
                    return CallResult::Done(type_error(ctx, "synclo", 3, "list", vars));
                }
                list_copy(ctx, vars)
            };
            let synclo = make_synclo(ctx, env, vars, expr);
            CallResult::Done(synclo)
        },
        2,
        false,
    );

    defun(
        ctx,
        "make-syntactic-closure",
        |ctx, args, _| {
            let env = args[0];
            let fv = args[1];
            let expr = args[2];

            CallResult::Done(make_synclo(ctx, env, fv, expr))
        },
        3,
        false,
    );
}
