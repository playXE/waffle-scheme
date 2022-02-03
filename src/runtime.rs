use self::{
    value::{
        Macro, NativeCallback, NativeFunction, Null, ScmBignum, ScmBlob, ScmBox, ScmComplex,
        ScmCons, ScmException, ScmPrototype, ScmRational, ScmString, ScmSymbol, ScmTable,
        ScmVector, Value,
    },
    vm::Frame,
};
use crate::{
    compiler::{make_env, Compiler},
    init::enable_core,
    jit::{compile_thread, Jit},
    runtime::value::Closure,
    Heap, Managed,
};
use comet::{
    api::Trace,
    gc_base::{AllocationSpace, MarkingConstraint},
    letroot,
    mutator::{JoinData, MutatorRef},
};

use comet_extra::alloc::{array::Array, hash::HashMap, string::String, vector::Vector};
use std::{
    mem::size_of,
    ops::{Deref, DerefMut},
    ptr::{null_mut, NonNull},
    sync::atomic::{AtomicBool, AtomicU64},
};

pub mod arith;
//pub mod interpreter;
pub mod subr_arith;
pub mod threading;
pub mod value;
pub mod vm;
#[repr(C)]
pub struct SchemeThread {
    pub(crate) current_frame: *mut Frame,
    pub mutator: MutatorRef<Heap>,
    pub runtime: Runtime,
    pub(crate) trampoline_arguments: Vec<Value>,
    pub(crate) trampoline_fn: Value,

    pub(crate) sp: *mut Value,
    pub(crate) end: *mut Value,
    pub(crate) stack: Box<[Value]>,

    pub(crate) rc: u32,
}

pub struct SchemeThreadRef {
    pub(crate) ptr: NonNull<SchemeThread>,
}

impl SchemeThreadRef {}

impl Deref for SchemeThreadRef {
    type Target = SchemeThread;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr.as_ptr() }
    }
}

impl DerefMut for SchemeThreadRef {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.ptr.as_ptr() }
    }
}

impl Drop for SchemeThreadRef {
    fn drop(&mut self) {
        self.rc -= 1;
        if self.rc == 0 {
            unsafe {
                std::ptr::drop_in_place(self.ptr.as_ptr());
            }
        }
    }
}
impl Clone for SchemeThreadRef {
    fn clone(&self) -> Self {
        unsafe {
            (*self.ptr.as_ptr()).rc += 1;
        }
        Self { ptr: self.ptr }
    }
}

unsafe impl Trace for SchemeThread {
    fn trace(&mut self, vis: &mut dyn comet::api::Visitor) {
        self.trampoline_arguments.trace(vis);
        self.trampoline_fn.trace(vis);
        unsafe {
            let mut frame = self.current_frame;
            while !frame.is_null() {
                (*frame).trace(vis);
                frame = (*frame).prev;
            }
        }
    }
}
use parking_lot::{lock_api::RawMutex, Condvar, Mutex, RawMutex as Lock};
#[allow(dead_code)]
pub(crate) struct RtInner {
    pub(crate) core_module: Option<Managed<ScmTable>>,
    pub(crate) user_module: Option<Managed<ScmTable>>,
    pub(crate) symbol_table: Option<Managed<ScmTable>>,
    pub(crate) modules: Option<Managed<ScmTable>>,
    pub(crate) globals: Vec<Managed<ScmSymbol>>,
    pub(crate) module_search_paths: Vec<std::string::String>,
    pub(crate) qualified_imports: Vec<Value>,
    pub(crate) threads: Vec<SchemeThreadRef>,
    pub(crate) global_lock: Lock,
    pub(crate) dump_bytecode: bool,

    pub(crate) compile_queue_wake: Condvar,
    pub(crate) compile_queue: Mutex<Vec<Managed<ScmPrototype>>>,
    pub(crate) compile_thread_terminating: AtomicBool,
    pub(crate) compile_thread_handle: Option<JoinData>,
    pub(crate) dump_jit: bool,
    pub(crate) jit: Jit,
    pub(crate) hotness: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Runtime {
    inner: NonNull<RtInner>,
}

unsafe impl Send for Runtime {}

impl Runtime {
    pub fn with_modules<R>(&self, mut cb: impl FnMut(&mut Managed<ScmTable>) -> R) -> R {
        let rt = self.inner();

        rt.global_lock.lock();
        let ret = cb(rt.modules.as_mut().unwrap());
        unsafe {
            rt.global_lock.unlock();
        }
        ret
    }
}

struct MarkRt(NonNull<RtInner>);

unsafe impl MarkingConstraint for MarkRt {
    fn name(&self) -> &str {
        "mark-runtime"
    }
    fn is_over(&self) -> bool {
        false
    }
    fn runs_at(&self) -> comet::gc_base::MarkingConstraintRuns {
        comet::gc_base::MarkingConstraintRuns::BeforeMark
    }
    fn run(&mut self, vis: &mut dyn comet::api::Visitor) {
        unsafe {
            let rt = &mut *self.0.as_ptr();
            rt.core_module.trace(vis);
            rt.globals.iter_mut().for_each(|x| x.trace(vis));
            rt.user_module.trace(vis);
            rt.symbol_table.trace(vis);
            rt.modules.trace(vis);
            rt.qualified_imports.trace(vis);
            rt.threads.iter_mut().for_each(|thread| {
                thread.trace(vis);
            });
            // very unsafe, be acqurate with this
            rt.compile_queue.get_mut().trace(vis);
        }
    }
}

impl Runtime {
    pub fn new(
        heap: MutatorRef<Heap>,
        dump_bytecode: bool,
        dump_jit: bool,
        hotness: usize,
    ) -> SchemeThreadRef {
        let rt = Runtime {
            inner: NonNull::new(Box::into_raw(Box::new(RtInner {
                core_module: None,
                user_module: None,
                symbol_table: None,
                globals: vec![],
                compile_queue_wake: Condvar::new(),
                qualified_imports: vec![],
                module_search_paths: vec![],
                threads: vec![],
                compile_queue: Mutex::new(vec![]),
                modules: None,
                dump_bytecode,
                compile_thread_terminating: AtomicBool::new(false),
                compile_thread_handle: None,
                dump_jit,
                jit: Jit::new(),
                global_lock: Lock::INIT,
                hotness,
            })))
            .unwrap(),
        };
        let mut thread = SchemeThreadRef {
            ptr: NonNull::new(Box::into_raw(Box::new(SchemeThread {
                runtime: rt,
                mutator: heap.clone(),
                current_frame: null_mut(),
                trampoline_arguments: vec![],
                trampoline_fn: Value::encode_null_value(),
                rc: 1,
                sp: null_mut(),
                stack: vec![Value::encode_undefined_value(); 8192].into_boxed_slice(),
                end: null_mut(),
            })))
            .unwrap(),
        };
        thread.sp = &mut thread.stack[0];
        let at = thread.stack.len() - 1;
        thread.end = &mut thread.stack[at];
        rt.inner().threads.push(thread.clone());
        rt.inner().symbol_table = Some(make_table(&mut thread, 8));
        for sym in GLOBAL_SYMBOLS.iter() {
            let v = make_symbol(&mut thread, sym);
            rt.inner().globals.push(v);
        }
        rt.inner().core_module = Some(make_env(
            &mut thread,
            Value::new(Null),
            Some("#waffle#core"),
        ));
        rt.inner().user_module = Some(make_env(
            &mut thread,
            Value::new(rt.inner().core_module.unwrap()),
            Some("#user"),
        ));
        rt.inner().modules = Some(make_table(&mut thread, 4));
        register_module(
            &mut thread,
            "#waffle#core",
            Value::new(rt.inner().core_module.unwrap()),
        )
        .unwrap_or_else(|_| unreachable!());
        register_module(
            &mut thread,
            "#user",
            Value::new(rt.inner().user_module.unwrap()),
        )
        .unwrap_or_else(|_| unreachable!());

        let mark = MarkRt(rt.inner);
        thread.mutator.add_constraint(mark);
        let rt2 = rt;
        rt.inner().compile_thread_handle = Some(thread.mutator.spawn_mutator(move |mutator| {
            compile_thread(mutator, rt2);
        }));
        enable_core(&mut thread);
        thread
    }

    pub fn terminate(rt: Self, mutator: &MutatorRef<Heap>) {
        let inner = rt.inner();
        inner
            .compile_thread_terminating
            .store(true, std::sync::atomic::Ordering::Release);
        inner.compile_queue_wake.notify_all();
        inner.compile_thread_handle.take().unwrap().join(mutator);
    }
}

pub(crate) static ID: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Global {
    Special = 0,
    Variable,
    Upvalue,
    Parent,
    UnqualifiedImports,
    QualifiedImports,
    ModuleName,
    GlobalEnvironment,
    Exports,
    Exporting,
    ExportParent,
    ScmRead,
    ScmCompile,
    ScmEval,
    ScmTable,
    ScmType,

    Access,
    Set,
    Lambda,
    If,
    Defmacro,
    Module,
    Quote,
    Import,
    Public,
    Private,
    Export,
    Begin,

    Asterisk,
    GlobalCount,
}

pub const GLOBAL_SYMBOLS: &'static [&'static str] = &[
    "special",
    "variable",
    "upvalue",
    "#parent",
    "#unqualified-imports",
    "#qualified-imports",
    "#module-name",
    "#global-environment",
    "#exports",
    "#exporting",
    "#export-parent",
    "read",
    "compile",
    "eval",
    "table",
    "type",
    "access",
    "set",
    "lambda",
    "if",
    "defmacro",
    "module",
    "quote",
    "import",
    "public",
    "private",
    "export",
    "begin",
    "*",
];

impl Runtime {
    pub(crate) fn inner(&self) -> &mut RtInner {
        unsafe { &mut *self.inner.as_ptr() }
    }
    pub fn global_symbol(&self, g: Global) -> Managed<ScmSymbol> {
        self.inner().globals[g as usize]
    }

    pub fn make_symbol(
        &self,
        thread: &mut SchemeThread,
        string: Managed<ScmString>,
    ) -> Managed<ScmSymbol> {
        let sym;
        let rt = self.inner();
        rt.global_lock.lock();
        unsafe {
            // check if symbol is already interned
            if let Some(s) = rt
                .symbol_table
                .unwrap_unchecked()
                .get(Value::encode_object_value(string))
            {
                sym = s.downcast(); // success! Symbol already exists
            } else {
                // woops, symbol not yet interned. Allocate string copy because our strings are mutable
                let cpy = ScmString::new(&mut thread.mutator, string.to_string());
                // allocate symbol itself
                sym = thread.mutator.allocate(
                    ScmSymbol {
                        name: cpy,
                        mutable: true,
                        value: Value::encode_null_value(),
                        id: ID.fetch_add(1, std::sync::atomic::Ordering::AcqRel), // new unique id for our symbol
                    },
                    AllocationSpace::New,
                );
                // insert symbol into symbol table
                rt.symbol_table.unwrap_unchecked().set(
                    thread,
                    Value::new(cpy),
                    Value::encode_object_value(sym),
                );
            }

            rt.global_lock.unlock();
        }
        sym
    }
}

pub fn make_symbol(thread: &mut SchemeThread, string: impl AsRef<str>) -> Managed<ScmSymbol> {
    let string = make_string(thread, string);
    let rt = thread.runtime;
    rt.make_symbol(thread, string)
}

pub fn make_box(thread: &mut SchemeThread, val: Value) -> Managed<ScmBox> {
    thread
        .mutator
        .allocate(ScmBox { value: val }, AllocationSpace::New)
}

pub fn cons(thread: &mut SchemeThread, car: Value, cdr: Value) -> Managed<ScmCons> {
    thread
        .mutator
        .allocate(ScmCons { car, cdr }, AllocationSpace::New)
}

pub fn make_vector(thread: &mut SchemeThread, mut capacity: usize) -> Managed<ScmVector> {
    if capacity < 2 {
        capacity = 2;
    }
    let v = Vector::with_capacity(&mut thread.mutator, capacity);
    thread
        .mutator
        .allocate(ScmVector { vec: v }, AllocationSpace::New)
}
pub fn make_exception(
    thread: &mut SchemeThread,
    tag: Managed<ScmSymbol>,
    message: Managed<ScmString>,
    irritants: Value,
) -> Managed<ScmException> {
    thread.mutator.allocate(
        ScmException {
            tag,
            irritants,
            message,
        },
        AllocationSpace::New,
    )
}

pub fn list_copy(thread: &mut SchemeThread, lst: Value) -> Managed<ScmCons> {
    let mut lst = lst;
    let mut lst2head = Value::encode_null_value();
    let mut lst2tail = Value::encode_null_value();

    while lst.consp() {
        append_m(thread, &mut lst2head, &mut lst2tail, lst.car());
        lst = lst.cdr();
    }
    lst2head.cons()
}
pub fn add_module_search_path(thread: &mut SchemeThread, path: impl AsRef<std::path::Path>) {
    unsafe {
        thread.runtime.inner().global_lock.lock();
        thread
            .runtime
            .inner()
            .module_search_paths
            .push(path.as_ref().to_str().unwrap().to_string());
        thread.runtime.inner().global_lock.unlock();
    }
}
pub fn append_m2(thread: &mut SchemeThread, head: &mut Value, tail: &mut Value, value: Value) {
    let stack = thread.mutator.shadow_stack();
    letroot!(h = stack, *head);
    letroot!(t = stack, *tail);
    letroot!(swap = stack, Value::encode_null_value());
    *swap = Value::new(cons(thread, value, Value::encode_null_value()));
    if !h.consp() {
        *head = *swap;
        *tail = *swap;
    } else {
        t.set_cdr(*swap);
        *tail = *swap;
    }
}
#[inline]
pub fn append_m(thread: &mut SchemeThread, head: &mut Value, tail: &mut Value, value: Value) {
    let h = *head;
    let t = *tail;
    let swap;
    swap = Value::new(cons(thread, value, Value::encode_null_value()));
    if !h.consp() {
        *head = swap;
        *tail = swap;
    } else {
        t.set_cdr(swap);
        *tail = swap;
    }
}
pub fn make_blob<T: Copy>(thread: &mut SchemeThread, length: usize) -> ScmBlob {
    Array::<u8>::new_with_default(&mut thread.mutator, length * size_of::<T>())
}

pub fn make_string(thread: &mut SchemeThread, str: impl AsRef<str>) -> Managed<ScmString> {
    ScmString::new(&mut thread.mutator, str).string()
}

pub fn make_table(thread: &mut SchemeThread, mut capacity: usize) -> Managed<ScmTable> {
    if capacity < 4 {
        capacity = 4;
    }
    let table = HashMap::with_capacity(&mut thread.mutator, capacity);
    thread
        .mutator
        .allocate(ScmTable { table }, AllocationSpace::New)
}

pub fn make_native_function(
    thread: &mut SchemeThread,
    name: Value,
    ptr: NativeCallback,
    arguments: usize,
    variable_arity: bool,
) -> Managed<NativeFunction> {
    thread.mutator.allocate(
        NativeFunction {
            arguments,
            variable_arity,
            callback: ptr,
            name,
        },
        AllocationSpace::New,
    )
}

pub fn env_define(
    thread: &mut SchemeThread,
    mut table: Managed<ScmTable>,
    key: Value,
    value: Value,
    exported: bool,
) {
    let exports;
    if exported {
        let sym = thread.runtime.global_symbol(Global::Exports);
        exports = table.get(Value::new(sym)).unwrap();
    } else {
        exports = Value::encode_null_value();
    }

    table.set(thread, key, value);
    if exported {
        exports.table().set(thread, key, value);
    }
}
pub fn env_qualify_name(
    thread: &mut SchemeThread,
    env: Managed<ScmTable>,
    name: Value,
) -> Managed<ScmSymbol> {
    let sym = thread.runtime.global_symbol(Global::ModuleName);

    let module_name = env
        .get(Value::new(sym))
        .unwrap_or_else(|| panic!("wtf {:?} {}", env.keys(), name))
        .string();
    let name = format!("{}#{}", module_name.to_string(), name);

    make_symbol(thread, name)
}
pub fn defun(
    thread: &mut SchemeThread,
    name: &str,
    ptr: NativeCallback,
    arguments: usize,
    variable_arity: bool,
    mutable: bool,
) {
    let name_ = make_string(thread, name);
    let fun = make_native_function(thread, Value::new(name_), ptr, arguments, variable_arity);
    let name = make_symbol(thread, name);
    let core = thread.runtime.inner().core_module;
    env_define(
        thread,
        core.unwrap(),
        Value::new(name),
        Value::new(fun),
        true,
    );
    let mut qualified_name = env_qualify_name(thread, core.unwrap(), Value::new(name));
    qualified_name.value = Value::new(fun);
    qualified_name.mutable = mutable;
}
pub fn define(thread: &mut SchemeThread, name: &str, value: Value, mutable: bool) {
    let name = make_symbol(thread, name);
    let core = thread.runtime.inner().core_module;
    env_define(thread, core.unwrap(), Value::new(name), value, true);
    let mut qualified_name = env_qualify_name(thread, core.unwrap(), Value::new(name));
    qualified_name.value = value;
    qualified_name.mutable = mutable;
}

pub fn string_cat(
    thread: &mut SchemeThread,
    first: Managed<ScmString>,
    second: Managed<ScmString>,
) -> Managed<ScmString> {
    let string = format!("{}{}", first.string, second.string);
    let str = String::from_str(&mut thread.mutator, string);
    thread
        .mutator
        .allocate(ScmString { string: str }, AllocationSpace::New)
}

pub fn vector_append(thread: &mut SchemeThread, vec: Value, value: Value) {
    vec.downcast::<ScmVector>()
        .vec
        .push(&mut thread.mutator, value);
}

pub fn vector_combine(
    thread: &mut SchemeThread,
    v1: Value,
    v2: Value,
) -> Option<Managed<ScmVector>> {
    if !v1.vectorp() && !v2.vectorp() {
        return None;
    }
    let capacity = if v1.vectorp() { v1.vector_length() } else { 0 }
        + if v2.vectorp() { v2.vector_length() } else { 0 };
    let mut n = make_vector(thread, capacity);
    if v1.vectorp() {
        for i in 0..v1.vector_length() {
            n.vec.push(&mut thread.mutator, v1.vector_ref(i));
        }
    }

    if v2.vectorp() {
        for i in 0..v2.vector_length() {
            n.vec.push(&mut thread.mutator, v2.vector_ref(i));
        }
    }
    Some(n)
}

pub fn module_loaded(thread: &mut SchemeThread, name: Managed<ScmString>) -> bool {
    let rt = thread.runtime;
    rt.inner().global_lock.lock();

    let ret = unsafe {
        let ret = rt
            .inner()
            .modules
            .unwrap_unchecked()
            .contains(Value::new(name));
        rt.inner().global_lock.unlock();
        ret
    };
    ret
}

pub fn register_module(
    thread: &mut SchemeThread,
    name: impl AsRef<str>,
    env: Value,
) -> Result<(), Value> {
    let name = make_string(thread, name);
    register_module_(thread, name, env)
}

pub fn register_module_(
    thread: &mut SchemeThread,
    name: Managed<ScmString>,
    env: Value,
) -> Result<(), Value> {
    let rt = thread.runtime;
    rt.inner().global_lock.lock();

    unsafe {
        let ret = rt
            .inner()
            .modules
            .unwrap_unchecked()
            .contains(Value::new(name));

        let ret = if ret {
            rt.inner().global_lock.unlock();
            let message = make_string(thread, "attempt to overload existing module");
            let tag = thread.runtime.global_symbol(Global::ScmEval);
            let exception = make_exception(thread, tag, message, Value::new(Null));
            return Err(Value::new(exception));
        } else {
            rt.inner()
                .modules
                .unwrap_unchecked()
                .set(thread, Value::new(name), env);
        };
        rt.inner().global_lock.unlock();
        ret
    };
    Ok(())
}

pub fn env_globalp(thread: &mut SchemeThread, env: Managed<ScmTable>) -> bool {
    let s = thread.runtime.global_symbol(Global::GlobalEnvironment);
    env.contains(Value::new(s))
}

pub fn load_file(
    thread: &mut SchemeThread,
    path: impl AsRef<std::path::Path>,
    module_name: Value,
) -> Result<Value, Value> {
    let file = match std::fs::read_to_string(path) {
        Err(_) => return Ok(Value::new(false)),
        Ok(val) => val,
    };
    let stack = thread.mutator.shadow_stack();
    let mut parser = lexpr::Parser::from_str(&file);
    letroot!(cc = stack, Compiler::new(thread, None, None, 0));
    if module_name.stringp() {
        cc.enter_module(thread, module_name)?;
    } else {
        let tag = thread.runtime.global_symbol(Global::ModuleName);
        let module_name = thread
            .runtime
            .inner()
            .user_module
            .unwrap()
            .get(Value::new(tag));
        cc.enter_module(thread, module_name.unwrap())?;
    }
    let mut x = Value::encode_undefined_value();
    while let Some(val) = parser.next_value().map_err(|error| {
        let tag = thread.runtime.global_symbol(Global::ScmRead);
        let message = make_string(thread, format!("Failed to read file: '{}'", error));
        Value::new(make_exception(thread, tag, message, Value::new(Null)))
    })? {
        cc.compile(thread, &val, false)?;

        let p = cc.end(thread, 0, false);

        x = vm::apply(thread, Value::new(p), &[])?;
        cc.clear();
    }

    Ok(x)
}

pub fn load_module(thread: &mut SchemeThread, name: Managed<ScmString>) -> Result<Value, Value> {
    if module_loaded(thread, name) {
        return Ok(thread
            .runtime
            .with_modules(|modules| modules.get(Value::new(name)))
            .unwrap());
    }

    let mut path = name.to_string();
    path = path.replace('#', "/");
    path.push_str(".scm");

    if thread.runtime.inner().module_search_paths.is_empty() {
        panic!("No module search paths; Try adding new one");
    }

    for i in 0..thread.runtime.inner().module_search_paths.len() {
        // todo: thread safety
        let mut whole_path = thread.runtime.inner().module_search_paths[i].clone();
        whole_path.push_str(&path);

        let whole_path = std::path::Path::new(&whole_path);
        if !whole_path.exists() {
            continue;
        }
        load_file(thread, whole_path, Value::new(name))?;

        if module_loaded(thread, name) {
            return Ok(thread
                .runtime
                .with_modules(|modules| modules.get(Value::new(name)))
                .unwrap());
        }
    }

    let msg = make_string(
        thread,
        format!(
            "Failed to find file {} searched paths: {:?}",
            path,
            thread.runtime.inner().module_search_paths
        ),
    );
    let tag = thread.runtime.global_symbol(Global::ScmCompile);

    Err(Value::new(make_exception(
        thread,
        tag,
        msg,
        Value::encode_null_value(),
    )))
}

pub fn listp(obj: Value) -> bool {
    let mut local = obj;
    let mut rapid = obj;
    loop {
        for _ in 0..2 {
            if let Some(r) = rapid.try_cons() {
                rapid = r.cdr;
            } else {
                return rapid.is_null();
            }
        }

        local = local.cons().cdr;
        if local == rapid {
            return false;
        }
    }
}

pub fn convert_module_name(
    thread: &mut SchemeThread,
    mut spec: &lexpr::Value,
) -> Result<Value, Value> {
    let mut out = std::string::String::new();
    out.push('#');
    if spec.is_symbol() {
        out.push_str(&spec.to_string());
        return Ok(Value::new(make_string(thread, out)));
    }

    if !spec.is_list() {
        let tag = thread.runtime.global_symbol(Global::ScmEval);
        let msg = make_string(thread, "module name must be a list of symbols");
        return Err(Value::new(make_exception(
            thread,
            tag,
            msg,
            Value::new(Null),
        )));
    }
    while let Some(cons) = spec.as_cons() {
        let sym = cons.car();
        if let Some(sym) = sym.as_symbol() {
            out.push_str(sym);
            if !cons.cdr().is_null() {
                out.push('#');
            }
            spec = cons.cdr();
        } else {
            let tag = thread.runtime.global_symbol(Global::ScmEval);
            let msg = make_string(thread, "Encountered non-symbol in module name");
            return Err(Value::new(make_exception(
                thread,
                tag,
                msg,
                Value::new(Null),
            )));
        }
    }
    Ok(Value::new(make_string(thread, out)))
}
impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}
impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_int32() {
            write!(f, "{}", self.get_int32())
        } else if self.is_double() {
            write!(f, "{}", self.get_double())
        } else if self.symbolp() {
            let sym = self.downcast::<ScmSymbol>();
            write!(f, "{}", sym.name)
        } else if self.boolp() {
            write!(f, "{}", self.get_bool())
        } else if self.is_null() {
            write!(f, "null")
        } else if self.is_undefined() {
            write!(f, "undefined")
        } else if self.stringp() {
            write!(f, "{}", self.string().to_string())
        } else if self.blobp() {
            write!(f, "#<blob {}>", self.blob_length())
        } else if self.vectorp() {
            write!(f, "#(")?;
            for i in 0..self.vector_length() {
                write!(f, "{}", self.vector_ref(i))?;
                if i != self.vector_length() - 1 {
                    write!(f, " ")?;
                }
            }
            write!(f, ")")
        } else if self.consp() {
            write!(f, "({}", self.car())?;
            let mut x = self.cdr();
            while x.consp() {
                write!(f, " {}", x.car())?;
                x = x.cdr();
            }
            if !x.is_null() {
                write!(f, " . {}", x)?;
            }
            write!(f, ")")
        } else if self.exceptionp() {
            write!(
                f,
                "#<exception {} {}>",
                self.exception_tag().name,
                self.exception_message().to_string()
            )
        } else if self.prototypep() {
            write!(
                f,
                "#<function {} at {:p}>",
                self.prototype_name()
                    .map(|x| x.to_string())
                    .unwrap_or_else(|| "<anonymous>".to_string()),
                self.get_object()
            )
        } else if self.closurep() {
            write!(
                f,
                "#<closure {} at {:p}>",
                self.downcast::<Closure>()
                    .prototype
                    .name
                    .map(|x| x.to_string())
                    .unwrap_or_else(|| "<anonymous>".to_string()),
                self.get_object()
            )
        } else if self.native_functionp() {
            write!(
                f,
                "#<native function '{}' at {:p}>",
                self.downcast::<NativeFunction>().name,
                self.downcast::<NativeFunction>().callback as usize as *const u8,
            )
        } else if self.tablep() {
            write!(f, "#<table at {:p}>", self.get_object())
        } else if self.is_object() {
            write!(f, "#<object at {:p}>", self.get_object())
        } else if self.is_native_value() {
            write!(f, "#<native value {}>", self.get_native_value())
        } else if self.is_object() && self.get_object().is::<Macro>() {
            write!(f, "#<macro>")
        } else {
            write!(f, "#unknown")
        }
    }
}

pub fn value_to_lexpr(thread: &mut SchemeThread, val: Value) -> lexpr::Value {
    if val.is_int32() {
        lexpr::Value::Number(lexpr::Number::from(val.get_int32()))
    } else if val.is_double() {
        lexpr::Value::Number(lexpr::Number::from_f64(val.get_double()).unwrap())
    } else if val.boolp() {
        lexpr::Value::Bool(val.get_bool())
    } else if val.is_null() {
        lexpr::Value::Null
    } else if val.stringp() {
        lexpr::Value::String(val.string().to_string().into_boxed_str())
    } else if val.symbolp() {
        lexpr::Value::Symbol(val.symbol_name().to_string().into_boxed_str())
    } else if val.consp() {
        lexpr::Value::Cons(lexpr::Cons::new(
            value_to_lexpr(thread, val.car()),
            value_to_lexpr(thread, val.cdr()),
        ))
    } else {
        todo!()
    }
}

pub fn lexpr_to_value(thread: &mut SchemeThread, val: &lexpr::Value) -> Value {
    match val {
        lexpr::Value::Bool(x) => Value::new(*x),
        lexpr::Value::Number(x) => {
            if let Some(i) = x.as_i64() {
                if i as i32 as i64 == i {
                    return Value::new(i as i32);
                } else {
                    return Value::new(i as f64);
                }
            } else if let Some(i) = x.as_f64() {
                return Value::new(i);
            } else {
                return Value::new(x.as_u64().unwrap() as f64);
            }
        }
        lexpr::Value::Null => Value::encode_null_value(),
        lexpr::Value::String(x) => Value::new(make_string(thread, x)),
        lexpr::Value::Symbol(x) => Value::new(make_symbol(thread, x)),
        lexpr::Value::Vector(values) => {
            let mut vector = make_vector(thread, values.len());
            for val in values.iter() {
                let val = lexpr_to_value(thread, val);
                vector.vec.push(&mut thread.mutator, val);
            }
            Value::new(vector)
        }
        lexpr::Value::Cons(cons_) => {
            let car = lexpr_to_value(thread, cons_.car());
            let cdr = lexpr_to_value(thread, cons_.cdr());
            Value::new(cons(thread, car, cdr))
        }
        _ => todo!(),
    }
}

pub fn make_list(thread: &mut SchemeThread, values: &[Value]) -> Value {
    let mut first = None;
    let mut last: Option<Managed<ScmCons>> = None;
    for val in values.iter() {
        let newcell = cons(thread, *val, Value::encode_null_value());
        if first.is_none() {
            first = Some(newcell);
        } else {
            last.unwrap().cdr = Value::new(newcell);
        }
        last = Some(newcell);
    }
    first
        .map(|x| Value::new(x))
        .unwrap_or_else(|| Value::encode_null_value())
}

pub fn make_bignum(thread: &mut SchemeThread, n: num::BigInt) -> Managed<ScmBignum> {
    thread
        .mutator
        .allocate(ScmBignum { num: n }, AllocationSpace::New)
}

pub fn make_complex(thread: &mut SchemeThread, n: num::complex::Complex64) -> Managed<ScmComplex> {
    thread
        .mutator
        .allocate(ScmComplex { complex: n }, AllocationSpace::New)
}

pub fn make_rational(thread: &mut SchemeThread, n: num::BigRational) -> Managed<ScmRational> {
    thread
        .mutator
        .allocate(ScmRational { rational: n }, AllocationSpace::New)
}
