use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::{Hash, Hasher},
    mem::{size_of, MaybeUninit},
    ops::{ControlFlow, FromResidual, Try},
    ptr::null_mut,
};

use crate::{
    gc::{allocator::PageReleaseMode, Gc},
    gc_bdwgc::DEFAULT_INITIAL_HEAP_SIZE,
    vec::GcVec,
    vm::{env_define, Compiler},
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[repr(u8)]
pub enum ValueType {
    Object = 0,
    Context,
    Pair,
    Symbol,
    String,
    Bytes,
    Vector,

    HashTable,

    Function,
    Closure,
    NativeFunction,
    Macro,
    Synclo,

    Upvalue,

    Exception,

    GcVec,
    Compiler,
}
#[derive(Copy)]
union EncodedValueDescriptor {
    as_int64: i64,
    #[cfg(target_pointer_width = "32")]
    as_f64: f64,
    #[cfg(target_pointer_width = "64")]
    ptr: *mut (),

    #[cfg(target_pointer_width = "32")]
    as_bits: AsBits,
}
impl Clone for EncodedValueDescriptor {
    fn clone(&self) -> Self {
        *self
    }
}

impl PartialEq for EncodedValueDescriptor {
    fn eq(&self, other: &Self) -> bool {
        unsafe { self.as_int64 == other.as_int64 }
    }
}

impl Eq for EncodedValueDescriptor {}

#[cfg(target_pointer_width = "32")]
#[cfg(target_endian = "little")]
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct AsBits {
    payload: i32,
    tag: i32,
}

#[cfg(target_pointer_width = "32")]
#[cfg(target_endian = "big")]
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct AsBits {
    tag: i32,
    payload: i32,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Value(EncodedValueDescriptor);

impl Value {
    pub const VOID: Self = Self(EncodedValueDescriptor { as_int64: 0 });
}

#[cfg(target_pointer_width = "32")]
impl Value {
    pub const INT32_TAG: i32 = 0xffffffff;
    pub const BOOLEAN_TAG: i32 = 0xfffffffe;
    pub const NULL_TAG: i32 = 0xfffffffd;
    pub const UNDEFINED_TAG: i32 = 0xfffffffc;
    pub const CELL_TAG: i32 = 0xfffffffb;
    pub const EMPTY_VALUE_TAG: i32 = 0xfffffffa;
    pub const DELETED_VALUE_TAG: i32 = 0xfffffff9;
}

/// Returns some kind of pure NaN.
#[inline(always)]
pub fn pure_nan() -> f64 {
    f64::from_bits(0x7ff8000000000000)
}

#[inline]
pub fn is_impure_nan(value: f64) -> bool {
    // Tests if the double value would break JSVALUE64 encoding, which is the most
    // aggressive kind of encoding that we currently use.
    value.to_bits() >= 0xfffe000000000000
}
/// If the given value is NaN then return a NaN that is known to be pure.
pub fn purify_nan(value: f64) -> f64 {
    if value != value {
        return pure_nan();
    }
    value
}

#[cfg(target_pointer_width = "64")]
impl Value {
    pub const DOUBLE_ENCODE_OFFSET_BIT: usize = 49;
    pub const DOUBLE_ENCODE_OFFSET: i64 = 1 << Self::DOUBLE_ENCODE_OFFSET_BIT as i64;
    pub const NUMBER_TAG: i64 = 0xfffe000000000000u64 as i64;
    pub const LOWEST_OF_HIGH_BITS: i64 = 1 << 49;
    pub const OTHER_TAG: i32 = 0x2;
    pub const BOOL_TAG: i32 = 0x4;
    pub const UNDEFINED_TAG: i32 = 0x8;

    pub const VALUE_FALSE: i32 = Self::OTHER_TAG | Self::BOOL_TAG | false as i32;
    pub const VALUE_TRUE: i32 = Self::OTHER_TAG | Self::BOOL_TAG | true as i32;

    pub const VALUE_UNDEFINED: i32 = Self::OTHER_TAG | Self::UNDEFINED_TAG;
    pub const VALUE_NULL: i32 = Self::OTHER_TAG;

    pub const MISC_TAG: i64 = (Self::OTHER_TAG | Self::BOOL_TAG | Self::UNDEFINED_TAG) as i64;

    pub const NOT_CELL_MASK: i64 = Self::NUMBER_TAG | Self::OTHER_TAG as i64;

    pub const VALUE_EMPTY: i32 = 0x0;
    pub const VALUE_DELETED: i32 = 0x4;

    pub const fn as_i64(self) -> i64 {
        unsafe { self.0.as_int64 }
    }

    pub const fn is_empty(self) -> bool {
        self.as_i64() == Self::VALUE_EMPTY as i64
    }

    pub const fn is_undefined(self) -> bool {
        self.as_i64() == Self::VALUE_UNDEFINED as i64
    }

    pub const fn is_null(self) -> bool {
        self.as_i64() == Self::VALUE_NULL as i64
    }

    pub const fn is_true(self) -> bool {
        self.as_i64() == Self::VALUE_TRUE as i64
    }

    pub const fn is_false(self) -> bool {
        self.as_i64() == Self::VALUE_FALSE as i64
    }

    pub const fn is_boolean(self) -> bool {
        (self.as_i64() & !1) == Self::VALUE_FALSE as i64
    }

    pub const fn is_int32(self) -> bool {
        (self.as_i64() & Self::NUMBER_TAG) == Self::NUMBER_TAG
    }

    pub const fn is_cell(self) -> bool {
        (self.as_i64() & Self::NOT_CELL_MASK) == 0
    }

    pub const fn is_undefined_or_null(self) -> bool {
        (self.as_i64() & !Self::UNDEFINED_TAG as i64) == Self::VALUE_NULL as i64
    }

    pub const fn as_boolean(self) -> bool {
        debug_assert!(self.is_boolean());
        self.as_i64() == Self::VALUE_TRUE as i64
    }

    pub const fn as_int32(self) -> i32 {
        debug_assert!(self.is_int32());
        self.as_i64() as i32
    }

    pub const fn as_number(self) -> f64 {
        if self.is_int32() {
            return self.as_int32() as f64;
        }
        self.as_double()
    }

    pub const fn is_double(self) -> bool {
        self.is_number() && !self.is_int32()
    }

    pub const fn is_number(self) -> bool {
        (self.as_i64() & Self::NUMBER_TAG) != 0
    }

    pub const fn as_cell(&self) -> Gc<()> {
        unsafe { std::mem::transmute(self.0.ptr) }
    }

    pub const fn as_double(self) -> f64 {
        let tmp = self.as_i64() - Self::DOUBLE_ENCODE_OFFSET;

        // TODO: Change this to f64::from_bits once it is stable in const fn
        unsafe { std::mem::transmute(tmp) }
    }

    pub const fn new_f64(x: f64) -> Self {
        let bits = unsafe { std::mem::transmute::<_, i64>(x) };

        Self(EncodedValueDescriptor {
            as_int64: bits + Self::DOUBLE_ENCODE_OFFSET,
        })
    }

    pub const fn new_i32(x: i32) -> Self {
        Self(EncodedValueDescriptor {
            as_int64: Self::NUMBER_TAG | x as i64,
        })
    }

    pub const fn new_cell<T>(x: Gc<T>) -> Self {
        Self(EncodedValueDescriptor {
            as_int64: unsafe { std::mem::transmute::<_, usize>(x) as i64 },
        })
    }

    pub const fn new_bool(x: bool) -> Self {
        if x {
            Self(EncodedValueDescriptor {
                as_int64: Self::VALUE_TRUE as _,
            })
        } else {
            Self(EncodedValueDescriptor {
                as_int64: Self::VALUE_FALSE as _,
            })
        }
    }

    pub fn new_null() -> Self {
        Self(EncodedValueDescriptor {
            as_int64: Self::VALUE_NULL as _,
        })
    }

    pub fn empty() -> Self {
        Self(EncodedValueDescriptor {
            as_int64: Self::VALUE_EMPTY as _,
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Pair {
    pub car: Value,
    pub cdr: Value,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Vector {
    length: usize,
    data: [Value; 1],
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Bytes {
    length: usize,
    data: [u8; 1],
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Str {
    length: usize,
    data: [u8; 1],
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Macro {
    procedure: Value,
    env: Value,
}

#[repr(C)]
pub struct Upvalue {
    pub(crate) inner: UpvaluerInner,
    pub(crate) converted: bool,
}

pub(crate) union UpvaluerInner {
    pub(crate) local_ref: *mut Value,
    pub(crate) converted: Value,
}

#[repr(C)]
pub struct Closure {
    /// Procedure
    pub(crate) procedure: Value,
    /// Vector of upvalues
    pub(crate) upvalues: Value,
    /// Optional data that is passed with this closure
    pub(crate) data: Value,
}

#[repr(C)]
pub struct Procedure {
    pub(crate) constants: Value,
    pub(crate) code: Value,

    pub(crate) local_free_variables: Value,
    pub(crate) upvalues: Value,

    pub(crate) name: Value,

    pub(crate) stack_max: u16,
    pub(crate) locals: u16,
    pub(crate) local_free_variable_count: u16,
    pub(crate) arguments: u16,
    pub(crate) variable_arity: bool,
}

pub type NativeCallback = fn(ContextRef, &[Value], Value) -> CallResult;

#[repr(C)]
pub struct NativeProcedure {
    pub(crate) name: Value,
    pub(crate) callback: NativeCallback,
    pub(crate) argc: usize,
    pub(crate) variable: bool,
    pub(crate) closure: Value,
    pub(crate) macrop: bool,
}

#[repr(C)]
pub struct Symbol {
    pub(crate) name: Value,
    pub(crate) value: Value,
    pub(crate) module: Value,
}

#[repr(C)]
pub struct Synclo {
    env: Value,
    vars: Value,
    expr: Value,
}

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct HashTableRec {
    pub(crate) key: Value,
    pub(crate) value: Value,
    pub(crate) hash: u32,
    pub(crate) next: *mut HashTableRec,
}

#[repr(C)]
pub struct HashTable {
    pub(crate) size: u32,
    pub(crate) count: u32,
    pub(crate) elts: *mut *mut HashTableRec,
    pub(crate) eq_fn: EqualFn,
    pub(crate) hash_fn: HashFn,
}

pub type HashFn = fn(ContextRef, value: Value) -> Value;
pub type EqualFn = fn(ContextRef, a: Value, b: Value) -> Value;

#[repr(C)]

pub struct Exception {
    kind: Value,
    message: Value,
    irritants: Value,
    procedure: Value,
    stack_trace: Value,
}

impl Value {
    pub fn check_tag(self, x: u32) -> bool {
        if !self.is_cell() || self.is_empty() {
            return false;
        }
        self.as_cell().is_tagged(x)
    }
    pub fn macrop(self) -> bool {
        self.check_tag(ValueType::Macro as _)
    }

    pub fn synclop(self) -> bool {
        self.check_tag(ValueType::Synclo as _)
    }

    pub fn procedurep(self) -> bool {
        self.check_tag(ValueType::Function as _)
    }

    pub fn closurep(self) -> bool {
        self.check_tag(ValueType::Closure as _)
    }

    pub fn nativep(self) -> bool {
        self.check_tag(ValueType::NativeFunction as _)
    }

    pub fn applicablep(self) -> bool {
        self.procedurep() || self.nativep() || self.closurep()
    }

    pub fn pairp(self) -> bool {
        self.check_tag(ValueType::Pair as _)
    }

    pub fn hashtablep(self) -> bool {
        self.check_tag(ValueType::HashTable as _)
    }
    pub fn gcvecp(self) -> bool {
        self.check_tag(ValueType::GcVec as _)
    }
    pub fn vectorp(self) -> bool {
        self.check_tag(ValueType::Vector as _)
    }

    pub fn bvectorp(self) -> bool {
        self.check_tag(ValueType::Bytes as _)
    }

    pub fn stringp(self) -> bool {
        self.check_tag(ValueType::String as _)
    }

    pub fn symbolp(self) -> bool {
        self.check_tag(ValueType::Symbol as _)
    }

    pub fn upvaluep(self) -> bool {
        self.check_tag(ValueType::Upvalue as _)
    }

    pub fn exceptionp(self) -> bool {
        self.check_tag(ValueType::Exception as _)
    }

    pub(crate) fn downcast<T>(self, t: u32) -> Gc<T> {
        assert!(self.check_tag(t));
        unsafe { self.as_cell().downcast_unchecked() }
    }
    pub(crate) fn downcast_ref<T>(&self, t: u32) -> &Gc<T> {
        assert!(self.check_tag(t));
        unsafe { std::mem::transmute(self) }
    }

    pub(crate) fn downcast_mut<T>(&mut self, t: u32) -> &mut Gc<T> {
        assert!(self.check_tag(t));
        unsafe { std::mem::transmute(self) }
    }
    pub fn car(self) -> Value {
        self.downcast::<Pair>(ValueType::Pair as _).car
    }

    pub fn cdr(self) -> Value {
        self.downcast::<Pair>(ValueType::Pair as _).cdr
    }

    pub fn car_mut(&mut self) -> &mut Value {
        &mut self.downcast_mut::<Pair>(ValueType::Pair as _).car
    }

    pub fn cdr_mut(&mut self) -> &mut Value {
        &mut self.downcast_mut::<Pair>(ValueType::Pair as _).cdr
    }
    pub fn set_car(self, x: Value) {
        self.downcast::<Pair>(ValueType::Pair as _).car = x;
    }

    pub fn set_cdr(self, x: Value) {
        self.downcast::<Pair>(ValueType::Pair as _).cdr = x;
    }
    pub fn caar(self) -> Value {
        self.car().car()
    }

    pub fn cadr(self) -> Value {
        self.car().cdr()
    }

    pub fn cddr(self) -> Value {
        self.cdr().cdr()
    }

    pub fn caaar(self) -> Value {
        self.caar().car()
    }

    pub fn caadr(self) -> Value {
        self.car().car().cdr()
    }

    pub fn caddr(self) -> Value {
        self.car().cdr().cdr()
    }

    pub fn cdddr(self) -> Value {
        self.cddr().cdr()
    }

    pub fn upvalue_value(self) -> Value {
        let u = self.downcast::<Upvalue>(ValueType::Upvalue as _);
        if u.converted {
            // safety: when u.converted is true, u.inner.converted is guaranteed to hold correct value
            unsafe { u.inner.converted }
        } else {
            // safety: local_ref is guaranteed to point to initialized stack slot
            unsafe { u.inner.local_ref.read() }
        }
    }

    pub fn upvalue_converted(self) -> bool {
        self.downcast::<Upvalue>(ValueType::Upvalue as _).converted
    }

    pub fn upvalue_set_value(self, x: Value) {
        let mut u = self.downcast::<Upvalue>(ValueType::Upvalue as _);
        if u.converted {
            u.inner.converted = x;
        } else {
            unsafe {
                u.inner.local_ref.write(x);
            }
        }
    }

    pub fn upvalue_close(self) {
        let mut u = self.downcast::<Upvalue>(ValueType::Upvalue as _);
        if !u.converted {
            let tmp = unsafe { u.inner.local_ref.read() };
            u.inner.converted = tmp;
            u.converted = true;
        }
    }

    pub fn string_data(&self) -> &str {
        let s = self.downcast_ref::<Str>(ValueType::String as _);
        unsafe {
            std::str::from_utf8_unchecked(std::slice::from_raw_parts(s.data.as_ptr(), s.length))
        }
    }

    pub fn vector_ref(self, x: usize) -> Value {
        unsafe {
            let v = self.downcast::<Vector>(ValueType::Vector as _);
            debug_assert!(v.length > x);
            v.data.as_ptr().add(x).read()
        }
    }
    pub fn vector_set(self, x: usize, val: Value) {
        unsafe {
            let mut v = self.downcast::<Vector>(ValueType::Vector as _);
            debug_assert!(v.length > x);
            v.data.as_mut_ptr().add(x).write(val);
        }
    }
    pub fn vector_length(self) -> usize {
        self.downcast::<Vector>(ValueType::Vector as _).length
    }

    pub fn bvector_raw(self) -> *mut u8 {
        self.downcast::<Bytes>(ValueType::Bytes as _)
            .data
            .as_mut_ptr()
    }

    pub fn bvector_ref<T: Copy>(self, x: usize) -> T {
        unsafe {
            let v = self.downcast::<Bytes>(ValueType::Bytes as _);
            debug_assert!(v.length > x * size_of::<T>());
            v.data.as_ptr().cast::<T>().add(x).read()
        }
    }

    pub fn bvector_set<T: Copy>(self, x: usize, val: T) {
        unsafe {
            let mut v = self.downcast::<Bytes>(ValueType::Bytes as _);
            debug_assert!(
                v.length > x * size_of::<T>(),
                "{} > {}",
                v.length,
                x * size_of::<T>()
            );
            v.data.as_mut_ptr().cast::<T>().add(x).write(val);
        }
    }

    pub fn bvector_length<T>(self) -> usize {
        self.downcast::<Bytes>(ValueType::Bytes as _).length / size_of::<T>()
    }

    pub fn symbol_name(self) -> Value {
        self.downcast::<Symbol>(ValueType::Symbol as _).name
    }
    pub fn symbol_value(self) -> Value {
        self.downcast::<Symbol>(ValueType::Symbol as _).value
    }

    pub fn symbol_module(self) -> Value {
        self.downcast::<Symbol>(ValueType::Symbol as _).module
    }

    pub fn set_symbol_value(self, x: Value) {
        self.downcast::<Symbol>(ValueType::Symbol as _).value = x;
    }

    pub(crate) fn set_symbol_module(self, x: Value) {
        self.downcast::<Symbol>(ValueType::Symbol as _).module = x;
    }
    pub fn hash_set(self, ctx: ContextRef, key: Value, value: Value) -> Value {
        self.downcast::<HashTable>(ValueType::HashTable as _)
            .insert(ctx, key, value)
    }

    pub fn hash_get(self, ctx: ContextRef, key: Value, failure_result: Value) -> Value {
        self.downcast::<HashTable>(ValueType::HashTable as _)
            .lookup(ctx, key, failure_result)
    }

    pub fn hash_remove(self, ctx: ContextRef, key: Value) -> Value {
        self.downcast::<HashTable>(ValueType::HashTable as _)
            .remove(ctx, key)
    }

    pub fn hash_for_each(self, callback: impl FnMut(Value, Value, u32) -> Value) -> Value {
        self.downcast::<HashTable>(ValueType::HashTable as _)
            .for_each(callback)
    }

    pub fn closure_procedure(self) -> Value {
        self.downcast::<Closure>(ValueType::Closure as _).procedure
    }

    pub fn closure_upvalues(self) -> Value {
        self.downcast::<Closure>(ValueType::Closure as _).upvalues
    }

    pub fn macro_procedure(self) -> Value {
        self.downcast::<Macro>(ValueType::Macro as _).procedure
    }

    pub fn synclo_vars(self) -> Value {
        self.downcast::<Synclo>(ValueType::Synclo as _).vars
    }

    pub fn synclo_env(self) -> Value {
        self.downcast::<Synclo>(ValueType::Synclo as _).env
    }

    pub fn synclo_expr(self) -> Value {
        self.downcast::<Synclo>(ValueType::Synclo as _).expr
    }

    pub fn synclo_vars_set(self, x: Value) {
        self.downcast::<Synclo>(ValueType::Synclo as _).vars = x;
    }

    pub fn synclo_env_set(self, x: Value) {
        self.downcast::<Synclo>(ValueType::Synclo as _).env = x;
    }

    pub fn synclo_vars_expr(self, x: Value) {
        self.downcast::<Synclo>(ValueType::Synclo as _).expr = x;
    }

    pub fn macro_procedure_set(self, x: Value) {
        self.downcast::<Macro>(ValueType::Macro as _).procedure = x;
    }
}

pub fn hashtable_default_eq(_ctx: ContextRef, a: Value, b: Value) -> Value {
    return Value::new_bool(r5rs_equal_pred(a, b));
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.as_i64().hash(h);
    }
}

pub fn make_pair(mut ctx: ContextRef, car: Value, cdr: Value) -> Value {
    let p = ctx
        .heap()
        .allocate_tagged(Pair { car, cdr }, ValueType::Pair as _, false, false);
    Value::new_cell(p)
}

#[allow(dead_code)]
fn find_and_merge_opponent(
    ctx: ContextRef,
    visited: &mut HashMap<Value, Value>,
    a: Value,
    b: Value,
) -> bool {
    let opponent = visited.get(&a).copied();
    if let Some(opponent) = opponent {
        let mut lst = opponent;
        while lst.pairp() {
            if lst.car() != b {
                lst = lst.cdr();
                continue;
            }
            return true;
        }

        visited.insert(a, make_pair(ctx, b, opponent));
    } else {
        visited.insert(a, Value::new_null());
    }
    false
}

pub fn r5rs_equal_pred(mut lst1: Value, mut lst2: Value) -> bool {
    'top: loop {
        if lst1 == lst2 {
            return true;
        }

        if lst1.pairp() {
            if lst2.pairp() {
                if r5rs_equal_pred(lst1.car(), lst2.car()) {
                    lst1 = lst1.cdr();
                    lst2 = lst2.cdr();
                    continue 'top;
                }
            }
            return false;
        }

        if lst1.vectorp() {
            if lst2.vectorp() {
                let n1 = lst1.vector_length();
                let n2 = lst2.vector_length();
                if n1 == n2 {
                    for i in 0..n1 {
                        if r5rs_equal_pred(lst1.vector_ref(i), lst2.vector_ref(i)) {
                            continue;
                        }
                        return false;
                    }
                }
            }
            return false;
        }

        if lst1.bvectorp() {
            if lst2.bvectorp() {
                let n1 = lst1.bvector_length::<u8>();
                let n2 = lst2.bvector_length::<u8>();
                if n1 == n2 {
                    for i in 0..n1 {
                        if lst1.bvector_ref::<u8>(i) != lst2.bvector_ref::<u8>(i) {
                            return false;
                        }
                    }

                    return true;
                }
            }
            return false;
        }

        if lst1.stringp() {
            if lst2.stringp() {
                return lst1.string_data() == lst2.string_data();
            }
            return false;
        }

        return eqv_pred(lst1, lst2);
    }
}

pub fn eqv_pred(obj1: Value, obj2: Value) -> bool {
    if obj1 == obj2 {
        return true;
    }

    if obj1.is_number() {
        if obj2.is_number() {
            let a = obj1.as_number();
            let b = obj2.as_number();
            return a == b;
        }
    }

    false
}
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

    Define,

    Set,
    Lambda,
    If,
    DefineSyntax,
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
    "define",
    "set!",
    "lambda",
    "if",
    "%define-syntax",
    "module",
    "quote",
    "import",
    "public",
    "private",
    "export",
    "begin",
    "*",
];

pub struct ContextParams {
    pub heap_size: usize,
    pub heap_max_size: usize,
    pub heap_min_size: usize,
    pub heap_threshold: usize,
    pub heap_growth_multiplier: f64,
    pub page_release_threshold: usize,
    pub page_release_mode: PageReleaseMode,
    pub gc_verbose: u8,
    pub stack_size: usize,
}

impl Default for ContextParams {
    fn default() -> Self {
        Self {
            gc_verbose: 0,
            heap_growth_multiplier: 1.5,
            heap_max_size: 128 * 1024 * 1024,
            heap_min_size: 32 * 1024,
            heap_size: DEFAULT_INITIAL_HEAP_SIZE,
            heap_threshold: 128 * 1024,
            page_release_mode: PageReleaseMode::SizeAndEnd,
            page_release_threshold: 16 * 1024,
            stack_size: 8 * 1024,
        }
    }
}

pub type ContextRef = Gc<Context>;

pub struct Context {
    heap: MaybeUninit<Box<crate::Heap>>,

    /// Arguments that are passed to `trampoline_function`.
    pub(crate) trampoline_arguments: GcVec<Value>,

    /// Trampoline function
    pub(crate) trampoline_function: Value,
    pub(crate) symbols: Value,
    pub(crate) user_module: Value,
    pub(crate) core_module: Value,
    pub module_search_paths: Vec<String>,
    pub(crate) modules: Value,
    pub(crate) stack: Gc<Stack>,
    pub(crate) globals: [Value; GLOBAL_SYMBOLS.len()],
    pub(crate) toplevel_cc: Option<Gc<Compiler>>,
}

impl Context {
    pub fn new(p: ContextParams) -> Gc<Context> {
        let mut heap = Box::new(crate::Heap::new(
            p.heap_size,
            p.heap_min_size,
            p.heap_max_size,
            p.heap_threshold,
            p.heap_growth_multiplier,
            p.page_release_mode,
            p.page_release_threshold,
            p.gc_verbose,
        ));

        let stack = Stack::new(&mut heap, p.stack_size);
        let targs = GcVec::with_capacity(&mut heap, 6);

        let mut this = heap.allocate_tagged(
            Context {
                toplevel_cc: None,
                heap: MaybeUninit::uninit(),
                symbols: Value::new_null(),
                stack,
                globals: [Value::new_null(); GLOBAL_SYMBOLS.len()],
                trampoline_arguments: targs,
                trampoline_function: Value::new_null(),
                user_module: Value::new_null(),
                core_module: Value::new_null(),
                module_search_paths: vec![],
                modules: Value::new_null(),
            },
            ValueType::Context as _,
            false,
            false,
        );

        //heap.ctx = Value::new_cell(this);
        this.heap = MaybeUninit::new(heap);
        this.init_globals();

        this
    }

    pub fn heap(&mut self) -> &mut crate::Heap {
        unsafe { self.heap.assume_init_mut() }
    }

    pub fn global(&self, g: Global) -> Value {
        self.globals[g as usize]
    }
}

impl ContextRef {
    fn init_globals(mut self) {
        self.symbols = make_vector(self, 389, Value::new_null());

        for (i, g) in GLOBAL_SYMBOLS.iter().enumerate() {
            let sym = intern(self, g);
            self.globals[i] = sym;
        }

        self.core_module = make_env(self, Value::new_bool(false), Some("#waffle#core"));

        for i in Global::Define as usize..=Global::Begin as usize {
            let g = unsafe { std::mem::transmute::<_, Global>(i as u8) };

            env_define(
                self,
                self.core_module,
                self.global(g),
                self.global(Global::Special),
                true,
            );
        }

        self.user_module = make_env(self, self.core_module, Some("#user"));

        self.modules = make_hash(self, 4);

        let n1 = make_string(self, "#waffle#core");
        self.register_module(n1, self.core_module);
        let n2 = make_string(self, "#user");
        self.register_module(n2, self.user_module);

        self.toplevel_cc = Some(Compiler::new(self, Value::new_null()));
        self.toplevel_cc.unwrap().enter_module(n2);

        super::vm::init_primitives(self);
    }

    pub fn register_module(self, name: Value, env: Value) -> Value {
        let ret = self.modules.hash_get(self, name, Value::new_null());
        if ret.is_null() {
            self.modules.hash_set(self, name, env);
        } else {
            let g = self.global(Global::ScmEval);
            let message = make_string(self, format!("trying to redefine module '{}'", name));
            return make_exception(
                self,
                g,
                message,
                Value::new_null(),
                Value::new_null(),
                Value::new_null(),
            );
        }

        ret
    }

    pub fn module_loaded(self, x: Value) -> bool {
        self.modules.hash_get(self, x, Value::empty()) != Value::empty()
    }

    pub fn load_module(mut self, x: Value) -> Value {
        if self.module_loaded(x) {
            return self.modules.hash_get(self, x, Value::empty());
        }
        let mut path = x.string_data().to_string();
        path = path.replace('#', "/");
        path.push_str(".scm");
        if self.module_search_paths.is_empty() {
            panic!("no module search paths; try adding new one");
        }
        for i in 0..self.module_search_paths.len() {
            let mut whole_path = self.module_search_paths[i].clone();
            whole_path.push_str(&path);

            let whole_path = std::path::Path::new(&whole_path);
            if !whole_path.exists() {
                continue;
            }
            let saved = self.toplevel_cc.unwrap();
            self.toplevel_cc = Some(Compiler::new(self, Value::new_null()));
            let res = self.load_file(&whole_path, x);
            self.toplevel_cc = Some(saved);
            if res.exceptionp() {
                return res;
            }

            if self.module_loaded(x) {
                return self.modules.hash_get(self, x, Value::empty());
            }
        }

        let message = make_string(
            self,
            format!(
                "Failed to find module {}; searched paths: {:?}",
                x, self.module_search_paths
            ),
        );
        let kind = self.global(Global::ScmCompile);

        make_exception(
            self,
            kind,
            message,
            Value::new_null(),
            Value::new_null(),
            Value::new_null(),
        )
    }

    pub fn load_file(self, path: impl AsRef<std::path::Path>, x: Value) -> Value {
        let file = match std::fs::read_to_string(path) {
            Ok(src) => src,
            Err(e) => {
                panic!("failed to read: {}", e)
            }
        };
        if x.stringp() {
            self.toplevel_cc.unwrap().enter_module(x);
        } else {
            let tag = self.global(Global::ModuleName)?;
            let name = self.user_module.hash_get(self, tag, Value::new_null());
            self.toplevel_cc.unwrap().enter_module(name)?;
        }
        let parser = lexpr::Parser::from_str(&file);
        let proc = self.toplevel_cc.unwrap().compile_code(parser)?;

        crate::vm::apply(self, proc, &[])
    }
}

pub fn intern(mut ctx: ContextRef, s: impl AsRef<str>) -> Value {
    let s = s.as_ref();

    let bucket = crate::hash::hash32(s.as_bytes()) % ctx.symbols.vector_length() as u32;
    let mut ls = ctx.symbols.vector_ref(bucket as _);
    while ls.pairp() {
        if ls.car().symbol_name().string_data() == s {
            return ls.car();
        }
        ls = ls.cdr();
    }
    let sym = make_string(ctx, s);
    let sym = ctx.heap().allocate_tagged(
        Symbol {
            name: sym,
            value: Value::new_null(),
            module: Value::new_null(),
        },
        ValueType::Symbol as _,
        false,
        false,
    );
    let ls = ctx.symbols.vector_ref(bucket as _);
    let ls = make_pair(ctx, Value::new_cell(sym), ls);

    ctx.symbols.vector_set(bucket as _, ls);
    Value::new_cell(sym)
}

pub fn make_string(mut ctx: ContextRef, s: impl AsRef<str>) -> Value {
    unsafe {
        let s = s.as_ref();
        let bytes = s.as_bytes();
        let size = size_of::<Str>() + bytes.len() - 1;
        let mut str = ctx.heap().allocate_var(
            Str {
                length: 0,
                data: [0; 1],
            },
            ValueType::String as _,
            false,
            false,
            size,
        );
        str.length = bytes.len();
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), str.data.as_mut_ptr(), bytes.len());
        Value::new_cell(str)
    }
}

pub fn make_bytes(mut ctx: ContextRef, bytes: &[u8]) -> Value {
    unsafe {
        let size = size_of::<Bytes>() + bytes.len() - 1;
        let mut str = ctx.heap().allocate_var(
            Bytes {
                length: 0,
                data: [0; 1],
            },
            ValueType::Bytes as _,
            false,
            false,
            size,
        );
        str.length = bytes.len();
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), str.data.as_mut_ptr(), bytes.len());
        Value::new_cell(str)
    }
}

pub fn make_bytes2(mut ctx: ContextRef, count: usize, default: u8) -> Value {
    unsafe {
        let size = size_of::<Bytes>() + count - 1;
        let mut str = ctx.heap().allocate_var(
            Bytes {
                length: 0,
                data: [0; 1],
            },
            ValueType::Bytes as _,
            false,
            false,
            size,
        );
        str.length = count;
        std::ptr::write_bytes(str.data.as_mut_ptr(), default, count);
        Value::new_cell(str)
    }
}

pub fn make_vector(mut ctx: ContextRef, n: usize, default: Value) -> Value {
    unsafe {
        let size = size_of::<Vector>() + size_of::<Value>() * n;
        let mut v = ctx.heap().allocate_var(
            Vector {
                length: 0,
                data: [Value::new_null()],
            },
            ValueType::Vector as _,
            false,
            false,
            size,
        );
        for i in 0..n {
            v.data.as_mut_ptr().add(i).write(default);
        }
        v.length = n;
        Value::new_cell(v)
    }
}

pub fn make_hash(ctx: ContextRef, size: usize) -> Value {
    HashTable::new(
        ctx,
        size as _,
        crate::hash::equal_eq_fn,
        crate::hash::equal_hash_fn,
    )
}

pub fn make_synclo(mut ctx: ContextRef, env: Value, vars: Value, expr: Value) -> Value {
    Value::new_cell(ctx.heap().allocate_tagged(
        Synclo { env, vars, expr },
        ValueType::Synclo as _,
        false,
        false,
    ))
}

pub fn make_macro(mut ctx: ContextRef, proc: Value, env: Value) -> Value {
    Value::new_cell(ctx.heap().allocate_tagged(
        Macro {
            env,
            procedure: proc,
        },
        ValueType::Macro as _,
        false,
        false,
    ))
}

impl fmt::LowerHex for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> fmt::Result {
        write!(f, "Value({:x})", self.as_i64())
    }
}

impl fmt::UpperHex for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> fmt::Result {
        write!(f, "Value({:X})", self.as_i64())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(u8)]
pub enum Op {
    LoadN,
    LoadF,
    LoadI,
    LoadC,

    LocalRef,
    LocalSet,
    ClosureRef,
    ClosureSet,
    GlobalRef,
    GlobalSet,
    Pop,
    Dup,

    MakeClosure,

    Apply,
    TailApply,
    Jump,
    JumpIfFalse,
    JumpIfTrue,

    Return,
}

pub struct Frame {
    pub prev: *mut Frame,
    pub callee: Value,
    pub closure: Value,
    pub ip: *mut u8,
    pub bp: *mut Value,
    pub sp: u32,
    pub si: u32,
    pub locals: *mut Value,
    pub upvalues: *mut Value,
}

impl Frame {
    #[inline(always)]
    pub unsafe fn pop(&mut self) -> Value {
        self.si -= 1;
        self.bp.add(self.si as _).read()
    }
    #[inline(always)]
    pub unsafe fn push(&mut self, value: Value) {
        self.bp.add(self.si as _).write(value);
        self.si += 1;
    }

    #[inline(always)]
    pub unsafe fn slice(&self, count: usize) -> &[Value] {
        std::slice::from_raw_parts(self.bp.add(self.si as usize - count), count)
    }
}

#[repr(C)]
pub struct Stack {
    top: usize,
    pub(crate) current: *mut Frame,
    length: usize,
    data: [u8; 1],
}

impl Stack {
    pub(crate) fn new(ctx: &mut crate::Heap, size: usize) -> Gc<Self> {
        let size = size + size_of::<Self>();
        let p = ctx.allocate(Stack {
            top: 0,
            current: null_mut(),
            length: size,
            data: [0; 1],
        });

        p
    }

    pub unsafe fn make_frame(
        &mut self,
        callee: Value,
        closure: Value,
        args_on_stack: usize,
    ) -> *mut Frame {
        let stack_size = if callee.nativep() {
            size_of::<Frame>() + args_on_stack * 8
        } else {
            let proc = callee.downcast::<Procedure>(ValueType::Function as _);
            (proc.local_free_variable_count + proc.locals + proc.stack_max) as usize * 8
                + size_of::<Frame>()
        };
        let prev = self.top;
        let mem = self.alloc(stack_size).cast::<Frame>();
        if mem.is_null() {
            return null_mut();
        }
        (*mem).prev = self.current;
        (*mem).si = 0;
        (*mem).closure = closure;
        (*mem).callee = callee;

        (*mem).sp = prev as _;
        (*mem).bp = mem.cast::<u8>().add(size_of::<Frame>()).cast();
        if callee.procedurep() {
            let proc = callee.downcast::<Procedure>(ValueType::Function as _);
            (*mem).locals = (*mem).bp.add(proc.stack_max as _);
            (*mem).upvalues = (*mem).locals.add(proc.locals as _);
            (*mem).ip = proc.code.bvector_raw();
        } else {
            (*mem).ip = callee
                .downcast::<NativeProcedure>(ValueType::NativeFunction as _)
                .callback as *mut u8;
        }

        mem
    }

    pub unsafe fn leave_frame(&mut self, f: *mut Frame) {
        if (*f).callee.procedurep() {
            let proc = (*f).callee.downcast::<Procedure>(ValueType::Function as _);
            for i in 0..proc.local_free_variable_count {
                (*(*f).upvalues.add(i as _)).upvalue_close();
            }
        }
        self.top = (*f).sp as _;
        self.current = (*f).prev;
    }

    pub unsafe fn start(&mut self) -> *mut u8 {
        self.data.as_mut_ptr()
    }
    unsafe fn alloc(&mut self, size: usize) -> *mut u8 {
        let result = self.top;
        let new_top = self.top + size;
        if new_top >= self.length {
            return null_mut();
        }

        self.top = new_top;
        self.start().add(result)
    }
}

pub fn make_env(ctx: ContextRef, parent: Value, module_name: Option<&str>) -> Value {
    let table = make_hash(ctx, 4);
    if let Some(module_name) = module_name {
        let delegates = if parent.is_cell() {
            make_pair(ctx, parent, Value::new_null())
        } else {
            Value::new_null()
        };

        let unqualified = ctx.global(Global::UnqualifiedImports);

        table.hash_set(ctx, unqualified, delegates);

        let global = ctx.global(Global::GlobalEnvironment);
        let export_parent = ctx.global(Global::ExportParent);
        let exports_ = ctx.global(Global::Exports);
        let exporting = ctx.global(Global::Exporting);

        let exports = make_hash(ctx, 4);

        exports.hash_set(ctx, global, Value::new_bool(true));
        exports.hash_set(ctx, export_parent, table);

        table.hash_set(ctx, exports_, exports);

        let module_name = make_string(ctx, module_name);
        let mname = ctx.global(Global::ModuleName);
        table.hash_set(ctx, mname, module_name);

        table.hash_set(ctx, global, Value::new_bool(true));
        table.hash_set(ctx, exporting, Value::new_bool(false));
    } else {
        let p = ctx.global(Global::Parent);
        table.hash_set(ctx, p, parent);
    }

    table
}

pub fn make_exception(
    mut ctx: ContextRef,
    kind: Value,
    message: Value,
    irritants: Value,
    procedure: Value,
    stack_trace: Value,
) -> Value {
    Value::new_cell(ctx.heap().allocate_tagged(
        Exception {
            kind,
            message,
            irritants,
            procedure,
            stack_trace,
        },
        ValueType::Exception as _,
        false,
        false,
    ))
}

fn format(visited: &mut HashSet<Value>, val: Value, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if val.pairp() {
        if visited.contains(&val) {
            return write!(f, "<recur>");
        }
        visited.insert(val);
        write!(f, "(")?;
        format(visited, val.car(), f)?;
        let mut x = val.cdr();
        while x.pairp() {
            write!(f, " ")?;
            format(visited, x.car(), f)?;

            x = x.cdr();
        }
        if !x.is_null() {
            write!(f, " . ")?;
            format(visited, x, f)?;
        }
        write!(f, ")")?;
    } else if val.vectorp() {
        if visited.contains(&val) {
            return write!(f, "<recur>");
        }
        visited.insert(val);
        let n = val.vector_length();
        write!(f, "#(")?;
        for i in 0..n {
            format(visited, val.vector_ref(i), f)?;
            if i != n - 1 {
                write!(f, " ")?;
            }
        }
        write!(f, ")")?;
    } else if val.bvectorp() {
        write!(f, "#\"")?;
        for i in 0..val.bvector_length::<u8>() {
            write!(
                f,
                "{}",
                char::from_u32(val.bvector_ref::<u8>(i) as _).unwrap()
            )?;
        }
        write!(f, "\"")?;
    } else if val.closurep() {
        if visited.contains(&val) {
            return write!(f, "<recur>");
        }
        let proc = val.closure_procedure();
        write!(f, "#<closure ")?;
        format(visited, proc, f)?;
        write!(f, ">")?;
    } else if val.procedurep() {
        if visited.contains(&val) {
            return write!(f, "<recur>");
        }
        let proc = val.downcast::<Procedure>(ValueType::Function as _);
        if proc.name.is_null() {
            write!(f, "#<proc anonymous>")?;
        } else {
            write!(f, "#<proc ")?;
            format(visited, proc.name, f)?;
            write!(f, ">")?;
        }
    } else if val.nativep() {
        if visited.contains(&val) {
            return write!(f, "<recur>");
        }
        let proc = val.downcast::<NativeProcedure>(ValueType::NativeFunction as _);
        write!(
            f,
            "#<native-proc '{}' at {:p}>",
            proc.name, proc.callback as *mut u8
        )?;
    } else if val.macrop() {
        write!(f, "#<macro ")?;
        format(visited, val.macro_procedure(), f)?;
        write!(f, ">")?;
    } else if val.hashtablep() {
        if visited.contains(&val) {
            return write!(f, "<recur>");
        }
        visited.insert(val);
        let hash = val.downcast::<HashTable>(ValueType::HashTable as _);
        write!(f, "#(")?;
        let mut vals = vec![];
        hash.for_each(|key, val, _| {
            vals.push((key, val));
            Value::new_bool(true)
        });

        for (i, (k, v)) in vals.iter().enumerate() {
            write!(f, "(")?;
            format(visited, *k, f)?;
            write!(f, " . ")?;
            format(visited, *v, f)?;
            write!(f, ")")?;
            if i != vals.len() - 1 {
                write!(f, " ")?;
            }
        }
        write!(f, ")")?;
    } else if val.synclop() {
        write!(f, "#<SC")?;
        format(visited, val.synclo_expr(), f)?;
        write!(f, " ")?;
        format(visited, val.synclo_vars(), f)?;
        write!(f, " ")?;
        format(visited, val.synclo_env(), f)?;
    } else if val.symbolp() {
        write!(f, "{}", val.symbol_name().string_data())?;
    } else if val.stringp() {
        write!(f, "{}", val.string_data())?;
    } else if val.exceptionp() {
        let ex = val.downcast::<Exception>(ValueType::Exception as _);

        write!(f, "#<exception {}: {}>", ex.kind, ex.message)?;
    } else if val.is_int32() {
        write!(f, "{}", val.as_int32())?;
    } else if val.is_double() {
        write!(f, "{}", val.as_double())?;
    } else if val.is_undefined() {
        write!(f, "void")?;
    } else if val.is_null() {
        write!(f, "null")?;
    } else if val.is_empty() {
        write!(f, "#<empty>")?;
    } else if val.is_cell() {
        write!(
            f,
            "#<object {:p} of {:?}>",
            val.as_cell(),
            Gc::tag(val.as_cell())
        )?;
    } else if val.is_boolean() {
        write!(f, "{}", val.as_boolean())?;
    } else {
        write!(f, "#<value {:x}>", val)?;
    }
    visited.insert(val);

    Ok(())
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        format(&mut HashSet::with_capacity(2), *self, f)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CallResult {
    Done(Value),
    Trampoline,
}

pub fn lexpr_to_sexp(ctx: ContextRef, lexp: &lexpr::Value) -> Value {
    match lexp {
        lexpr::Value::Null | lexpr::Value::Nil => Value::new_null(),
        lexpr::Value::Cons(x) => {
            let car = lexpr_to_sexp(ctx, x.car());
            let cdr = lexpr_to_sexp(ctx, x.cdr());

            make_pair(ctx, car, cdr)
        }
        lexpr::Value::Vector(x) => {
            let v = make_vector(ctx, x.len(), Value::new_null());
            for (i, e) in x.iter().enumerate() {
                v.vector_set(i, lexpr_to_sexp(ctx, e));
            }
            v
        }
        lexpr::Value::Bytes(x) => {
            let v = make_bytes2(ctx, x.len(), 0);
            for (i, e) in x.iter().enumerate() {
                v.bvector_set::<u8>(i, *e);
            }
            v
        }
        lexpr::Value::String(x) => make_string(ctx, x),
        lexpr::Value::Symbol(x) => intern(ctx, x),
        lexpr::Value::Char(x) => Value::new_i32(*x as i32),
        lexpr::Value::Number(x) => {
            if let Some(i) = x.as_i64() {
                if i as i32 as i64 == i {
                    Value::new_i32(i as _)
                } else {
                    Value::new_f64(i as f64)
                }
            } else if let Some(f) = x.as_f64() {
                Value::new_f64(f)
            } else {
                todo!()
            }
        }

        lexpr::Value::Bool(x) => Value::new_bool(*x),
        lexpr::Value::Keyword(k) => intern(ctx, k),
    }
}

impl FromResidual<Self> for Value {
    fn from_residual(x: Value) -> Value {
        x
    }
}

impl Try for Value {
    type Output = Self;
    type Residual = Self;

    fn from_output(output: Self::Output) -> Self {
        output
    }

    fn branch(self) -> ControlFlow<Value, Value> {
        if self.exceptionp() {
            ControlFlow::Break(self)
        } else {
            ControlFlow::Continue(self)
        }
    }
}
