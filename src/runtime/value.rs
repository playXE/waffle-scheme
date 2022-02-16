use std::{
    hash::Hash,
    mem::size_of,
    ptr::NonNull,
    sync::atomic::{AtomicPtr, AtomicUsize},
};

use crate::{compiler::Op, method_jit::lower::FunctionLowerer, Heap, *};
use comet::{api::*, gc_base::AllocationSpace, mutator::MutatorRef};
use comet_extra::alloc::{array::Array, hash::HashMap, string::String, vector::Vector};

use super::{make_exception, make_string, make_vector, SchemeThread};

pub type TagKind = u32;

pub const FIRST_TAG: TagKind = 0xfff9;
pub const LAST_TAG: TagKind = 0xffff;
pub const EMPTY_INVALID_TAG: u32 = FIRST_TAG;
pub const UNDEFINED_NULL_TAG: u32 = FIRST_TAG + 1;
pub const BOOL_TAG: u32 = FIRST_TAG + 2;
pub const INT32_TAG: u32 = FIRST_TAG + 3;
pub const NATIVE_VALUE_TAG: u32 = FIRST_TAG + 4;
pub const STR_TAG: u32 = FIRST_TAG + 5;
pub const OBJECT_TAG: u32 = FIRST_TAG + 6;
pub const FIRST_PTR_TAG: u32 = STR_TAG;

#[repr(u32)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExtendedTag {
    Empty = EMPTY_INVALID_TAG * 2 + 1,
    Undefined = UNDEFINED_NULL_TAG * 2,
    Null = UNDEFINED_NULL_TAG * 2 + 1,
    Bool = BOOL_TAG * 2,
    Int32 = INT32_TAG * 2,
    Native1 = NATIVE_VALUE_TAG * 2,
    Native2 = NATIVE_VALUE_TAG * 2 + 1,
    Str1 = STR_TAG * 2,
    Str2 = STR_TAG * 2 + 1,
    Object1 = OBJECT_TAG * 2,
    Object2 = OBJECT_TAG * 2 + 1,
}

/// A NaN-boxed encoded value.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Value(u64);

impl Value {
    pub const NUM_TAG_EXP_BITS: u32 = 16;
    pub const NUM_DATA_BITS: u32 = (64 - Self::NUM_TAG_EXP_BITS);
    pub const TAG_WIDTH: u32 = 4;
    pub const TAG_MASK: u32 = (1 << Self::TAG_WIDTH) - 1;
    pub const DATA_MASK: u64 = (1 << Self::NUM_DATA_BITS as u64) - 1;
    pub const ETAG_WIDTH: u32 = 5;
    pub const ETAG_MASK: u32 = (1 << Self::ETAG_WIDTH) - 1;
    #[inline]
    pub const fn from_raw(x: u64) -> Self {
        Self(x)
    }
    #[inline]
    pub const fn get_tag(&self) -> TagKind {
        (self.0 >> Self::NUM_DATA_BITS as u64) as u32
    }
    #[inline]
    pub fn get_etag(&self) -> ExtendedTag {
        unsafe { std::mem::transmute((self.0 >> (Self::NUM_DATA_BITS as u64 - 1)) as u32) }
    }
    #[inline]
    pub const fn combine_tags(a: TagKind, b: TagKind) -> u32 {
        ((a & Self::TAG_MASK) << Self::TAG_WIDTH) | (b & Self::TAG_MASK)
    }
    #[inline]
    const fn internal_new(val: u64, tag: TagKind) -> Self {
        Self(val | ((tag as u64) << Self::NUM_DATA_BITS))
    }
    #[inline]
    const fn new_extended(val: u64, tag: ExtendedTag) -> Self {
        Self(val | ((tag as u64) << (Self::NUM_DATA_BITS - 1)))
    }
    #[inline]
    pub const fn encode_null_ptr_object_value() -> Self {
        Self::internal_new(0, OBJECT_TAG)
    }
    #[inline]
    pub fn encode_object_value<T: Collectable + ?Sized>(val: Managed<T>) -> Self {
        Self::internal_new(
            unsafe { std::mem::transmute::<_, usize>(val) } as _,
            OBJECT_TAG,
        )
    }

    #[inline]
    pub fn encode_object_value_raw(val: *mut HeapObjectHeader) -> Self {
        Self::internal_new(
            unsafe { std::mem::transmute::<_, usize>(val) } as _,
            OBJECT_TAG,
        )
    }
    #[inline]
    pub const fn encode_native_u32(val: u32) -> Self {
        Self::internal_new(val as _, NATIVE_VALUE_TAG)
    }
    #[inline]
    pub fn encode_native_pointer(p: *const ()) -> Self {
        Self::internal_new(p as _, NATIVE_VALUE_TAG)
    }
    #[inline]
    pub const fn encode_bool_value(val: bool) -> Self {
        Self::internal_new(val as _, BOOL_TAG)
    }
    #[inline]
    pub const fn encode_null_value() -> Self {
        Self::new_extended(0, ExtendedTag::Null)
    }
    #[inline]
    pub fn encode_int32(x: i32) -> Self {
        Self::internal_new(x as u32 as u64, INT32_TAG)
    }
    #[inline]
    pub const fn encode_undefined_value() -> Self {
        Self::new_extended(0, ExtendedTag::Undefined)
    }
    #[inline]
    pub const fn encode_empty_value() -> Self {
        Self::new_extended(0, ExtendedTag::Empty)
    }
    #[inline]
    pub fn encode_f64_value(x: f64) -> Self {
        Self::from_raw(x.to_bits())
    }

    #[inline]
    pub const fn encode_nan_value() -> Self {
        Self::from_raw(0x7ff8000000000000)
    }
    #[inline]
    pub fn encode_untrusted_f64_value(val: f64) -> Self {
        if val.is_nan() {
            return Self::encode_nan_value();
        }
        Self::encode_f64_value(val)
    }

    #[inline]
    pub fn update_pointer(&self, val: *const ()) -> Self {
        Self::internal_new(val as _, self.get_tag())
    }

    #[inline]
    pub unsafe fn unsafe_update_pointer(&mut self, val: *const ()) {
        self.0 = val as u64 | (self.get_tag() as u64) << Self::NUM_DATA_BITS as u64
    }

    #[inline]
    pub fn is_null(&self) -> bool {
        self.get_etag() == ExtendedTag::Null
    }
    #[inline]
    pub fn is_undefined(&self) -> bool {
        self.get_etag() == ExtendedTag::Undefined
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.get_etag() == ExtendedTag::Empty
    }

    #[inline]
    pub fn is_native_value(&self) -> bool {
        self.get_tag() == NATIVE_VALUE_TAG
    }

    #[inline]
    pub fn is_int32(&self) -> bool {
        self.get_tag() == INT32_TAG
    }

    #[inline]
    pub fn is_bool(&self) -> bool {
        self.get_tag() == BOOL_TAG
    }

    #[inline]
    pub fn is_object(&self) -> bool {
        self.get_tag() == OBJECT_TAG
    }

    #[inline]
    pub fn is_double(&self) -> bool {
        self.0 < ((FIRST_TAG as u64) << Self::NUM_DATA_BITS as u64)
    }

    #[inline]
    pub fn is_pointer(&self) -> bool {
        self.0 >= ((FIRST_PTR_TAG as u64) << Self::NUM_DATA_BITS as u64)
    }

    #[inline]
    pub fn get_raw(&self) -> u64 {
        self.0
    }

    #[inline]
    pub fn get_pointer(&self) -> *mut () {
        assert!(self.is_pointer());
        unsafe { std::mem::transmute((self.0 & Self::DATA_MASK) as usize) }
    }
    #[inline]
    pub fn get_int32(&self) -> i32 {
        assert!(self.is_int32());
        self.0 as u32 as i32
    }
    #[inline]
    pub fn get_double(&self) -> f64 {
        f64::from_bits(self.0)
    }
    #[inline]
    pub fn get_native_value(&self) -> i64 {
        assert!(self.is_native_value());
        (((self.0 & Self::DATA_MASK as u64) as i64) << (64 - Self::NUM_DATA_BITS as i64))
            >> (64 - Self::NUM_DATA_BITS as i64)
    }

    #[inline]
    pub fn get_native_u32(&self) -> u32 {
        assert!(self.is_native_value());
        self.0 as u32
    }

    #[inline]
    pub fn get_native_ptr(&self) -> *mut () {
        assert!(self.is_native_value());
        (self.0 & Self::DATA_MASK) as *mut ()
    }

    #[inline]
    pub fn get_bool(&self) -> bool {
        assert!(self.is_bool());
        (self.0 & 0x1) != 0
    }

    #[inline]
    pub fn get_object(&self) -> Managed<dyn Collectable> {
        assert!(self.is_object());
        unsafe { std::mem::transmute::<_, _>((self.0 & Self::DATA_MASK) as usize) }
    }
    #[inline]
    pub fn get_object_raw(&self) -> *mut HeapObjectHeader {
        assert!(self.is_object());
        unsafe { std::mem::transmute::<_, _>((self.0 & Self::DATA_MASK) as usize) }
    }

    /// Get number value from JS value.If value is int32 value then it is casted to f64.
    #[inline]
    pub fn get_number(&self) -> f64 {
        if self.is_int32() {
            return self.get_int32() as f64;
        }
        self.get_double()
    }

    pub unsafe fn set_no_barrier(&mut self, val: Self) {
        self.0 = val.0;
    }

    pub fn is_number(&self) -> bool {
        self.is_double() || self.is_int32()
    }

    pub fn same_value_impl(lhs: Self, rhs: Self, _zero: bool) -> bool {
        if lhs.is_number() {
            if !rhs.is_number() {
                return false;
            }

            let lhsn = lhs.get_number();
            let rhsn = rhs.get_number();
            if lhsn == rhsn {
                return true;
            }
            return lhsn.is_nan() && rhsn.is_nan();
        }

        if !lhs.is_object() || !rhs.is_object() {
            return lhs.get_raw() == rhs.get_raw();
        }
        if lhs.is_object()
            && rhs.is_object()
            && lhs.get_object().is::<ScmString>()
            && rhs.get_object().is::<ScmString>()
        {
            return unsafe {
                lhs.get_object().downcast_unchecked::<ScmString>().string
                    == rhs.get_object().downcast_unchecked::<ScmString>().string
            };
        }

        if lhs.is_object()
            && rhs.is_object()
            && lhs.get_object().is::<ScmSymbol>()
            && rhs.get_object().is::<ScmSymbol>()
        {
            return unsafe {
                lhs.get_object().downcast_unchecked::<ScmSymbol>().id
                    == rhs.get_object().downcast_unchecked::<ScmSymbol>().id
            };
        }
        lhs.get_raw() == rhs.get_raw()
    }
    pub fn same_value(x: Value, y: Value) -> bool {
        Self::same_value_impl(x, y, false)
    }
    pub fn same_value_zero(lhs: Self, rhs: Self) -> bool {
        Self::same_value_impl(lhs, rhs, true)
    }
}

unsafe impl Trace for Value {
    fn trace(&mut self, vis: &mut dyn comet::api::Visitor) {
        unsafe {
            if self.is_pointer() && !self.is_empty() {
                let mut base = NonNull::new_unchecked(std::mem::transmute(self.get_object_raw()));
                vis.mark_object(&mut base);
                // TODO: would not work on 32 bit targets (Who cares about 32 bit? lol)
                *self = Self::encode_object_value_raw(base.as_ptr());
            }
        }
    }
}

macro_rules! from_primitive {
    ($($t: ty),*) => {$(
        impl From<$t> for Value {
            fn from(x: $t) -> Self {
                if x as i32 as $t == x {
                    return Self::encode_int32(x as _);
                }
                Self::encode_f64_value(x as f64)
            }
        })*
    };
}

from_primitive!(u8, i8, u16, i16, u32, i32, u64, i64);

impl From<f32> for Value {
    fn from(x: f32) -> Self {
        if x.is_nan() {
            return Self::encode_nan_value();
        }
        Self::encode_f64_value(x as _)
    }
}

impl From<f64> for Value {
    fn from(x: f64) -> Self {
        if x.is_nan() {
            return Self::encode_nan_value();
        }
        Self::encode_f64_value(x as _)
    }
}

impl From<bool> for Value {
    fn from(x: bool) -> Self {
        Self::encode_bool_value(x)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Undefined;
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Null;

impl From<Null> for Value {
    fn from(_x: Null) -> Self {
        Self::encode_null_value()
    }
}

impl From<Undefined> for Value {
    fn from(_x: Undefined) -> Self {
        Self::encode_undefined_value()
    }
}
impl<T: Collectable> From<Managed<T>> for Value {
    fn from(x: Managed<T>) -> Self {
        Value::encode_object_value(x)
    }
}

impl Value {
    pub fn new<T: Into<Self>>(x: T) -> Self {
        T::into(x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_new_i32() {
        let val = Value::new(42);
        assert!(val.is_number());
        assert_eq!(val.get_number(), 42f64);
    }

    #[test]
    fn test_new_f64() {
        let val = Value::new(f64::NAN);
        assert!(val.is_number());
        assert!(val.get_number().is_nan());
    }
}

pub struct ScmString {
    pub(crate) string: String<Heap>,
}

#[repr(C)]
pub struct Rope {
    pub(crate) length: usize,
    pub(crate) data: RopeData,
}

pub enum RopeData {
    Leaf(Managed<comet_extra::alloc::string::Str>),
    Node(Managed<Rope>, Managed<Rope>),
}

impl RopeData {
    pub fn leaf(&self) -> Managed<comet_extra::alloc::string::Str> {
        match self {
            Self::Leaf(x) => *x,
            _ => debug_unreachable!(),
        }
    }
}

unsafe impl Trace for Rope {
    fn trace(&mut self, vis: &mut dyn comet::api::Visitor) {
        match &mut self.data {
            RopeData::Leaf(ref mut x) => x.trace(vis),
            RopeData::Node(ref mut x, ref mut y) => {
                x.trace(vis);
                y.trace(vis);
            }
        }
    }
}

unsafe impl Finalize for Rope {}
impl Collectable for Rope {}

impl ScmString {
    pub fn new(mutator: &mut MutatorRef<Heap>, str: impl AsRef<str>) -> Value {
        let str = str.as_ref();
        /*// we do not root leaf because it is instantly passed to `Str` so if GC will happen,
        // leaf will be traced too.
        let string = comet_extra::alloc::string::Str::new(mutator, str);
        let leaf = mutator.allocate(
            Rope {
                length: str.len(),
                data: RopeData::Leaf(string),
            },
            comet::gc_base::AllocationSpace::New,
        );
        unsafe {
            std::ptr::copy_nonoverlapping(str.as_ptr(), leaf.data.leaf().as_mut_ptr(), str.len());
        }
        */
        let str = String::from_str(mutator, str);
        Value::encode_object_value(
            mutator.allocate(ScmString { string: str }, AllocationSpace::New),
        )
    }
    pub fn to_string(&self) -> std::string::String {
        self.string.as_str().to_string()
    }

    pub fn len(&self) -> usize {
        self.string.len()
    }
}
impl Collectable for ScmString {}

unsafe impl Trace for ScmString {
    fn trace(&mut self, vis: &mut dyn Visitor) {
        self.string.trace(vis);
    }
}

unsafe impl Finalize for ScmString {}

pub struct HashValueZero(pub Value);

impl Hash for HashValueZero {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        if !self.0.is_object() {
            let raw = (self.0).0;
            raw.hash(state);
        } else if !self.0.is_empty() {
            let obj = self.0.get_object();
            if let Some(string) = obj.downcast::<ScmString>() {
                string.string.hash(state);
            } else if let Some(symbol) = obj.downcast::<ScmSymbol>() {
                symbol.id.hash(state);
            } else {
                // TODO: Find a better alternative. If Moving GC is enabled it is UB
                state.write_usize(unsafe { std::mem::transmute(obj) });
            }
        } else {
            state.write_u8(0xff);
        }
    }
}

impl PartialEq for HashValueZero {
    fn eq(&self, other: &Self) -> bool {
        Value::same_value(self.0, other.0)
    }
}

impl Eq for HashValueZero {}
unsafe impl Trace for HashValueZero {
    fn trace(&mut self, _vis: &mut dyn Visitor) {
        self.0.trace(_vis);
    }
}

pub struct ScmTable {
    pub table: HashMap<HashValueZero, Value, Heap>,
}

impl ScmTable {
    pub fn new(thread: &mut SchemeThread) -> Managed<ScmTable> {
        let map = HashMap::new(&mut thread.mutator);
        thread
            .mutator
            .allocate(Self { table: map }, AllocationSpace::New)
    }

    pub fn set(&mut self, thread: &mut SchemeThread, key: Value, val: Value) {
        self.table
            .insert(&mut thread.mutator, HashValueZero(key), val);
    }

    pub fn get(&self, key: Value) -> Option<Value> {
        self.table.get(&HashValueZero(key)).copied()
    }
    pub fn contains(&self, key: Value) -> bool {
        self.get(key).is_some()
    }

    pub fn keys(&self) -> Vec<std::string::String> {
        let mut keys = vec![];
        for (key, val) in self.table.iter() {
            keys.push(format!("{}->{}", key.0, val));
        }
        keys
    }
}

pub struct ScmVector {
    pub vec: Vector<Value, Heap>,
}

pub struct ScmException {
    pub tag: Managed<ScmSymbol>,
    pub message: Managed<ScmString>,
    pub irritants: Value,
}

pub struct ScmBox {
    pub value: Value,
}

pub struct ScmSymbol {
    pub id: u64,
    pub name: Value,
    pub value: Value,
    pub(crate) mutable: bool,
}

pub type ScmBlob = Managed<Array<u8>>;
/// Prototype for a function containing constants, code, and debugging
/// information. May be executed directly if the function does not reference
/// free variables.
#[allow(dead_code)]
pub struct ScmPrototype {
    pub(crate) constants: Vector<Value, Heap>,
    pub(crate) code: ScmBlob,
    pub(crate) debuginfo: ScmBlob,
    pub(crate) local_free_variables: ScmBlob,
    pub(crate) upvalues: ScmBlob,
    pub(crate) name: Option<Managed<ScmString>>,
    pub(crate) stack_max: u16,
    pub locals: u16,
    pub(crate) local_free_variable_count: u16,
    pub(crate) arguments: u16,
    pub(crate) variable_arity: bool,
    pub(crate) jit_code: AtomicPtr<u8>,
    pub(crate) n_calls: AtomicUsize,
    pub(crate) entry_points: HashMap<u32, u32, Heap>,
}

/// A closure, aka a function which references free variables
pub struct Closure {
    pub(crate) prototype: Managed<ScmPrototype>,
    pub(crate) upvalues: Vector<Value, Heap>,
}

unsafe impl Trace for ScmPrototype {
    fn trace(&mut self, vis: &mut dyn Visitor) {
        self.constants.trace(vis);
        self.code.trace(vis);
        self.debuginfo.trace(vis);
        self.local_free_variables.trace(vis);
        self.upvalues.trace(vis);
        self.name.trace(vis);
    }
}

unsafe impl Finalize for ScmPrototype {}
impl Collectable for ScmPrototype {}

unsafe impl Trace for Closure {
    fn trace(&mut self, _vis: &mut dyn Visitor) {
        self.prototype.trace(_vis);
        self.upvalues.trace(_vis);
    }
}
unsafe impl Finalize for Closure {}
impl Collectable for Closure {}

pub type NativeCallback = fn(&mut SchemeThread, args: &[Value]) -> Result<Value, Value>;
pub type NativeTransformer =
    fn(&mut FunctionLowerer, slow: &mut dyn FnMut(&mut FunctionLowerer) -> u32, u16) -> bool;
#[allow(dead_code)]
pub struct NativeFunction {
    pub(crate) callback: NativeCallback,
    pub(crate) arguments: usize,
    pub(crate) name: Value,
    pub(crate) variable_arity: bool,
    pub(crate) transformer: Option<NativeTransformer>,
}

pub struct Macro {
    pub(crate) p: Value,
}
unsafe impl Trace for Macro {
    fn trace(&mut self, _vis: &mut dyn Visitor) {
        self.p.trace(_vis);
    }
}

unsafe impl Finalize for Macro {}
impl Collectable for Macro {}

unsafe impl Trace for NativeFunction {
    fn trace(&mut self, vis: &mut dyn Visitor) {
        self.name.trace(vis);
    }
}
unsafe impl Finalize for NativeFunction {}
impl Collectable for NativeFunction {}
pub struct Upvalue {
    pub(crate) upval: Upval,
    pub(crate) closed: bool,
}

unsafe impl Trace for Upvalue {
    fn trace(&mut self, _vis: &mut dyn Visitor) {
        if self.closed {
            unsafe {
                self.upval.converted.trace(_vis);
            }
        } else {
            unsafe {
                (&mut *self.upval.local).trace(_vis);
            }
        }
    }
}
unsafe impl Finalize for Upvalue {}
impl Collectable for Upvalue {}

pub union Upval {
    pub(crate) local: *mut Value,
    pub(crate) converted: Value,
}
unsafe impl Trace for ScmVector {
    fn trace(&mut self, _vis: &mut dyn Visitor) {
        self.vec.trace(_vis)
    }
}

unsafe impl Finalize for ScmVector {}
impl Collectable for ScmVector {}
unsafe impl Trace for ScmTable {
    fn trace(&mut self, _vis: &mut dyn Visitor) {
        self.table.trace(_vis);
    }
}
unsafe impl Finalize for ScmTable {}
impl Collectable for ScmTable {}
unsafe impl Trace for ScmException {
    fn trace(&mut self, _vis: &mut dyn Visitor) {
        self.tag.trace(_vis);
        self.irritants.trace(_vis);
        self.message.trace(_vis);
    }
}
unsafe impl Finalize for ScmException {}
impl Collectable for ScmException {}
unsafe impl Trace for ScmBox {
    fn trace(&mut self, _vis: &mut dyn Visitor) {
        self.value.trace(_vis);
    }
}
unsafe impl Finalize for ScmBox {}
impl Collectable for ScmBox {}
unsafe impl Trace for ScmSymbol {
    fn trace(&mut self, _vis: &mut dyn Visitor) {
        self.name.trace(_vis);
        self.value.trace(_vis);
    }
}

unsafe impl Finalize for ScmSymbol {}
impl Collectable for ScmSymbol {}

pub struct ScmCons {
    pub car: Value,
    pub cdr: Value,
}

unsafe impl Trace for ScmCons {
    fn trace(&mut self, vis: &mut dyn Visitor) {
        self.car.trace(vis);
        self.cdr.trace(vis);
    }
}
unsafe impl Finalize for ScmCons {}
impl Collectable for ScmCons {}

impl Value {
    pub fn to_vec(self, thread: &mut SchemeThread) -> Result<Vec<Value>, Value> {
        let mut res = vec![];
        let mut el = self;
        while !el.is_null() {
            if !el.consp() {
                let tag = thread.runtime.global_symbol(runtime::Global::ScmEval);
                let msg = make_string(
                    thread,
                    "Only null terminated lists of cons cells can be converted to vec",
                );
                return Err(Value::new(make_exception(
                    thread,
                    tag,
                    msg,
                    Value::new(Null),
                )));
            }
            let cons = el.cons();
            res.push(cons.car);
            el = cons.cdr;
        }
        Ok(res)
    }
    pub fn to_vector(self, thread: &mut SchemeThread) -> Result<Value, Value> {
        let mut res = make_vector(thread, 4);
        let mut el = self;
        while !el.is_null() {
            if !el.consp() {
                let tag = thread.runtime.global_symbol(runtime::Global::ScmEval);
                let msg = make_string(
                    thread,
                    "Only null terminated lists of cons cells can be converted to vec",
                );
                return Err(Value::new(make_exception(
                    thread,
                    tag,
                    msg,
                    Value::new(Null),
                )));
            }
            let cons = el.cons();
            res.vec.push(&mut thread.mutator, cons.car);
            el = cons.cdr;
        }
        Ok(Value::new(res))
    }
    pub fn to_boolean(self) -> bool {
        if self.boolp() {
            self.get_bool()
        } else if self.is_null() || self.is_undefined() {
            false
        } else {
            true
        }
    }
    pub fn fixnump(self) -> bool {
        self.is_int32()
    }

    pub fn realp(self) -> bool {
        self.is_double()
    }

    pub fn boolp(self) -> bool {
        self.is_bool()
    }
    pub fn consp(self) -> bool {
        self.is_object() && self.get_object().is::<ScmCons>()
    }
    pub fn closurep(self) -> bool {
        self.is_object() && self.get_object().is::<Closure>()
    }
    pub fn native_functionp(self) -> bool {
        self.is_object() && self.get_object().is::<NativeFunction>()
    }
    pub fn symbolp(self) -> bool {
        self.is_object() && self.get_object().is::<ScmSymbol>()
    }
    pub fn tablep(self) -> bool {
        self.is_object() && self.get_object().is::<ScmTable>()
    }
    pub fn upvalue_addr(self) -> *mut Value {
        let mut upval = self.downcast::<Upvalue>();
        if upval.closed {
            unsafe { &mut upval.upval.converted }
        } else {
            unsafe { upval.upval.local }
        }
    }
    pub fn downcast<U: Collectable>(self) -> Managed<U> {
        debug_assert!(self.is_object() && self.get_object().is::<U>());
        unsafe { self.get_object().downcast_unchecked() }
    }
    pub fn table(self) -> Managed<ScmTable> {
        self.downcast()
    }
    pub fn cons(self) -> Managed<ScmCons> {
        self.downcast::<ScmCons>()
    }
    pub fn listp(self) -> bool {
        self.consp()
    }
    pub fn car(self) -> Value {
        self.cons().car
    }

    pub fn cdr(self) -> Value {
        self.cons().cdr
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

    pub fn cdar(self) -> Value {
        self.cdr().car()
    }

    pub fn caadr(self) -> Value {
        self.car().car().cdr()
    }

    pub fn caaar(self) -> Value {
        self.car().car().car()
    }

    pub fn cdadr(self) -> Value {
        self.cdr().car().cdr()
    }

    pub fn cdddr(self) -> Value {
        self.cdr().cdr().cdr()
    }

    pub fn list_ref(self, mut i: usize) -> Value {
        let mut lst = self;
        loop {
            if i == 0 {
                break;
            }
            lst = lst.car();
            i -= 1;
        }
        if !lst.is_null() {
            lst
        } else {
            Value::encode_bool_value(false)
        }
    }
    /// Compares `self` and `v` for equality.
    ///
    ///
    /// Behaviour:
    /// 1) If both values are fixnums they are compared for integer equality
    /// 2) If both values are reals they are compared for f64 equality
    /// 3) If one of values is fixnum and other value is real then integer is casted to f64 and step 2) is performed.
    /// 4) If both values are strings, strings are compared byte by byte
    /// 5) If both values are symbols, unqiue symbol identifiers are compared (can't compare symbols by pointers)
    /// 6) Otherwise values are compare by pointer/raw representation. It is safe because other types can't be hashed and even if GC decides to move them
    /// their locations will be updated and equality operation can be performed.
    pub fn eq(self, v: Value) -> bool {
        Value::same_value(self, v)
    }

    /// Walks cons-list and compares value `x` against the elements of the list.
    pub fn memq(self, x: Value) -> bool {
        let mut lst = self;
        while lst.consp() {
            if Value::same_value(lst.car(), x) {
                return true;
            }
            lst = lst.cdr();
        }
        false
    }

    pub fn set_car(self, x: Value) {
        self.cons().car = x;
    }

    pub fn set_cdr(self, x: Value) {
        self.cons().cdr = x;
    }
    pub fn vectorp(self) -> bool {
        self.is_object() && self.get_object().is::<ScmVector>()
    }
    pub fn vector_ref(self, i: usize) -> Value {
        *self.downcast::<ScmVector>().vec.at(i)
    }

    pub fn vector_set(self, at: usize, v: Value) {
        *self.downcast::<ScmVector>().vec.at_mut(at) = v;
    }

    pub fn vector_push(self, thread: &mut SchemeThread, val: Value) {
        self.downcast::<ScmVector>()
            .vec
            .push(&mut thread.mutator, val);
    }

    pub fn vector_length(self) -> usize {
        self.downcast::<ScmVector>().vec.len()
    }
    /// Same as [memq](Value::memq) but iterates vector instead.
    pub fn vector_memq(self, v: Value) -> bool {
        for i in 0..self.vector_length() {
            if Self::same_value(self.vector_ref(i), v) {
                return true;
            }
        }
        false
    }

    pub fn symbol_name(self) -> Managed<ScmString> {
        self.downcast::<ScmSymbol>().name.string()
    }

    pub fn blobp(self) -> bool {
        self.is_object() && self.get_object().is::<ScmBlob>()
    }

    pub fn blob_data(self) -> ScmBlob {
        self.downcast::<Array<u8>>()
    }

    pub fn blob_length(self) -> usize {
        self.blob_data().len()
    }

    /// Get value `T` stored in blob at `i * sizeof(T)`
    pub unsafe fn blob_ref<T: Copy>(self, i: usize) -> T {
        self.blob_data().as_ptr().cast::<T>().add(i).read()
    }

    /// Write value `T` at `i * sizeof(T)`
    pub unsafe fn blob_set<T: Copy>(self, i: usize, val: T) {
        self.blob_data().as_mut_ptr().cast::<T>().add(i).write(val);
    }

    pub fn stringp(self) -> bool {
        self.is_object() && self.get_object().is::<ScmString>()
    }

    pub fn string(self) -> Managed<ScmString> {
        self.downcast()
    }

    pub fn string_length(self) -> usize {
        self.string().len()
    }

    pub fn exceptionp(self) -> bool {
        self.is_object() && self.get_object().is::<ScmException>()
    }
    pub fn exception(self) -> Managed<ScmException> {
        self.downcast()
    }
    pub fn exception_tag(self) -> Managed<ScmSymbol> {
        self.exception().tag
    }

    pub fn exception_message(self) -> Managed<ScmString> {
        self.exception().message
    }

    pub fn exception_irritants(self) -> Value {
        self.exception().irritants
    }

    pub fn prototypep(self) -> bool {
        self.is_object() && self.get_object().is::<ScmPrototype>()
    }
    pub fn prototype(self) -> Managed<ScmPrototype> {
        self.downcast()
    }
    pub fn prototype_name(self) -> Option<Managed<ScmString>> {
        self.prototype().name
    }

    pub fn upvalue(self) -> Value {
        let u = self.downcast::<Upvalue>();
        if u.closed {
            unsafe { u.upval.converted }
        } else {
            unsafe { *u.upval.local }
        }
    }

    pub fn upvalue_set(self, v: Value) {
        let mut u = self.downcast::<Upvalue>();
        unsafe {
            if u.closed {
                u.upval.converted = v;
            } else {
                *u.upval.local = v;
            }
        }
    }

    pub fn upvalue_close(self) {
        let mut u = self.downcast::<Upvalue>();
        u.closed = true;
        unsafe {
            u.upval.converted = *u.upval.local;
        }
    }

    pub fn upvalue_closed(self) -> bool {
        self.downcast::<Upvalue>().closed
    }

    pub fn box_value(self) -> Value {
        self.downcast::<ScmBox>().value
    }

    pub fn try_cons(self) -> Option<Managed<ScmCons>> {
        if self.consp() {
            Some(self.cons())
        } else {
            None
        }
    }

    pub fn applicablep(self) -> bool {
        self.closurep() || self.prototypep() || self.native_functionp()
    }

    pub fn is_cell<T: Collectable>(self) -> bool {
        self.is_object() && self.get_object().is::<T>()
    }

    pub fn flonump(self) -> bool {
        self.is_double()
    }

    pub fn bignump(self) -> bool {
        self.is_cell::<ScmBignum>()
    }

    pub fn complexp(self) -> bool {
        self.is_cell::<ScmComplex>()
    }

    pub fn rationalp(self) -> bool {
        self.is_cell::<ScmRational>()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ValueType {
    Int,
    Real,
    Pair,
    Function,
    NativeFunction,
    Closure,
    Macro,
    Vector,
    Blob,
    Symbol,
    String,
    Table,
    Null,
    Undefined,
    Bool,
    Exception,
}

impl std::fmt::Display for ValueType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueType::Int => write!(f, "int"),
            ValueType::Real => write!(f, "real"),
            ValueType::Pair => write!(f, "pair"),
            ValueType::Function => write!(f, "function"),
            ValueType::NativeFunction => write!(f, "native-function"),
            ValueType::Closure => write!(f, "closure"),
            ValueType::Macro => write!(f, "macro"),
            ValueType::Vector => write!(f, "vector"),
            ValueType::Blob => write!(f, "blob"),
            ValueType::Symbol => write!(f, "symbol"),
            ValueType::String => write!(f, "string"),
            ValueType::Table => write!(f, "table"),
            ValueType::Null => write!(f, "null"),
            ValueType::Undefined => write!(f, "undefined"),
            ValueType::Bool => write!(f, "bool"),
            ValueType::Exception => write!(f, "exception"),
        }
    }
}

impl Value {
    pub fn typ(self) -> ValueType {
        if self.is_int32() {
            ValueType::Int
        } else if self.is_double() {
            ValueType::Real
        } else if self.consp() {
            ValueType::Pair
        } else if self.is_undefined() {
            ValueType::Undefined
        } else if self.is_null() {
            ValueType::Null
        } else if self.stringp() {
            ValueType::String
        } else if self.symbolp() {
            ValueType::Symbol
        } else if self.tablep() {
            ValueType::Table
        } else if self.vectorp() {
            ValueType::Vector
        } else if self.closurep() {
            ValueType::Closure
        } else if self.prototypep() {
            ValueType::Function
        } else if self.native_functionp() {
            ValueType::NativeFunction
        } else if self.exceptionp() {
            ValueType::Exception
        } else if self.blobp() {
            ValueType::Blob
        } else {
            todo!()
        }
    }
}

pub struct ScmComplex {
    pub complex: num::complex::Complex64,
}

unsafe impl Trace for ScmComplex {
    fn trace(&mut self, _vis: &mut dyn Visitor) {}
}
unsafe impl Finalize for ScmComplex {}
impl Collectable for ScmComplex {}

pub struct ScmRational {
    pub rational: num::BigRational,
}

unsafe impl Trace for ScmRational {
    fn trace(&mut self, _vis: &mut dyn Visitor) {}
}
unsafe impl Finalize for ScmRational {}
impl Collectable for ScmRational {}

pub struct ScmBignum {
    pub num: num::BigInt,
}

unsafe impl Trace for ScmBignum {
    fn trace(&mut self, _vis: &mut dyn Visitor) {}
}
unsafe impl Finalize for ScmBignum {}
impl Collectable for ScmBignum {}

pub fn print_bytecode(proto: Managed<ScmPrototype>) {
    println!("bytecode for {}:", Value::new(proto));
    println!(" constant pool: ");
    for (i, c) in proto.constants.iter().enumerate() {
        println!("  {:04}: {}", i, c);
    }

    let mut i = 0;
    println!(" code:");
    let ncode = proto.code.len() / size_of::<Op>();
    while i < ncode {
        let op = unsafe { proto.code.as_ptr().cast::<Op>().add(i).read() };
        i += 1;
        print!("  {:04}: ", i - 1);
        match op {
            Op::Apply(nargs) => println!("apply {}", nargs),
            Op::TailApply(nargs) => println!("tail-apply {}", nargs),
            Op::CloseOver => println!("close-over"),
            Op::GlobalGet => println!("global.get"),
            Op::GlobalSet => println!("global.set"),
            Op::LocalGet(x) => println!("local.get {}", x),
            Op::LocalSet(x) => println!("local.set {}", x),
            Op::UpvalueGet(x) => println!("upvalue.get {}", x),
            Op::UpvalueSet(x) => println!("upvalue.set {}", x),
            Op::Jump(x) => println!("jump {:04}", x),
            Op::JumpIfFalse(x) => println!("jump-if-false {:04}", x),
            Op::Pop => println!("pop"),
            Op::PushInt(x) => println!("push.i32 {}", x),
            Op::PushConstant(x) => println!("push.const {} ; {}", x, proto.constants[x as usize]),
            Op::PushFalse => println!("push.false"),
            Op::PushTrue => println!("push.true"),
            Op::PushNull => println!("push.null"),
            Op::Return => println!("return"),
            Op::LoopHint => println!("loophint"),
        }
    }
}
