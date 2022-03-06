use std::fmt;
use std::marker::PhantomData;
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SmallTypeId(u32);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ConstantTypeId<T> {
    id: SmallTypeId,
    marker: PhantomData<T>,
}

impl<T: 'static> ConstantTypeId<T> {
    pub const ID: SmallTypeId = unsafe {
        let id = std::any::TypeId::of::<T>();
        let bytes: [u8; std::mem::size_of::<std::any::TypeId>()] = std::mem::transmute(id);
        let id = crate::fnv::fnv1a_hash_32(&bytes, None);
        SmallTypeId(id)
    };
}

impl fmt::Debug for SmallTypeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "SmallTypeId(0x{:X}", self.0)
    }
}

impl fmt::Display for SmallTypeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "SmallTypeId(0x{:X}", self.0)
    }
}
