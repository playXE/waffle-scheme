pub trait BitFieldTrait<const SHIFT: u64, const SIZE: u64> {
    const MASK: u64 = ((1 << SHIFT) << SIZE) - (1 << SHIFT);

    fn encode(value: u64) -> u64 {
        value.wrapping_shl(SHIFT as _)
    }
    fn update(previous: u64, value: u64) -> u64 {
        (previous & !Self::MASK) | Self::encode(value)
    }

    fn decode(value: u64) -> u64 {
        (value & Self::MASK).wrapping_shr(SHIFT as _)
    }
}

pub struct SizeBitField;
pub struct ImmutableBitfield;
pub struct FreeBitfield;
pub struct SyntaticBitfield;
pub struct LargeBitfield;

// TODO: Maybe make this large? This allows us up to 16GB large object size to be stored
impl BitFieldTrait<1, 12> for SizeBitField {}
impl BitFieldTrait<13, 1> for ImmutableBitfield {}
impl BitFieldTrait<14, 1> for FreeBitfield {}
impl BitFieldTrait<15, 1> for SyntaticBitfield {}
impl BitFieldTrait<16, 1> for LargeBitfield {}
