pub const FNV_OFFSET_BASIS_32: u32 = 0x811c9dc5;

pub const FNV_PRIME_32: u32 = 0x01000193;

/// Computes 32-bits fnv1a hash of the given slice, or up-to limit if provided.
/// If limit is zero or exceeds slice length, slice length is used instead.
#[inline(always)]
pub const fn fnv1a_hash_32(bytes: &[u8], limit: Option<usize>) -> u32 {
    let mut hash = FNV_OFFSET_BASIS_32;

    let mut i = 0;
    let len = match limit {
        Some(v) => {
            if v <= bytes.len() && v > 0 {
                v
            } else {
                bytes.len()
            }
        }
        None => bytes.len(),
    };

    while i < len {
        hash ^= bytes[i] as u32;
        hash = hash.wrapping_mul(FNV_PRIME_32);
        i += 1;
    }
    hash
}
