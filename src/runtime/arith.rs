use crate::Managed;

use super::{
    make_bignum,
    value::{ScmBignum, ScmRational, Value},
    SchemeThread,
};

/*
use super::{
    make_bignum, make_string,
    value::{ScmBignum, ScmString, Value},
    SchemeThread,
};

const IEXPT_2N52: i64 = 0x10000000000000i64;
const IEXPT_2N53: i64 = 0x20000000000000i64;

fn bn_norm_pred(bn: Managed<ScmBignum>) -> bool {
    bn.count == 0 || bn.elements[bn.count as usize - 1] != 0
}

fn bn_dup(thread: &mut SchemeThread, bn: Managed<ScmBignum>) -> Managed<ScmBignum> {
    let mut new_bn = make_bignum(thread, bn.count);
    unsafe {
        std::ptr::copy_nonoverlapping(&bn.elements[0], &mut new_bn.elements[0], bn.count as _);
    }
    new_bn.count = bn.count;
    new_bn.sign = bn.sign;
    new_bn
}

const DIGIT_BIT: u64 = 64;
const DIGIT_BIT_MASK: u64 = u64::MAX;
const DIGIT_BIT_SHIFT_COUNT: u64 = 6;
type Digit2x = u128;
type SignedDigit = i64;
type SignedDigit2x = i128;

fn bn_flip2sc(mut bn: Managed<ScmBignum>) {
    let bn_count = bn.count;
    let mut acc = 1 as Digit2x;
    for i in 0..bn_count {
        acc = (!bn.elements[i as usize]) as Digit2x + acc;
        bn.elements[i as usize] = acc as u64;
        acc >>= DIGIT_BIT as Digit2x;
    }
}

fn bn_set_zero(mut bn: Managed<ScmBignum>) {
    bn.count = 0;
    bn.sign = 0;
}

fn bn_norm(mut bn: Managed<ScmBignum>) -> i32 {
    let bn_count = bn.count;
    if bn_count > 0 {
        let mut index = bn_count as i32 - 1;
        while bn.elements[index as usize] == 0 {
            index -= 1;
            if index < 0 {
                bn_set_zero(bn);
                return 0;
            }
        }

        bn.count = index as u32 + 1;
        return index as i32 + 1;
    }
    bn_set_zero(bn);
    0
}

fn bn_to_integer(thread: &mut SchemeThread, bn: Managed<ScmBignum>) -> Value {
    if bn.count == 0 {
        return Value::new(0i32);
    } else if bn.count == 1 {
        let mut n = bn.elements[0] as SignedDigit2x;
        if bn.sign < 0 {
            n = -n;
        }
        if n >= i32::MIN as SignedDigit2x && n <= i32::MAX as SignedDigit2x {
            return Value::new(n as i32);
        }
    }
    Value::new(bn_dup(thread, bn))
}

fn bn_demote(mut bn: Managed<ScmBignum>) -> Value {
    if bn.count == 0 {
        return Value::new(0i32);
    } else if bn.count == 1 {
        let mut n = bn.elements[0] as SignedDigit2x;
        if bn.sign < 0 {
            n = -n;
        }
        if n >= i32::MIN as SignedDigit2x && n <= i32::MAX as SignedDigit2x {
            return Value::new(n as i32);
        }
    }
    Value::new(bn)
}

fn bn_lognot(mut ans: Managed<ScmBignum>, obj: Managed<ScmBignum>) {
    let ans_count = ans.count;
    let obj_count = obj.count;
    for i in 0..ans_count {
        if i < obj_count {
            ans.elements[i as usize] = !obj.elements[i as usize];
        } else {
            ans.elements[i as usize] = (-1i64) as u64;
        }
    }
    bn_norm(ans);
}

fn bn_logand(
    mut ans: Managed<ScmBignum>,
    lhs: Managed<ScmBignum>,
    rhs: Managed<ScmBignum>,
    lhs2c: bool,
    rhs2c: bool,
) {
    let ans_count = ans.count;
    let lhs_count = lhs.count;
    let rhs_count = rhs.count;
    for i in 0..ans_count {
        let bit1 = if i < lhs_count {
            lhs.elements[i as usize]
        } else if lhs2c {
            DIGIT_BIT_MASK
        } else {
            0
        };
        let bit2 = if i < rhs_count {
            rhs.elements[i as usize]
        } else if rhs2c {
            DIGIT_BIT_MASK
        } else {
            0
        };
        ans.elements[i as usize] = bit1 & bit2;
    }
    bn_norm(ans);
}
fn bn_logior(
    mut ans: Managed<ScmBignum>,
    lhs: Managed<ScmBignum>,
    rhs: Managed<ScmBignum>,
    lhs2c: bool,
    rhs2c: bool,
) {
    let ans_count = ans.count;
    let lhs_count = lhs.count;
    let rhs_count = rhs.count;
    for i in 0..ans_count {
        let bit1 = if i < lhs_count {
            lhs.elements[i as usize]
        } else if lhs2c {
            DIGIT_BIT_MASK
        } else {
            0
        };
        let bit2 = if i < rhs_count {
            rhs.elements[i as usize]
        } else if rhs2c {
            DIGIT_BIT_MASK
        } else {
            0
        };
        ans.elements[i as usize] = bit1 | bit2;
    }
    bn_norm(ans);
}

fn bn_logxor(
    mut ans: Managed<ScmBignum>,
    lhs: Managed<ScmBignum>,
    rhs: Managed<ScmBignum>,
    lhs2c: bool,
    rhs2c: bool,
) {
    let ans_count = ans.count;
    let lhs_count = lhs.count;
    let rhs_count = rhs.count;
    for i in 0..ans_count {
        let bit1 = if i < lhs_count {
            lhs.elements[i as usize]
        } else if lhs2c {
            DIGIT_BIT_MASK
        } else {
            0
        };
        let bit2 = if i < rhs_count {
            rhs.elements[i as usize]
        } else if rhs2c {
            DIGIT_BIT_MASK
        } else {
            0
        };
        ans.elements[i as usize] = bit1 ^ bit2;
    }
    bn_norm(ans);
}

fn bn_add(mut ans: Managed<ScmBignum>, lhs: Managed<ScmBignum>, rhs: Managed<ScmBignum>) -> bool {
    let ans_count = ans.count;
    let lhs_count = lhs.count;
    let rhs_count = rhs.count;
    let mut acc = 0 as Digit2x;
    for i in 0..ans_count {
        if i < lhs_count {
            acc = acc + lhs.elements[i as usize] as Digit2x;
        }
        if i < rhs_count {
            acc = acc + rhs.elements[i as usize] as Digit2x;
        }
        ans.elements[i as usize] = acc as u64;
        acc >= DIGIT_BIT as Digit2x;
    }
    bn_norm(ans);
    acc != 0
}
fn bn_sub(mut ans: Managed<ScmBignum>, lhs: Managed<ScmBignum>, rhs: Managed<ScmBignum>) -> bool {
    let ans_count = ans.count;
    let lhs_count = lhs.count;
    let rhs_count = rhs.count;
    let mut acc = 0 as SignedDigit2x;
    for i in 0..ans_count {
        if i < lhs_count {
            acc = acc + lhs.elements[i as usize] as Digit2x as SignedDigit2x;
        }
        if i < rhs_count {
            acc = acc - rhs.elements[i as usize] as Digit2x as SignedDigit2x;
        }
        ans.elements[i as usize] = acc as u64;
        acc >= DIGIT_BIT as Digit2x as SignedDigit2x;
    }
    if acc >= 0 {
        bn_norm(ans);
        true
    } else {
        acc != 0
    }
}

pub fn cnvt_fixnum_to_string(
    thread: &mut SchemeThread,
    fixnum: i32,
    radix: i32,
) -> Managed<ScmString> {
    let mut value = fixnum;
    let mut buf = [0u8; 64];
    if value != 0 {
        let mut negative = false;
        if value < 0 {
            negative = true;
            value = -value;
        }
        let mut i = buf.len() - 1;
        while value != 0 {
            let digit = value % radix;
            value /= radix;
            if digit < 10 {
                buf[i] = digit as u8 + '0' as u8;
            } else {
                buf[i] = digit as u8 + 'a' as u8 - 10;
            }
            i -= 1;
        }
        if negative {
            buf[i] = '-' as u8;
            i -= 1;
        }
        unsafe {
            return make_string(thread, std::str::from_utf8_unchecked(&buf[i + 1..]));
        }
    }
    make_string(thread, "0")
}

pub fn decode_double(n: f64) -> (i64, i32, i32) {
    let bits = n.to_bits();
    let mut mant_bits = bits & (IEXPT_2N52 as u64 - 1);
    let sign_bits = bits >> 63;
    let exp_bits = (bits >> 52) & 0x7ff;

    if n == 0.0 {
        return (0, 0, if sign_bits > 0 { -1 } else { 1 });
    }
    if n.is_nan() {
        return (0x18000000000000, 972, 1);
    }

    if n.is_infinite() {
        return (0x10000000000000, 972, if sign_bits > 0 { -1 } else { 1 });
    }

    let exp = if exp_bits > 0 {
        exp_bits as i32 - 1023
    } else {
        -1022
    } - 52;
    let sign = if sign_bits > 0 { -1 } else { 1 };
    if exp_bits > 0 {
        mant_bits |= IEXPT_2N52 as u64;
    }
    (mant_bits as i64, exp, sign)
}

pub fn cnvt_number_to_string(thread: &mut SchemeThread, obj: Value, radix: i32) -> Value {
    if obj.fixnump() {
        return Value::new(cnvt_fixnum_to_string(thread, obj.get_int32(), radix));
    }

    todo!()
}
*/

pub fn arirth_add(thread: &mut SchemeThread, lhs: Value, rhs: Value) -> Value {
    if lhs.fixnump() {
        if rhs.fixnump() {
            let n = lhs.get_int32() as i64 + rhs.get_int32() as i64;
            if n >= i32::MIN as i64 && n <= i32::MAX as i64 {
                return Value::new(n as i32);
            }
            return Value::new(make_bignum(thread, num::BigInt::from(n)));
        }

        if rhs.flonump() {
            return Value::new(lhs.get_int32() as f64 + rhs.get_double());
        }

        if rhs.is_cell::<ScmBignum>() {
            let big = num::BigInt::from(lhs.get_int32())
                .checked_add(&rhs.downcast::<ScmBignum>().num)
                .unwrap();
            return Value::new(make_bignum(thread, big));
        }
    }

    if lhs.flonump() {
        if rhs.fixnump() {
            return Value::new(lhs.get_double() + rhs.get_int32() as f64);
        }
        if rhs.flonump() {
            return Value::new(lhs.get_double() + rhs.get_double());
        }

        if rhs.bignump() {}
    }
    todo!()
}
