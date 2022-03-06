use std::{mem::size_of, ptr::null_mut};

use crate::sexp::{r5rs_equal_pred, ContextRef, EqualFn, HashFn, HashTable, HashTableRec, Value};

const HASH_DEPTH_LIMIT: i32 = 100;

pub fn string_hash1(str: &str, bound: u32) -> u32 {
    let mut hash = 107u32;
    for b in str.bytes() {
        hash = hash.wrapping_mul(32).wrapping_sub(hash) + b as u32;
    }
    hash % bound
}

pub fn string_hash2(str: &str, bound: u32) -> u32 {
    let mut hash = 131;

    for b in str.bytes() {
        hash = hash * 4 + hash + b as u32;
    }
    hash %= bound;
    hash + (hash == 0) as u32
}

pub fn address1_hash(adrs: *mut (), bound: u32) -> u32 {
    let adrs = adrs as usize;
    (((adrs >> 3).wrapping_mul(2654435761) + (adrs & 7)) % bound as usize) as u32
}
pub fn address2_hash(adrs: *mut (), bound: u32) -> u32 {
    let hash = ((adrs as usize >> 3) * 13845163) % bound as usize;
    hash as u32 + (hash == 0) as u32
}
pub fn obj_hash(obj: Value, depth: i32, seed: u32) -> u32 {
    if depth > HASH_DEPTH_LIMIT {
        return 1;
    }
    if obj.is_cell() {
        if obj.pairp() {
            let hash1 = obj_hash(obj.car(), depth + 1, seed);
            return obj_hash(obj.cdr(), depth + 1, hash1);
        }

        if obj.vectorp() {
            let n = obj.vector_length();
            let mut hash = seed;
            for i in 0..n {
                hash = obj_hash(obj.vector_ref(i), depth + 1, hash);
            }
            hash = hash32_with_seed(&n.to_le_bytes(), hash);
            return hash;
        }

        if obj.symbolp() {
            let mut hash = hash32_with_seed(obj.symbol_name().string_data().as_bytes(), seed);
            if hash % (i32::MAX as u32) == 0 {
                hash = hash + 1;
            }
            return hash;
        }
        if obj.stringp() {
            return hash32_with_seed(obj.string_data().as_bytes(), seed); //string_hash1(obj.string_data(), i32::MAX as _);
        }
    }

    hash32_with_seed(&obj.as_i64().to_le_bytes(), seed)
}

impl HashTable {
    pub fn new(mut ctx: ContextRef, size: u32, eq_fn: EqualFn, hash_fn: HashFn) -> Value {
        let size = if size < 4 { 4 } else { size };

        unsafe {
            let elts = ctx
                .heap()
                .malloc(size_of::<*mut HashTableRec>() * size as usize)
                .cast::<*mut HashTableRec>();
            let table = ctx.heap().allocate_tagged(
                HashTable {
                    size,
                    count: 0,
                    elts,
                    eq_fn,
                    hash_fn,
                },
                crate::sexp::ValueType::HashTable as _,
                false,
                false,
            );

            Value::new_cell(table)
        }
    }

    fn resize(&mut self, mut ctx: ContextRef) -> Value {
        let size = self.size * 2;

        unsafe {
            let prev = self.elts;
            self.elts = ctx
                .heap()
                .malloc(size_of::<*mut HashTableRec>() * size as usize)
                .cast();
            let mut node;
            let mut next;
            for i in 0..self.size {
                node = prev.add(i as _).read();
                while !node.is_null() {
                    next = (*node).next;
                    let pos = (*node).hash % size;
                    (*node).next = self.elts.add(pos as _).read();

                    self.elts.add(pos as _).write(node);
                    node = next;
                }
            }
            ctx.heap().free(prev.cast());
            self.size = size;
            Value::new_null()
        }
    }

    pub fn remove(&mut self, mut ctx: ContextRef, key: Value) -> Value {
        let hash = (self.hash_fn)(ctx, key);

        if hash.exceptionp() {
            return hash;
        }
        let hash = hash.as_int32() as u32;

        let position = hash % self.size;

        unsafe {
            let mut node = self.elts.add(position as _).read();
            let mut prevnode = null_mut::<HashTableRec>();
            while !node.is_null() {
                let eq = (self.eq_fn)(ctx, (*node).key, key);
                if eq.exceptionp() {
                    return eq;
                }
                if (*node).hash == hash && !eq.is_false() {
                    if !prevnode.is_null() {
                        (*prevnode).next = (*node).next;
                    } else {
                        self.elts.add(position as _).write((*node).next);
                    }

                    ctx.heap().free(node.cast());

                    self.count -= 1;
                    return Value::new_bool(true);
                }
                node = (*node).next;
            }
        }

        Value::new_bool(false)
    }

    pub fn insert(&mut self, ctx: ContextRef, key: Value, value: Value) -> Value {
        let hash = (self.hash_fn)(ctx, key);

        if hash.exceptionp() {
            return hash;
        }
        let hash = hash.as_int32() as u32;

        let position = hash % self.size;

        unsafe {
            let mut node = self.elts.add(position as _).read();
            while !node.is_null() {
                let eq = (self.eq_fn)(ctx, key, (*node).key)?;
                if (*node).hash == hash && eq.is_true() {
                    (*node).value = value;
                    return Value::new_bool(false);
                }

                node = (*node).next;
            }
        }
        self.insert_slow(ctx, key, value, position as _, hash);

        Value::new_bool(true)
    }

    fn insert_slow(
        &mut self,
        mut ctx: ContextRef,
        key: Value,
        value: Value,
        mut pos: usize,
        hash: u32,
    ) {
        if self.count >= (self.size as f64 * 0.75) as u32 {
            self.resize(ctx);
            pos = (hash % self.size) as usize;
        }
        unsafe {
            let node = ctx
                .heap()
                .malloc(size_of::<HashTableRec>())
                .cast::<HashTableRec>();
            (*node).next = self.elts.add(pos).read();
            (*node).key = key;
            (*node).value = value;
            (*node).hash = hash;
            self.elts.add(pos).write(node);

            self.count += 1;
        }
    }

    pub fn lookup(&self, ctx: ContextRef, key: Value, failure_result: Value) -> Value {
        let hash = (self.hash_fn)(ctx, key);

        if hash.exceptionp() {
            return hash;
        }
        let hash = hash.as_int32() as u32;

        let position = hash % self.size;
        unsafe {
            let mut node = self.elts.add(position as _).read();
            while !node.is_null() {
                let eq = (self.eq_fn)(ctx, (*node).key, key);
                if eq.exceptionp() {
                    return eq;
                }

                if (*node).hash == hash && eq.is_true() {
                    //   println!("found {} {}", key, (*node).value);
                    return (*node).value;
                }
                node = (*node).next;
            }
        }
        // TODO: invoke it if it is function
        failure_result
    }

    pub fn for_each(&self, mut callback: impl FnMut(Value, Value, u32) -> Value) -> Value {
        unsafe {
            for i in 0..self.size {
                let mut node = self.elts.add(i as _).read();

                while !node.is_null() {
                    let res = callback((*node).key, (*node).value, (*node).hash);
                    if res.exceptionp() || res.is_false() {
                        return res;
                    }
                    node = (*node).next;
                }
            }
        }
        Value::new_bool(true)
    }
}

pub fn equal_hash_fn(_: ContextRef, v: Value) -> Value {
    Value::new_i32(obj_hash(v, 0, 0) as _)
}

pub fn equal_eq_fn(_: ContextRef, a: Value, b: Value) -> Value {
    Value::new_bool(r5rs_equal_pred(a, b))
}

// The code below is adapted from C++ code with the following disclaimer
//-----------------------------------------------------------------------------
// MurmurHash3 was written by Austin Appleby, and is placed in the public
// domain. The author hereby disclaims copyright to this source code.

/// MurmurHash3 32-bit implementation of the 32-bit hashing algorithm.
/// This version allows you to specify a seed.
pub fn hash32_with_seed<T: AsRef<[u8]>>(v: T, seed: u32) -> u32 {
    let data = v.as_ref().clone();
    let n_blocks = data.len() / 4;

    const C1: u32 = 0xcc9e2d51;
    const C2: u32 = 0x1b873593;
    const D: u32 = 0xe6546b64;

    let mut h1: u32 = seed;

    // body
    for i in 0..n_blocks {
        let mut k1 = get_u32(data, i * 4);

        k1 = k1.wrapping_mul(C1);
        k1 = k1.rotate_left(15);
        k1 = k1.wrapping_mul(C2);

        h1 ^= k1;
        h1 = h1.rotate_left(13);
        h1 = (h1.wrapping_mul(5)).wrapping_add(D);
    }

    // tail
    let tail = data.clone();
    let tail_num = n_blocks * 4;
    let mut k1 = 0;
    for i in (1..=data.len() & 3).rev() {
        match i {
            3 => k1 ^= (tail[tail_num + 2] as u32) << 16,
            2 => k1 ^= (tail[tail_num + 1] as u32) << 8,
            1 => {
                k1 ^= tail[tail_num] as u32;
                k1 = k1.wrapping_mul(C1);
                k1 = k1.rotate_left(15);
                k1 = k1.wrapping_mul(C2);
                h1 ^= k1;
            }
            _ => {} // should never occur
        }
    }

    // finalization
    h1 ^= data.len() as u32;
    h1 = fmix32(h1);

    h1
}

/// MurmurHash3 32-bit implementation of the 32-bit hashing algorithm.
/// The seed is always 0 in this version.
pub fn hash32<T: AsRef<[u8]>>(v: T) -> u32 {
    hash32_with_seed(v, 0)
}

#[inline(always)]
fn get_u32(data: &[u8], i: usize) -> u32 {
    let buf = [data[i], data[i + 1], data[i + 2], data[i + 3]];
    u32::from_le_bytes(buf)
}

#[inline(always)]
fn fmix32(h: u32) -> u32 {
    let mut input = h;
    input ^= input >> 16;
    input = input.wrapping_mul(0x85ebca6b);
    input ^= input >> 13;
    input = input.wrapping_mul(0xc2b2ae35);
    input ^= input >> 16;
    input
}
