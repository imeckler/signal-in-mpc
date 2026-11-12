//! Integers mod p = 2^255 - 19 in four little-endian 64-bit limbs: the stand-in engines'
//! arithmetic (test code only, clear values).
#![allow(dead_code)]

pub type Fe = [u64; 4];
pub const P: Fe = [0xffff_ffff_ffff_ffed, u64::MAX, u64::MAX, 0x7fff_ffff_ffff_ffff];

fn ge(a: &Fe, b: &Fe) -> bool {
    for i in (0..4).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}
fn raw_sub(a: &Fe, b: &Fe) -> Fe {
    let mut r = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (d, b1) = a[i].overflowing_sub(b[i]);
        let (d, b2) = d.overflowing_sub(borrow);
        r[i] = d;
        borrow = (b1 || b2) as u64;
    }
    r
}
fn raw_add(a: &Fe, b: &Fe) -> Fe {
    let mut r = [0u64; 4];
    let mut carry = 0u64;
    for i in 0..4 {
        let (s, c1) = a[i].overflowing_add(b[i]);
        let (s, c2) = s.overflowing_add(carry);
        r[i] = s;
        carry = (c1 || c2) as u64;
    }
    r
}
/// a + b mod p for a, b < p (the sum is below 2^256).
pub fn add(a: &Fe, b: &Fe) -> Fe {
    let s = raw_add(a, b);
    if ge(&s, &P) { raw_sub(&s, &P) } else { s }
}
pub fn sub(a: &Fe, b: &Fe) -> Fe {
    if ge(a, b) { raw_sub(a, b) } else { raw_sub(&raw_add(a, &P), b) }
}
pub fn mul(a: &Fe, b: &Fe) -> Fe {
    let mut r = [0u64; 4];
    for i in (0..256).rev() {
        r = add(&r, &r);
        if (b[i / 64] >> (i % 64)) & 1 == 1 {
            r = add(&r, a);
        }
    }
    r
}
pub fn inv(a: &Fe) -> Fe {
    let e = raw_sub(&P, &[2, 0, 0, 0]);
    let mut r = [1, 0, 0, 0];
    for i in (0..256).rev() {
        r = mul(&r, &r);
        if (e[i / 64] >> (i % 64)) & 1 == 1 {
            r = mul(&r, a);
        }
    }
    r
}
pub fn fe_of(b: &[u8; 32]) -> Fe {
    let mut r = [0u64; 4];
    for (i, limb) in r.iter_mut().enumerate() {
        *limb = u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap());
    }
    r
}
pub fn bytes_of(f: &Fe) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * i + 8].copy_from_slice(&f[i].to_le_bytes());
    }
    out
}
