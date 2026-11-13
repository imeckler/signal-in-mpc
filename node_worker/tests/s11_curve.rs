//! Stage S11: the Lean local curve arithmetic (`TlsMpc/Node/Local/Edwards.lean`) against an
//! independent implementation, curve25519-dalek (vendored; no libsodium binding is available
//! offline). The vectors are computed by the Lean definitions
//! (`tests/lean/S11Curve.lean` → `tests/s11_curve_vectors.txt`); every line is recomputed here.

use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
use curve25519_dalek::montgomery::MontgomeryPoint;
use curve25519_dalek::scalar::Scalar;

const VECTORS: &str = include_str!("s11_curve_vectors.txt");

fn unhex(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0, "hex length");
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex")).collect()
}

fn arr(s: &str) -> [u8; 32] {
    let v = unhex(s);
    assert_eq!(v.len(), 32, "32 bytes");
    let mut a = [0u8; 32];
    a.copy_from_slice(&v);
    a
}

/// p = 2^255 − 19, little-endian.
fn below_p(y: &[u8; 32]) -> bool {
    let mut p = [0xffu8; 32];
    p[0] = 0xed;
    p[31] = 0x7f;
    for i in (0..32).rev() {
        if y[i] != p[i] {
            return y[i] < p[i];
        }
    }
    false
}

/// libsodium's decoding rules: canonical y (below p), then the point must decompress.
fn decode(b: &[u8; 32]) -> Option<EdwardsPoint> {
    let mut y = *b;
    y[31] &= 127;
    if !below_p(&y) {
        return None;
    }
    CompressedEdwardsY(*b).decompress()
}

fn point(s: &str) -> EdwardsPoint {
    decode(&arr(s)).expect("vector point decodes")
}

fn enc(p: &EdwardsPoint) -> String {
    p.compress().to_bytes().iter().map(|b| format!("{b:02x}")).collect()
}

fn scalar(s: &str) -> Scalar {
    Scalar::from_bytes_mod_order(arr(s))
}

#[test]
fn lean_local_curve_matches_dalek() {
    let mut counts = std::collections::BTreeMap::new();
    for line in VECTORS.lines().filter(|l| !l.is_empty()) {
        let f: Vec<&str> = line.split(' ').collect();
        *counts.entry(f[0]).or_insert(0usize) += 1;
        match f[0] {
            "basemul" => assert_eq!(enc(&(ED25519_BASEPOINT_POINT * scalar(f[1]))), f[2], "{line}"),
            "add" => assert_eq!(enc(&(point(f[1]) + point(f[2]))), f[3], "{line}"),
            "sub" => assert_eq!(enc(&(point(f[1]) - point(f[2]))), f[3], "{line}"),
            "mul" => assert_eq!(enc(&(point(f[2]) * scalar(f[1]))), f[3], "{line}"),
            "mont" => {
                let u = point(f[1]).to_montgomery().to_bytes();
                assert_eq!(u.to_vec(), unhex(f[2]), "{line}");
            }
            "valid" => {
                let ok = match decode(&arr(f[1])) {
                    Some(p) => !p.is_small_order() && p.is_torsion_free(),
                    None => false,
                };
                assert_eq!(ok, f[2] == "1", "{line}");
            }
            "decode" => assert_eq!(decode(&arr(f[1])).is_some(), f[2] == "1", "{line}"),
            "liftu" => {
                let got = MontgomeryPoint(arr(f[1])).to_edwards(0).map(|p| enc(&p));
                // dalek's `to_edwards` takes u mod p; the Lean lift rejects u = −1 (y's denominator).
                let want = if f[2] == "none" { None } else { Some(f[2].to_string()) };
                assert_eq!(got, want, "{line}");
            }
            other => panic!("unknown vector kind {other}"),
        }
    }
    for kind in ["basemul", "add", "sub", "mul", "mont", "valid", "decode", "liftu"] {
        assert!(counts.get(kind).copied().unwrap_or(0) > 0, "no {kind} vectors");
    }
}
