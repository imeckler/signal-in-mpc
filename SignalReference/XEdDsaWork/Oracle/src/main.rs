// Calls the unchanged pinned libsignal-core and locked dalek public operations.
use std::io::{self, BufRead};
use curve25519_dalek::{montgomery::MontgomeryPoint, edwards::EdwardsPoint, scalar::Scalar};
use sha2::{Digest, Sha512};
fn bytes(s: &str) -> Vec<u8> {
    assert_eq!(s.len()%2,0);
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()
}
fn hex(b: &[u8]) -> String { b.iter().map(|x|format!("{x:02x}")).collect() }
fn main() {
    for line in io::stdin().lock().lines() {
        let line=line.unwrap(); let a:Vec<_>=line.split_whitespace().collect();
        match a[0] {
            "recover" => {
                let u: [u8;32]=bytes(a[1]).try_into().unwrap();
                let sign:u8=a[2].parse().unwrap();
                match MontgomeryPoint(u).to_edwards(sign) {
                    None => println!("none"),
                    Some(p) => println!("{}",hex(p.compress().as_bytes())),
                }
            }
            "double" => {
                let u: [u8;32]=bytes(a[1]).try_into().unwrap();
                let sign:u8=a[2].parse().unwrap();
                let hh:[u8;32]=bytes(a[3]).try_into().unwrap();
                let ss:[u8;32]=bytes(a[4]).try_into().unwrap();
                let p=MontgomeryPoint(u).to_edwards(sign).unwrap();
                let h=Scalar::from_canonical_bytes(hh).unwrap();
                let s=Scalar::from_bytes_mod_order(ss);
                let q=EdwardsPoint::vartime_double_scalar_mul_basepoint(&h,&(-p),&s);
                println!("{}",hex(q.compress().as_bytes()));
            }
            "sign" => {
                use rand::SeedableRng;
                let key=libsignal_core::curve::PrivateKey::deserialize(&bytes(a[1])).unwrap();
                let msg=if a[2]=="-" {vec![]} else {bytes(a[2])};
                let mut rng=rand::rngs::StdRng::seed_from_u64(71821);
                println!("{} {}",hex(&key.public_key().unwrap().serialize()),hex(&key.calculate_signature(&msg,&mut rng).unwrap()));
            }
            "verify" => {
                let key=libsignal_core::curve::PublicKey::deserialize(&bytes(a[1])).unwrap();
                let msg=if a[2]=="-" {vec![]} else {bytes(a[2])};
                println!("{}",key.verify_signature(&msg,&bytes(a[3])));
            }
            "reduce" => {
                let data:[u8;64]=bytes(a[1]).try_into().unwrap();
                println!("{}",hex(Scalar::from_bytes_mod_order_wide(&data).as_bytes()));
            }
            "hash" => {
                let hash=Sha512::digest(if a[1]=="-" {vec![]} else {bytes(a[1])});
                println!("{} {}",hex(&hash),hex(Scalar::from_bytes_mod_order_wide(hash.as_ref()).as_bytes()));
            }
            _ => panic!("mode"),
        }
    }
}
