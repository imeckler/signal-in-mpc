//! Public differential oracle calling the actual pinned portable libcrux SHA3.
use std::io::{self,BufRead};
fn main() {
    for line in io::stdin().lock().lines() {
        let line=line.unwrap(); let fields:Vec<_>=line.split('|').collect();
        let mode=fields[0]; let count:usize=fields[1].parse().unwrap();
        let input:Vec<u8>=fields[2].as_bytes().chunks(2).map(|p|u8::from_str_radix(std::str::from_utf8(p).unwrap(),16).unwrap()).collect();
        let mut out=vec![0u8;count];
        match mode {
            "sha3-256"=>libcrux_sha3::portable::sha256(&mut out,&input),
            "sha3-512"=>libcrux_sha3::portable::sha512(&mut out,&input),
            "shake128"=>libcrux_sha3::portable::shake128(&mut out,&input),
            "shake256"=>libcrux_sha3::portable::shake256(&mut out,&input),
            _=>panic!("mode")
        }
        println!("{}",out.iter().map(|x|format!("{x:02x}")).collect::<String>());
    }
}
