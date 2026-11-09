#![allow(unexpected_cfgs)]
// PUBLIC-FIXTURE-only stdin oracle. Never link to a worker/provider/RPC.
use std::io::{self, BufRead};
use aes::cipher::{BlockCipherEncrypt, KeyInit, KeyIvInit, StreamCipher};
use serde_json::{json, Value};
fn bytes(v: &Value, field: &str) -> Vec<u8> {
    v[field].as_array().unwrap().iter().map(|x| u8::try_from(x.as_u64().unwrap()).unwrap()).collect()
}
fn run(v: &Value) -> Value {
    let mode = v["mode"].as_str().unwrap();
    if mode == "profile" {
        return json!({"forced_soft": cfg!(aes_backend="soft"), "pointer_bits": usize::BITS,
            "debug_assertions": cfg!(debug_assertions), "aes": "0.9.1", "ctr": "0.10.1"});
    }
    let key = bytes(v, "key");
    let plaintext = bytes(v, "plaintext");
    if mode == "aes" {
        if key.len() != 32 || plaintext.is_empty() || plaintext.len() % 16 != 0 || plaintext.len() > 128 {
            return json!({"accepted": false, "error": "shape"});
        }
        let cipher = aes::Aes256::new_from_slice(&key).unwrap();
        let mut blocks: Vec<aes::Block> = plaintext.chunks_exact(16)
            .map(|part| aes::Block::try_from(part).unwrap()).collect();
        if blocks.len() == 1 { cipher.encrypt_block(&mut blocks[0]); }
        else { cipher.encrypt_blocks(&mut blocks); }
        let ciphertext: Vec<u8> = blocks.iter().flat_map(|block| block.iter().copied()).collect();
        json!({"accepted": true, "ciphertext": ciphertext})
    } else if mode == "ctr" {
        let nonce = bytes(v, "nonce");
        if key.len() != 32 || nonce.len() != 16 || plaintext.len() > 8192 {
            return json!({"accepted": false, "error": "shape"});
        }
        let mut cipher = ctr::Ctr32BE::<aes::Aes256>::new_from_slices(&key, &nonce).unwrap();
        let mut ciphertext = plaintext.clone();
        let accepted = cipher.try_apply_keystream(&mut ciphertext).is_ok();
        json!({"accepted": accepted, "ciphertext": ciphertext,
            "preserved": !accepted && ciphertext == plaintext})
    } else { panic!("public fixture mode") }
}
fn main() {
    for line in io::stdin().lock().lines() {
        let v: Value = serde_json::from_str(&line.unwrap()).unwrap();
        println!("{}", run(&v));
    }
}
