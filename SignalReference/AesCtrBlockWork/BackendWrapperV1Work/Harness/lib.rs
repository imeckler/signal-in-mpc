//! Extraction roots only. All cryptographic/library computations call unchanged pinned crates.
use aes::cipher::{BlockCipherEncrypt, KeyInit};
pub fn encrypt_one(key: &[u8; 32], block: &mut [u8; 16]) {
    let cipher = aes::Aes256::new(key.into());
    cipher.encrypt_block(block.into());
}
pub fn encrypt_four(key: &[u8; 32], blocks: &mut [[u8; 16]; 4]) {
    let cipher = aes::Aes256::new(key.into());
    for block in blocks {
        cipher.encrypt_block(block.into());
    }
}
