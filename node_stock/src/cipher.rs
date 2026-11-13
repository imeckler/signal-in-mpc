//! Authenticated encryption of one item.
//!
//! Every item has its own key (the chain, chain.rs) and each key encrypts exactly one plaintext,
//! once (the producer chain is advanced before the record is written, store.rs `put`), so a fixed
//! all-zero nonce is safe. The associated data binds the item to its boot id, stock id, manifest,
//! shape and index (format.rs `item_aad`).
//!
//! `ChaChaCipher` is the production cipher: ChaCha20-Poly1305 (RFC 8439) from the vendored
//! `chacha20poly1305 = 0.11.0` (RustCrypto), available offline in `.deps/libsignal-vendor`.
//! `NullCipher` is FOR TESTS ONLY: it does not encrypt (the plaintext is on disk in the clear);
//! it keeps integrity with an HMAC-SHA256 tag under the item key, so the store's logic (wrong
//! key, wrong associated data, tampering) is exercised the same way.

use chacha20poly1305::{AeadInOut, ChaCha20Poly1305, KeyInit, Nonce, Tag};
use hmac::{Hmac, Mac};
use sha2::Sha256;
use zeroize::Zeroizing;

use crate::format::TAG_LEN;

pub trait ItemCipher {
    /// Encrypt `plain`; the result is `plain.len() + TAG_LEN` bytes.
    fn seal(&self, key: &[u8; 32], aad: &[u8], plain: &[u8]) -> Vec<u8>;
    /// Decrypt and verify; `None` if the key, the associated data or the bytes are wrong.
    fn open(&self, key: &[u8; 32], aad: &[u8], sealed: &[u8]) -> Option<Zeroizing<Vec<u8>>>;
}

/// ChaCha20-Poly1305 with a zero nonce (one key, one message).
#[derive(Clone, Copy, Debug, Default)]
pub struct ChaChaCipher;

impl ItemCipher for ChaChaCipher {
    fn seal(&self, key: &[u8; 32], aad: &[u8], plain: &[u8]) -> Vec<u8> {
        let c = ChaCha20Poly1305::new_from_slice(key).expect("32-byte key");
        let mut buf = plain.to_vec();
        let tag = c
            .encrypt_inout_detached(&Nonce::default(), aad, buf.as_mut_slice().into())
            .expect("item length within the cipher's limit");
        buf.extend_from_slice(&tag);
        buf
    }

    fn open(&self, key: &[u8; 32], aad: &[u8], sealed: &[u8]) -> Option<Zeroizing<Vec<u8>>> {
        if sealed.len() < TAG_LEN {
            return None;
        }
        let (ct, tag) = sealed.split_at(sealed.len() - TAG_LEN);
        let tag = Tag::try_from(tag).ok()?;
        let c = ChaCha20Poly1305::new_from_slice(key).ok()?;
        let mut buf = Zeroizing::new(ct.to_vec());
        c.decrypt_inout_detached(&Nonce::default(), aad, buf.as_mut_slice().into(), &tag).ok()?;
        Some(buf)
    }
}

/// TESTS ONLY. No confidentiality: the plaintext is stored as is, followed by a 16-byte
/// HMAC-SHA256 tag over (aad length, aad, plaintext) under the item key.
#[derive(Clone, Copy, Debug, Default)]
pub struct NullCipher;

impl NullCipher {
    fn tag(key: &[u8; 32], aad: &[u8], plain: &[u8]) -> [u8; TAG_LEN] {
        let mut m = <Hmac<Sha256> as KeyInit>::new_from_slice(key).expect("any key length");
        m.update(&(aad.len() as u64).to_le_bytes());
        m.update(aad);
        m.update(plain);
        let full = m.finalize().into_bytes();
        full[..TAG_LEN].try_into().expect("16 bytes")
    }
}

impl ItemCipher for NullCipher {
    fn seal(&self, key: &[u8; 32], aad: &[u8], plain: &[u8]) -> Vec<u8> {
        let mut out = plain.to_vec();
        out.extend_from_slice(&Self::tag(key, aad, plain));
        out
    }

    fn open(&self, key: &[u8; 32], aad: &[u8], sealed: &[u8]) -> Option<Zeroizing<Vec<u8>>> {
        if sealed.len() < TAG_LEN {
            return None;
        }
        let (pt, tag) = sealed.split_at(sealed.len() - TAG_LEN);
        let want = Self::tag(key, aad, pt);
        // constant-time comparison
        let mut diff = 0u8;
        for (a, b) in want.iter().zip(tag) {
            diff |= a ^ b;
        }
        (diff == 0).then(|| Zeroizing::new(pt.to_vec()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check<C: ItemCipher>(c: C, hides: bool) {
        let key = [3u8; 32];
        let plain = b"preprocessed item bytes".to_vec();
        let sealed = c.seal(&key, b"aad", &plain);
        assert_eq!(sealed.len(), plain.len() + TAG_LEN);
        assert_eq!(sealed[..plain.len()] != plain[..], hides);
        assert_eq!(c.open(&key, b"aad", &sealed).as_deref(), Some(&plain));
        assert!(c.open(&[4u8; 32], b"aad", &sealed).is_none(), "wrong key");
        assert!(c.open(&key, b"aae", &sealed).is_none(), "wrong associated data");
        for i in 0..sealed.len() {
            let mut t = sealed.clone();
            t[i] ^= 0x80;
            assert!(c.open(&key, b"aad", &t).is_none(), "tampered byte {i}");
        }
        assert!(c.open(&key, b"aad", &sealed[..sealed.len() - 1]).is_none());
    }

    #[test]
    fn chacha() {
        check(ChaChaCipher, true);
    }

    #[test]
    fn null() {
        check(NullCipher, false);
    }

    /// RFC 8439 section 2.8.2 test vector: the vendored crate is the real ChaCha20-Poly1305.
    #[test]
    fn chacha_rfc8439() {
        use crate::format::unhex;
        let key: [u8; 32] = unhex("808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f").unwrap().try_into().unwrap();
        let nonce = Nonce::try_from(&unhex("070000004041424344454647").unwrap()[..]).unwrap();
        let aad = unhex("50515253c0c1c2c3c4c5c6c7").unwrap();
        let pt = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
        let c = ChaCha20Poly1305::new_from_slice(&key).unwrap();
        let mut buf = pt.to_vec();
        let tag = c.encrypt_inout_detached(&nonce, &aad, buf.as_mut_slice().into()).unwrap();
        assert_eq!(crate::format::hex(&tag), "1ae10b594f09e26a7e902ecbd0600691");
        assert_eq!(crate::format::hex(&buf[..16]), "d31a8d34648e60db7b86afbc53ef7ec2");
    }
}
