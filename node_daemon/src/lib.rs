//! The node daemon and the application stand-in. See ../README.md.
//!
//! - `channels`: EVERY external input and output of the daemon (sockets, files, processes, the
//!   clock, randomness, signals, its standard streams), with typed messages. A reviewer reads
//!   `src/channels/` to see everything that enters or leaves a node daemon; a unit test
//!   (`channels/lint.rs`) fails if any other daemon source uses an I/O primitive.
//! - `scheduler`: the daemon's state machine (jobs, queue, sessions), calling only `channels`.
//! - `request`: the application's signed requests (the exact bytes the database nodes verify).
//! - `config`: the node's configuration (parsed here; its files are read through `channels`).
//!
//! Everything the daemon handles is public data.

pub mod channels;
pub mod config;
pub mod request;
pub mod scheduler;

pub use request::{ACCOUNT_ID, Kind, MAX_CLOCK_SKEW_SECS, MAX_IDS, Request};

use serde_json::Value;
use sha2::{Digest, Sha256};

/// The longest line either side of a connection accepts.
pub const MAX_LINE: u64 = 16 << 20;
/// The controller's limit on a notify text (bytes of UTF-8).
pub const MAX_MESSAGE_BYTES: usize = 256;

pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out.copy_from_slice(Sha256::digest(data).as_slice());
    out
}

pub fn hmac(key: &[u8], data: &[u8]) -> [u8; 32] {
    let mut block = [0u8; 64];
    if key.len() > 64 {
        block[..32].copy_from_slice(&sha256(key));
    } else {
        block[..key.len()].copy_from_slice(key);
    }
    let mut inner: Vec<u8> = block.iter().map(|b| b ^ 0x36).collect();
    inner.extend_from_slice(data);
    let mut outer: Vec<u8> = block.iter().map(|b| b ^ 0x5c).collect();
    outer.extend_from_slice(&sha256(&inner));
    sha256(&outer)
}

/// Equality of two secrets in time that depends on neither their contents nor their lengths:
/// their SHA-256 digests are compared with every byte examined.
pub fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    let (x, y) = (sha256(a), sha256(b));
    x.iter().zip(y.iter()).fold(0u8, |acc, (p, q)| acc | (p ^ q)) == 0
}

/// A 32-byte public key in base64 (as the database network config spells it).
pub fn public_key(text: &str) -> Result<[u8; 32], String> {
    use base64::Engine;
    let bytes = base64::engine::general_purpose::STANDARD.decode(text.trim()).map_err(|_| "public key is not base64")?;
    <[u8; 32]>::try_from(bytes.as_slice()).map_err(|_| "public key must be 32 bytes".to_string())
}

/// The digest both daemons' results must share: over the fields that are the same on both
/// nodes by construction. serde_json writes object keys in sorted order.
pub fn result_digest(common: &Value) -> String {
    hex::encode(sha256(common.to_string().as_bytes()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hmac_and_constant_time_eq() {
        // RFC 4231 test case 2.
        assert_eq!(hex::encode(hmac(b"Jefe", b"what do ya want for nothing?")), "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843");
        assert!(constant_time_eq(b"secret token", b"secret token"));
        assert!(!constant_time_eq(b"secret token", b"secret tokem"));
        assert!(!constant_time_eq(b"secret token", b"secret"));
        assert!(!constant_time_eq(b"", b"x"));
    }
}
