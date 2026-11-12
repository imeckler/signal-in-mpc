//! Request agreement (`tls_worker_v3.cpp` `agree`, `await_peer`, and the prologue of
//! `dispatch`), now on the control link.
//!
//! Both workers must have been handed the same request: before acting on one, each sends
//! `SHA-256("tls-worker-v3:" ‖ session ‖ code ‖ sequence (8, big-endian) ‖ size (4) ‖ agreed)`
//! and compares it with the other's. `agreed` is the whole payload, except for operations
//! 36, 39, 47 and 53, whose payloads carry this party's PRIVATE bytes after a public prefix
//! (16 bytes for 36, none for the others): only the prefix and the total size are agreed.
//! Operation 8 (local abort) is never agreed.
//!
//! The wait for the other party's hash is bounded (`TLS_WORKER_PEER_WAIT`, default 180 s,
//! 0 = no bound): a peer whose controller died or hangs ends this party's session with a
//! reported failure instead of a wait without end.
use crate::link::{Link, LinkError, PeerFrame};
use sha2::{Digest, Sha256};
use std::time::Duration;

/// The agreed part of a request's payload.
pub fn agreed_part(code: u8, payload: &[u8]) -> Result<Vec<u8>, String> {
    if matches!(code, 36 | 39 | 47 | 53) {
        let open = if code == 36 { 16 } else { 0 };
        if payload.len() < open {
            return Err("private request shape".into());
        }
        let mut agreed = payload[..open].to_vec();
        agreed.extend_from_slice(&(payload.len() as u32).to_be_bytes());
        Ok(agreed)
    } else {
        Ok(payload.to_vec())
    }
}

/// The hash both parties compare.
pub fn request_hash(session: &str, code: u8, sequence: u64, agreed: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"tls-worker-v3:");
    h.update(session.as_bytes());
    h.update([code]);
    h.update(sequence.to_be_bytes());
    h.update((agreed.len() as u32).to_be_bytes());
    h.update(agreed);
    h.finalize().into()
}

/// Agree on one request with the other worker, or fail.
pub fn agree(link: &mut Link, session: &str, code: u8, sequence: u64, payload: &[u8], wait: Option<Duration>) -> Result<(), String> {
    let agreed = agreed_part(code, payload)?;
    let mine = request_hash(session, code, sequence, &agreed);
    link.send(&PeerFrame::Agreement(mine)).map_err(|e| format!("control link: {e}"))?;
    match link.recv(wait) {
        Ok(PeerFrame::Agreement(peer)) if peer == mine => Ok(()),
        Ok(PeerFrame::Agreement(_)) => Err("request disagreement".into()),
        Ok(other) => Err(format!("control link: expected an agreement, got {}", other.name())),
        Err(LinkError::Timeout) => Err(format!(
            "the other party did not reach operation {code} within {} s",
            wait.map(|w| w.as_secs()).unwrap_or(0)
        )),
        Err(e) => Err(format!("control link: {e}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cpp_frame(session: &str, code: u8, sequence: u64, agreed: &[u8]) -> Vec<u8> {
        // tls_worker_v3.cpp `agree`, byte for byte.
        let mut f = format!("tls-worker-v3:{session}").into_bytes();
        f.push(code);
        for i in (0..8).rev() {
            f.push((sequence >> (8 * i)) as u8);
        }
        for i in (0..4).rev() {
            f.push(((agreed.len() as u64) >> (8 * i)) as u8);
        }
        f.extend_from_slice(agreed);
        f
    }

    #[test]
    fn hash_is_the_cpp_frame_hash() {
        let s = "ab".repeat(32) + ":split:typed-open:stock=2,524288,4194304:field=16,128,2";
        let h = request_hash(&s, 12, 77, b"payload");
        let want: [u8; 32] = Sha256::digest(cpp_frame(&s, 12, 77, b"payload")).into();
        assert_eq!(h, want);
    }

    #[test]
    fn private_prefix_rule() {
        let mut p = vec![7u8; 16];
        p.extend_from_slice(&[9u8; 32]);
        assert_eq!(agreed_part(36, &p).unwrap(), [vec![7u8; 16], 48u32.to_be_bytes().to_vec()].concat());
        assert_eq!(agreed_part(39, &[1, 2, 3]).unwrap(), 3u32.to_be_bytes().to_vec());
        assert_eq!(agreed_part(47, &[5; 10]).unwrap(), 10u32.to_be_bytes().to_vec());
        assert_eq!(agreed_part(53, &[5; 32]).unwrap(), 32u32.to_be_bytes().to_vec());
        assert!(agreed_part(36, &[0; 15]).is_err());
        assert_eq!(agreed_part(37, &[1, 2]).unwrap(), vec![1, 2]);
        // Two different private payloads of one size agree; different public prefixes do not.
        let a = [vec![1u8; 16], vec![2u8; 32]].concat();
        let b = [vec![1u8; 16], vec![3u8; 32]].concat();
        let c = [vec![4u8; 16], vec![2u8; 32]].concat();
        assert_eq!(agreed_part(36, &a).unwrap(), agreed_part(36, &b).unwrap());
        assert_ne!(agreed_part(36, &a).unwrap(), agreed_part(36, &c).unwrap());
    }
}
