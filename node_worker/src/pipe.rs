//! The controller's pipe, unchanged from `tls_worker_v3.cpp` (`run`, lines 410-519) and
//! `TlsMpc/TlsWorkerPipe.lean`:
//! - request: operation 1 byte, sequence 8 bytes big-endian, size 4 bytes big-endian, payload
//!   (at most 2 MiB);
//! - reply: status 1 byte (0 ok, 1 rejected, then always empty), size 4 bytes, payload.
//!
//! Sequencing ([`Latch`]): requests must carry 0, 1, 2, ... ; the first wrong number or failed
//! operation makes the worker terminal, after which every request is refused except operation 8
//! (local abort), which is always answered and consumes no sequence number.
//!
//! The reply stream is a duplicate of the original stdout; stdout itself is pointed at stderr
//! ([`take_stdout`]), so nothing the engines print can corrupt the framing.
use std::fs::File;
use std::io::{self, Read, Write};
use std::os::fd::FromRawFd;

/// The request bound (`run`: "request bound"; TlsWorkerPipe.maxPayload).
pub const MAX_REQUEST: usize = 2 * 1024 * 1024;
pub const ABORT: u8 = 8;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Request {
    pub code: u8,
    pub sequence: u64,
    pub payload: Vec<u8>,
}

#[derive(Debug)]
pub enum PipeError {
    /// A request above [`MAX_REQUEST`]: the worker stops ("request bound").
    Bound,
    Io(io::Error),
}

/// Reads exactly `out.len()` bytes; false at end of stream (also part-way), as `read_exact` in C++.
fn fill<R: Read>(r: &mut R, out: &mut [u8]) -> Result<bool, PipeError> {
    let mut at = 0;
    while at < out.len() {
        match r.read(&mut out[at..]) {
            Ok(0) => return Ok(false),
            Ok(n) => at += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(PipeError::Io(e)),
        }
    }
    Ok(true)
}

/// The next request, or `None` when the controller closed the pipe (also in the middle of a
/// request, as today: the loop ends and the worker exits normally).
pub fn read_request<R: Read>(r: &mut R) -> Result<Option<Request>, PipeError> {
    let mut head = [0u8; 13];
    if !fill(r, &mut head)? {
        return Ok(None);
    }
    let sequence = u64::from_be_bytes(head[1..9].try_into().unwrap());
    let size = u32::from_be_bytes(head[9..13].try_into().unwrap()) as usize;
    if size > MAX_REQUEST {
        return Err(PipeError::Bound);
    }
    let mut payload = vec![0u8; size];
    if size > 0 && !fill(r, &mut payload)? {
        return Ok(None);
    }
    Ok(Some(Request { code: head[0], sequence, payload }))
}

/// A request as the controller frames it (`TlsWorkerPipe.frame`); for tests and tools.
pub fn encode_request(code: u8, sequence: u64, payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(13 + payload.len());
    out.push(code);
    out.extend_from_slice(&sequence.to_be_bytes());
    out.extend_from_slice(&(payload.len() as u32).to_be_bytes());
    out.extend_from_slice(payload);
    out
}

/// One reply. A rejection never carries a payload.
pub fn encode_reply(ok: bool, payload: &[u8]) -> Vec<u8> {
    let payload = if ok { payload } else { &[][..] };
    let mut out = Vec::with_capacity(5 + payload.len());
    out.push(if ok { 0 } else { 1 });
    out.extend_from_slice(&(payload.len() as u32).to_be_bytes());
    out.extend_from_slice(payload);
    out
}

pub fn write_reply<W: Write>(w: &mut W, ok: bool, payload: &[u8]) -> io::Result<()> {
    w.write_all(&encode_reply(ok, payload))?;
    w.flush()
}

/// The sequence check and failure latch of the C++ loop:
/// `if(failed||sequence!=expected++){failed=true;reply(false,{});continue;}`.
#[derive(Debug, Default)]
pub struct Latch {
    pub expected: u64,
    pub failed: bool,
}

impl Latch {
    /// True when the request may run. (As in C++, `expected` advances only while not failed.)
    pub fn admit(&mut self, sequence: u64) -> bool {
        if self.failed {
            return false;
        }
        let expected = self.expected;
        self.expected = self.expected.wrapping_add(1);
        if sequence != expected {
            self.failed = true;
            return false;
        }
        true
    }
    pub fn fail(&mut self) {
        self.failed = true;
    }
}

/// Keeps the original stdout as the reply stream and points stdout at stderr
/// (`int rpc=::dup(STDOUT_FILENO); ::dup2(STDERR_FILENO,STDOUT_FILENO)`).
pub fn take_stdout() -> io::Result<File> {
    // SAFETY: plain descriptor calls on this process's own standard descriptors; the
    // duplicate is owned by the returned File from here on.
    unsafe {
        let rpc = libc::dup(1);
        if rpc < 0 || libc::dup2(2, 1) < 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(File::from_raw_fd(rpc))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn request_round_trip() {
        let bytes = [encode_request(9, 0, b"\x00\x01a\x01\xbb"), encode_request(17, 1, b"")].concat();
        let mut r = &bytes[..];
        assert_eq!(read_request(&mut r).unwrap(), Some(Request { code: 9, sequence: 0, payload: b"\x00\x01a\x01\xbb".to_vec() }));
        assert_eq!(read_request(&mut r).unwrap(), Some(Request { code: 17, sequence: 1, payload: vec![] }));
        assert_eq!(read_request(&mut r).unwrap(), None);
    }

    #[test]
    fn framing_matches_the_lean_frame() {
        // TlsWorkerPipe.frame: [code] ++ uint 8 sequence ++ uint 4 payload.length ++ payload
        assert_eq!(
            encode_request(36, 0x0102030405060708, &[0xaa, 0xbb]),
            vec![36, 1, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0, 2, 0xaa, 0xbb]
        );
        assert_eq!(encode_reply(true, &[7, 8]), vec![0, 0, 0, 0, 2, 7, 8]);
        assert_eq!(encode_reply(false, &[7, 8]), vec![1, 0, 0, 0, 0]);
    }

    #[test]
    fn truncated_request_ends_the_loop() {
        let full = encode_request(39, 0, &[1, 2, 3, 4]);
        for cut in [1, 12, 13, 15] {
            let mut r = &full[..cut];
            assert_eq!(read_request(&mut r).unwrap(), None, "cut at {cut}");
        }
    }

    #[test]
    fn oversized_request_is_refused_before_reading_it() {
        let mut head = vec![12u8];
        head.extend_from_slice(&0u64.to_be_bytes());
        head.extend_from_slice(&((MAX_REQUEST + 1) as u32).to_be_bytes());
        let mut r = &head[..];
        assert!(matches!(read_request(&mut r), Err(PipeError::Bound)));
        let mut ok = head.clone();
        ok[9..13].copy_from_slice(&(MAX_REQUEST as u32).to_be_bytes());
        ok.extend(std::iter::repeat(0).take(MAX_REQUEST));
        let mut r = &ok[..];
        assert_eq!(read_request(&mut r).unwrap().unwrap().payload.len(), MAX_REQUEST);
    }

    #[test]
    fn latch_is_terminal_after_a_wrong_sequence() {
        let mut l = Latch::default();
        assert!(l.admit(0));
        assert!(l.admit(1));
        assert!(!l.admit(3));
        assert!(l.failed);
        assert!(!l.admit(2));
        assert!(!l.admit(3));
    }

    #[test]
    fn latch_is_terminal_after_a_failure() {
        let mut l = Latch::default();
        assert!(l.admit(0));
        l.fail();
        assert!(!l.admit(1));
    }
}
