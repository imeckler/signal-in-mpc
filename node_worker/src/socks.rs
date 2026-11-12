//! SOCKS5 (RFC 1928) with username/password (RFC 1929), for the leader's connection to the
//! server through a local Tor client (`tls_worker_v3.cpp` `socks_request`, `socks_connect`).
//!
//! The server is named by HOSTNAME (address type 3), so this worker never resolves it; the
//! proxy's own address must be numeric. Tor puts streams with different credentials on
//! different circuits (IsolateSOCKSAuth), so the credentials choose the circuit. The only method
//! offered is username/password. Tor is outside the MPC: it only ever sees TLS ciphertext.
//!
//! This module holds no socket: [`handshake`] runs over the stream `server.rs` opened, and
//! every byte it writes is built from the agreed connect request.
use std::io::{self, Read, Write};

/// The proxy part of an agreed connect request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proxy {
    pub host: Vec<u8>,
    pub port: u16,
    pub user: Vec<u8>,
    pub pass: Vec<u8>,
}

/// Parses the proxy part of a connect request from `at`: host length 2, host, port 2,
/// username length 1, username, password length 1, password; nothing after. Every field is
/// non-empty, the host at most 253 bytes, the port nonzero.
pub fn parse_proxy(p: &[u8], at: usize) -> Option<Proxy> {
    struct Cursor<'a> {
        p: &'a [u8],
        at: usize,
    }
    impl Cursor<'_> {
        fn number(&mut self, width: usize) -> Option<usize> {
            let end = self.at.checked_add(width).filter(|e| *e <= self.p.len())?;
            let n = self.p[self.at..end].iter().fold(0usize, |v, b| v << 8 | *b as usize);
            self.at = end;
            Some(n)
        }
        // A length of `width` bytes, then that many bytes (at least one).
        fn field(&mut self, width: usize) -> Option<Vec<u8>> {
            let n = self.number(width)?;
            let end = self.at.checked_add(n).filter(|e| n > 0 && *e <= self.p.len())?;
            let out = self.p[self.at..end].to_vec();
            self.at = end;
            Some(out)
        }
    }
    let mut c = Cursor { p, at };
    let host = c.field(2)?;
    if host.len() > 253 {
        return None;
    }
    let port = c.number(2)? as u16;
    let user = c.field(1)?;
    let pass = c.field(1)?;
    (c.at == p.len() && port > 0).then_some(Proxy { host, port, user, pass })
}

/// The bytes of the three client messages, for a given proxy and target.
pub fn greeting() -> Vec<u8> {
    vec![5, 1, 2]
}
pub fn authentication(via: &Proxy) -> Vec<u8> {
    let mut out = vec![1, via.user.len() as u8];
    out.extend_from_slice(&via.user);
    out.push(via.pass.len() as u8);
    out.extend_from_slice(&via.pass);
    out
}
pub fn connect_request(host: &[u8], port: u16) -> Vec<u8> {
    let mut out = vec![5, 1, 0, 3, host.len() as u8];
    out.extend_from_slice(host);
    out.extend_from_slice(&port.to_be_bytes());
    out
}

fn get<S: Read>(s: &mut S, n: usize) -> Result<Vec<u8>, String> {
    let mut b = vec![0u8; n];
    s.read_exact(&mut b).map_err(|e| match e.kind() {
        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut => "proxy timed out".to_string(),
        _ => "proxy closed".to_string(),
    })?;
    Ok(b)
}

/// The SOCKS5 exchange on an open stream to the proxy, ending with the stream connected to
/// `host:port` through it.
pub fn handshake<S: Read + Write>(s: &mut S, via: &Proxy, host: &[u8], port: u16) -> Result<(), String> {
    if host.is_empty() || host.len() > 255 || port == 0 {
        return Err("proxied endpoint".into());
    }
    let put = |s: &mut S, b: &[u8]| s.write_all(b).and_then(|_| s.flush()).map_err(|_| "proxy write".to_string());
    put(s, &greeting())?;
    if get(s, 2)? != [5, 2] {
        return Err("proxy refused username/password authentication".into());
    }
    put(s, &authentication(via))?;
    if get(s, 2)? != [1, 0] {
        return Err("proxy rejected the credentials".into());
    }
    put(s, &connect_request(host, port))?;
    let head = get(s, 4)?;
    if head[0] != 5 || head[1] != 0 || head[2] != 0 {
        return Err(format!("proxy could not reach the server (SOCKS reply {})", head[1]));
    }
    let bound = match head[3] {
        1 => 4,
        4 => 16,
        3 => get(s, 1)?[0] as usize,
        _ => 0,
    };
    if bound == 0 {
        return Err("proxy reply address".into());
    }
    get(s, bound + 2)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request_tail(host: &[u8], port: u16, user: &[u8], pass: &[u8]) -> Vec<u8> {
        let mut p = (host.len() as u16).to_be_bytes().to_vec();
        p.extend_from_slice(host);
        p.extend_from_slice(&port.to_be_bytes());
        p.push(user.len() as u8);
        p.extend_from_slice(user);
        p.push(pass.len() as u8);
        p.extend_from_slice(pass);
        p
    }

    #[test]
    fn parses_the_proxy_part() {
        let prefix = b"\x00\x0bchat.signal\x01\xbb".to_vec();
        let p = [prefix.clone(), request_tail(b"127.0.0.1", 9050, b"circuit-1", b"x")].concat();
        assert_eq!(
            parse_proxy(&p, prefix.len()),
            Some(Proxy { host: b"127.0.0.1".to_vec(), port: 9050, user: b"circuit-1".to_vec(), pass: b"x".to_vec() })
        );
        // Trailing byte, empty fields, zero port, truncation, an over-long host: refused.
        assert_eq!(parse_proxy(&[p.clone(), vec![0]].concat(), prefix.len()), None);
        assert_eq!(parse_proxy(&request_tail(b"h", 1, b"", b"x"), 0), None);
        assert_eq!(parse_proxy(&request_tail(b"h", 1, b"u", b""), 0), None);
        assert_eq!(parse_proxy(&request_tail(b"", 1, b"u", b"p"), 0), None);
        assert_eq!(parse_proxy(&request_tail(b"h", 0, b"u", b"p"), 0), None);
        let whole = request_tail(b"h", 1, b"u", b"p");
        for cut in 0..whole.len() {
            assert_eq!(parse_proxy(&whole[..cut], 0), None, "cut {cut}");
        }
        assert_eq!(parse_proxy(&request_tail(&[b'a'; 254], 1, b"u", b"p"), 0), None);
        assert!(parse_proxy(&request_tail(&[b'a'; 253], 1, b"u", b"p"), 0).is_some());
    }

    /// A stream that replays a proxy's answers and records what the client wrote.
    struct Scripted {
        answers: Vec<u8>,
        at: usize,
        written: Vec<u8>,
    }
    impl Read for Scripted {
        fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
            let n = out.len().min(self.answers.len() - self.at);
            out[..n].copy_from_slice(&self.answers[self.at..self.at + n]);
            self.at += n;
            Ok(n)
        }
    }
    impl Write for Scripted {
        fn write(&mut self, b: &[u8]) -> io::Result<usize> {
            self.written.extend_from_slice(b);
            Ok(b.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    fn via() -> Proxy {
        Proxy { host: b"127.0.0.1".to_vec(), port: 9050, user: b"u1".to_vec(), pass: b"pw".to_vec() }
    }

    #[test]
    fn handshake_bytes_are_exactly_the_three_requests() {
        let answers = [&[5u8, 2][..], &[1, 0], &[5, 0, 0, 1, 127, 0, 0, 1, 0x1f, 0x90]].concat();
        let mut s = Scripted { answers, at: 0, written: vec![] };
        handshake(&mut s, &via(), b"chat.signal.org", 443).unwrap();
        let want = [greeting(), authentication(&via()), connect_request(b"chat.signal.org", 443)].concat();
        assert_eq!(s.written, want);
        assert_eq!(want[..3], [5, 1, 2]);
        assert_eq!(&want[3..10], &[1, 2, b'u', b'1', 2, b'p', b'w']);
        assert_eq!(&want[10..15], &[5, 1, 0, 3, 15]);
        assert_eq!(s.at, s.answers.len());
    }

    #[test]
    fn handshake_refusals() {
        let cases: Vec<(Vec<u8>, &str)> = vec![
            (vec![5, 0], "proxy refused username/password authentication"),
            (vec![5, 2, 1, 1], "proxy rejected the credentials"),
            (vec![5, 2, 1, 0, 5, 2, 0, 1, 0, 0, 0, 0, 0, 0], "proxy could not reach the server (SOCKS reply 2)"),
            (vec![5, 2, 1, 0, 5, 0, 0, 3, 0], "proxy reply address"),
            (vec![5, 2, 1, 0, 5, 0, 0, 9], "proxy reply address"),
            (vec![5, 2, 1], "proxy closed"),
        ];
        for (answers, want) in cases {
            let mut s = Scripted { answers, at: 0, written: vec![] };
            assert_eq!(handshake(&mut s, &via(), b"h", 1).unwrap_err(), want);
        }
        let mut s = Scripted { answers: vec![], at: 0, written: vec![] };
        assert_eq!(handshake(&mut s, &via(), b"", 1).unwrap_err(), "proxied endpoint");
        assert_eq!(handshake(&mut s, &via(), b"h", 0).unwrap_err(), "proxied endpoint");
        assert!(s.written.is_empty());
    }
}
