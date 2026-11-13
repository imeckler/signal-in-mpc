//! THE server socket: the leader's TCP connection to the Signal server (or to the local Tor
//! client in front of it). The only holder of server sockets.
//!
//! What can go out on it (REORGANIZATION_PLAN.md 5.6), and nothing else:
//! - the SOCKS5 handshake of an agreed [`ServerOp::Connect`] (`socks.rs`);
//! - the bytes of an agreed [`ServerOp::Send`] (a TLS record the engines sealed and opened).
//!
//! [`ServerOp`] is the shell's whole instruction set for the server, with the pipe operation
//! codes of today's worker. `Close` (code 92) is new in S8, for connection rotation (X2); no
//! controller sends it yet.
use crate::socks::{self, Proxy};
use std::io::{self, Read, Write};
use std::net::{IpAddr, SocketAddr, TcpStream, ToSocketAddrs};
use std::time::Duration;

/// A whole TLS record's body is at most this long (`server_record`: "record bound").
pub const MAX_BODY: usize = 16640;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ServerOp {
    /// 9: host length 2, host, port 2; then, through a SOCKS5 proxy, the proxy part
    /// (`socks::parse_proxy`). Both parties agree on all of it, so neither can go direct while
    /// the other believes the connection is proxied, or use other credentials.
    Connect { host: Vec<u8>, port: u16, proxy: Option<Proxy> },
    /// 10: one TLS record to the server (the leader writes it; a write to a closed connection
    /// is dropped, and the next poll reports the closure to both parties).
    Send(Vec<u8>),
    /// 11: the next whole record (blocking).
    Receive,
    /// 17: a whole record if one is available, without blocking.
    Poll,
    /// 90: make connection `index` the active one (the next unused index opens a fresh one).
    Select(u8),
    /// 91: the active connection, reported closed, is replaced by a fresh one. Empty payload: the
    /// legacy library's TLS state of the connection too (it must have been retired). Payload `[1]`
    /// (STACK_NOTES J22: the Lean scripts own the connection's TLS state, `SIGNAL_SCRIPTS` with
    /// `tls`): the socket only; the legacy library's connection never left its fresh phase.
    Reset { legacy: bool },
    /// 92 (new): close the active connection's socket. Afterwards it counts as closed (91 resets it).
    Close,
}

impl ServerOp {
    pub const CONNECT: u8 = 9;
    pub const SEND: u8 = 10;
    pub const RECEIVE: u8 = 11;
    pub const POLL: u8 = 17;
    pub const SELECT: u8 = 90;
    pub const RESET: u8 = 91;
    pub const CLOSE: u8 = 92;

    pub fn is_server_op(code: u8) -> bool {
        matches!(code, 9 | 10 | 11 | 17 | 90 | 91 | 92)
    }

    /// The operation of a request, with today's shape checks.
    pub fn parse(code: u8, p: &[u8]) -> Result<ServerOp, String> {
        let need = |ok: bool, what: &str| if ok { Ok(()) } else { Err(what.to_string()) };
        match code {
            Self::CONNECT => {
                need(p.len() >= 5, "connect")?;
                let n = u16::from_be_bytes([p[0], p[1]]) as usize;
                need(p.len() >= n + 4 && n > 0, "connect shape")?;
                let host = p[2..2 + n].to_vec();
                let port = u16::from_be_bytes([p[2 + n], p[3 + n]]);
                let proxy = if p.len() > n + 4 { Some(socks::parse_proxy(p, n + 4).ok_or("proxy shape")?) } else { None };
                Ok(ServerOp::Connect { host, port, proxy })
            }
            Self::SEND => {
                need(p.len() >= 5 && p.len() <= 5 + MAX_BODY, "send")?;
                Ok(ServerOp::Send(p.to_vec()))
            }
            Self::RECEIVE => need(p.is_empty(), "receive").map(|_| ServerOp::Receive),
            Self::POLL => need(p.is_empty(), "poll").map(|_| ServerOp::Poll),
            Self::SELECT => need(p.len() == 1, "use connection").map(|_| ServerOp::Select(p[0])),
            Self::RESET => need(p.is_empty() || p == [1], "reset connection").map(|_| ServerOp::Reset { legacy: p.is_empty() }),
            Self::CLOSE => need(p.is_empty(), "close connection").map(|_| ServerOp::Close),
            _ => Err("not a server operation".into()),
        }
    }
}

/// Why no whole record could be read.
#[derive(Debug, PartialEq, Eq)]
pub enum RecordError {
    /// The server or the proxy closed the connection (or reading failed).
    Closed,
    /// A header announcing more than [`MAX_BODY`] bytes.
    Bound,
}

/// The leader's connection to the server.
pub struct Server {
    stream: TcpStream,
}

impl Server {
    /// A direct connection: the host is resolved here and the first address is used.
    pub fn connect_direct(host: &[u8], port: u16) -> Result<Server, String> {
        let name = std::str::from_utf8(host).map_err(|_| "resolve")?;
        let first: SocketAddr = (name, port).to_socket_addrs().ok().and_then(|mut a| a.next()).ok_or("resolve")?;
        let stream = TcpStream::connect(first).map_err(|_| "connect")?;
        Ok(Server { stream })
    }

    /// Through the SOCKS5 proxy (numeric address only), named by hostname.
    pub fn connect_proxied(via: &Proxy, host: &[u8], port: u16) -> Result<Server, String> {
        if host.is_empty() || host.len() > 255 || port == 0 {
            return Err("proxied endpoint".into());
        }
        let address: IpAddr = std::str::from_utf8(&via.host)
            .ok()
            .and_then(|h| h.parse().ok())
            .ok_or("proxy address (numeric only)")?;
        let mut stream = TcpStream::connect(SocketAddr::new(address, via.port)).map_err(|_| "proxy connect")?;
        // Building a circuit can take a while.
        stream.set_read_timeout(Some(Duration::from_secs(120))).map_err(|_| "proxy connect")?;
        socks::handshake(&mut stream, via, host, port)?;
        stream.set_read_timeout(None).map_err(|_| "proxy connect")?;
        Ok(Server { stream })
    }

    /// Writes one record. The caller drops a failure (see [`ServerOp::Send`]).
    pub fn send(&mut self, bytes: &[u8]) -> io::Result<()> {
        self.stream.write_all(bytes)?;
        self.stream.flush()
    }

    /// One whole record (blocking).
    pub fn record(&mut self) -> Result<Vec<u8>, RecordError> {
        let mut record = vec![0u8; 5];
        self.stream.read_exact(&mut record).map_err(|_| RecordError::Closed)?;
        let n = u16::from_be_bytes([record[3], record[4]]) as usize;
        if n > MAX_BODY {
            return Err(RecordError::Bound);
        }
        record.resize(5 + n, 0);
        self.stream.read_exact(&mut record[5..]).map_err(|_| RecordError::Closed)?;
        Ok(record)
    }

    /// Whether a read would not block now (data, end of stream or an error): `poll(…, 0) > 0`.
    pub fn readable(&self) -> bool {
        if self.stream.set_nonblocking(true).is_err() {
            return true;
        }
        let ready = match self.stream.peek(&mut [0u8; 1]) {
            Ok(_) => true,
            Err(e) => e.kind() != io::ErrorKind::WouldBlock,
        };
        let _ = self.stream.set_nonblocking(false);
        ready
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_shapes() {
        assert_eq!(
            ServerOp::parse(9, b"\x00\x03abc\x01\xbb").unwrap(),
            ServerOp::Connect { host: b"abc".to_vec(), port: 443, proxy: None }
        );
        assert_eq!(ServerOp::parse(9, b"\x00\x00\x01\xbb\x00").unwrap_err(), "connect shape");
        assert_eq!(ServerOp::parse(9, b"\x00\x05abc\x01").unwrap_err(), "connect shape");
        assert_eq!(ServerOp::parse(9, b"\x00\x03abc\x01\xbb\x00").unwrap_err(), "proxy shape");
        assert_eq!(ServerOp::parse(10, &[0; 4]).unwrap_err(), "send");
        assert!(ServerOp::parse(10, &vec![0; 5 + MAX_BODY]).is_ok());
        assert_eq!(ServerOp::parse(10, &vec![0; 6 + MAX_BODY]).unwrap_err(), "send");
        assert_eq!(ServerOp::parse(17, &[0]).unwrap_err(), "poll");
        assert_eq!(ServerOp::parse(90, &[3]).unwrap(), ServerOp::Select(3));
        assert_eq!(ServerOp::parse(90, &[]).unwrap_err(), "use connection");
        assert_eq!(ServerOp::parse(92, &[]).unwrap(), ServerOp::Close);
        assert!(ServerOp::parse(12, &[]).is_err());
    }
}
