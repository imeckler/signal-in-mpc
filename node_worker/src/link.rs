//! THE control link to the other worker: a TCP connection of its own at PORT+20 (inside the
//! deployment's WireGuard tunnel), separate from the engines' links (PORT and its siblings,
//! PORT+10). Party 0 listens, party 1 dials, as for the engines.
//!
//! [`PeerFrame`] is everything this worker's shell can put on it (REORGANIZATION_PLAN.md 5.6):
//! - `Hello`: once, at start: the session id and the frame-set version, compared;
//! - `Agreement`: a 32-byte hash. Per request (`agree.rs`), and once at start for the circuit
//!   manifest (`loader.rs`);
//! - `Exchange`: exactly the payload of an agreed operation 39 from Lean (values the controller
//!   has decided are safe to show the other party, such as parity shares of a check);
//! - `ServerRecord`, `ServerClosed`: leader to follower only. A record the leader read from the
//!   server (public TLS ciphertext; empty = none available yet), or the news that the server or
//!   proxy closed the connection.
//!
//! Wire format: tag (1 byte), body size (4 bytes, big-endian), body. Each tag has a fixed or
//! bounded body size, checked before anything is allocated.
use std::fmt;
use std::io::{self, Read, Write};
use std::net::{Ipv4Addr, SocketAddrV4, TcpListener, TcpStream};
use std::time::{Duration, Instant};

pub const LINK_VERSION: u16 = 1;
/// The control link listens on the worker's PORT + this.
pub const PORT_OFFSET: u32 = 20;
/// Operation 39's bound (`dispatch`: "exchange").
pub const MAX_EXCHANGE: usize = 65536;
/// A TLS record as the shell forwards it: header and at most 16640 bytes (`server_record`).
pub const MAX_RECORD: usize = 5 + 16640;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PeerFrame {
    Hello { session: [u8; 32], version: u16 },
    Agreement([u8; 32]),
    Exchange(Vec<u8>),
    ServerRecord(Vec<u8>),
    ServerClosed,
}

#[derive(Debug)]
pub enum LinkError {
    /// The bounded wait ran out before the other worker sent anything.
    Timeout,
    /// The other worker closed the link.
    Closed,
    Malformed(&'static str),
    Io(io::Error),
}

impl fmt::Display for LinkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LinkError::Timeout => write!(f, "timed out"),
            LinkError::Closed => write!(f, "closed by the other worker"),
            LinkError::Malformed(what) => write!(f, "malformed frame ({what})"),
            LinkError::Io(e) => write!(f, "{e}"),
        }
    }
}

impl PeerFrame {
    fn tag(&self) -> u8 {
        match self {
            PeerFrame::Hello { .. } => 1,
            PeerFrame::Agreement(_) => 2,
            PeerFrame::Exchange(_) => 3,
            PeerFrame::ServerRecord(_) => 4,
            PeerFrame::ServerClosed => 5,
        }
    }
    pub fn name(&self) -> &'static str {
        match self {
            PeerFrame::Hello { .. } => "hello",
            PeerFrame::Agreement(_) => "agreement",
            PeerFrame::Exchange(_) => "exchange",
            PeerFrame::ServerRecord(_) => "server record",
            PeerFrame::ServerClosed => "server closed",
        }
    }
    /// (smallest, largest) body for a tag; None for an unknown tag.
    fn body_bounds(tag: u8) -> Option<(usize, usize)> {
        match tag {
            1 => Some((34, 34)),
            2 => Some((32, 32)),
            3 => Some((1, MAX_EXCHANGE)),
            4 => Some((0, MAX_RECORD)),
            5 => Some((0, 0)),
            _ => None,
        }
    }
    pub fn encode(&self) -> Vec<u8> {
        let body: Vec<u8> = match self {
            PeerFrame::Hello { session, version } => [&session[..], &version.to_be_bytes()[..]].concat(),
            PeerFrame::Agreement(h) => h.to_vec(),
            PeerFrame::Exchange(b) | PeerFrame::ServerRecord(b) => b.clone(),
            PeerFrame::ServerClosed => vec![],
        };
        let mut out = Vec::with_capacity(5 + body.len());
        out.push(self.tag());
        out.extend_from_slice(&(body.len() as u32).to_be_bytes());
        out.extend_from_slice(&body);
        out
    }
    pub fn decode(tag: u8, body: Vec<u8>) -> Result<PeerFrame, LinkError> {
        let (lo, hi) = Self::body_bounds(tag).ok_or(LinkError::Malformed("tag"))?;
        if body.len() < lo || body.len() > hi {
            return Err(LinkError::Malformed("size"));
        }
        Ok(match tag {
            1 => PeerFrame::Hello {
                session: body[..32].try_into().unwrap(),
                version: u16::from_be_bytes([body[32], body[33]]),
            },
            2 => PeerFrame::Agreement(body[..].try_into().unwrap()),
            3 => PeerFrame::Exchange(body),
            4 => PeerFrame::ServerRecord(body),
            _ => PeerFrame::ServerClosed,
        })
    }
    /// Reads one frame from any byte stream (the link, or a test buffer).
    pub fn read_from<R: Read>(r: &mut R) -> Result<PeerFrame, LinkError> {
        let mut head = [0u8; 5];
        read_all(r, &mut head)?;
        let (_, hi) = Self::body_bounds(head[0]).ok_or(LinkError::Malformed("tag"))?;
        let size = u32::from_be_bytes(head[1..5].try_into().unwrap()) as usize;
        if size > hi {
            return Err(LinkError::Malformed("size"));
        }
        let mut body = vec![0u8; size];
        read_all(r, &mut body)?;
        Self::decode(head[0], body)
    }
}

fn read_all<R: Read>(r: &mut R, out: &mut [u8]) -> Result<(), LinkError> {
    let mut at = 0;
    while at < out.len() {
        match r.read(&mut out[at..]) {
            Ok(0) => return Err(LinkError::Closed),
            Ok(n) => at += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) if matches!(e.kind(), io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut) => return Err(LinkError::Timeout),
            Err(e) => return Err(LinkError::Io(e)),
        }
    }
    Ok(())
}

/// The control link. The only holder of the control socket.
pub struct Link {
    stream: TcpStream,
}

impl Link {
    /// Party 0: accept one connection on `port` (bound to `listen`, or all interfaces).
    pub fn listen(listen: Option<Ipv4Addr>, port: u16) -> io::Result<Link> {
        let listener = TcpListener::bind(SocketAddrV4::new(listen.unwrap_or(Ipv4Addr::UNSPECIFIED), port))?;
        let (stream, _) = listener.accept()?;
        Self::ready(stream)
    }

    /// Party 1: dial the other worker, retrying until it listens (or `within` has passed).
    pub fn dial(peer: Ipv4Addr, port: u16, within: Option<Duration>) -> io::Result<Link> {
        let started = Instant::now();
        loop {
            match TcpStream::connect(SocketAddrV4::new(peer, port)) {
                Ok(stream) => return Self::ready(stream),
                Err(e) => {
                    if within.is_some_and(|w| started.elapsed() >= w) {
                        return Err(e);
                    }
                    std::thread::sleep(Duration::from_millis(20));
                }
            }
        }
    }

    fn ready(stream: TcpStream) -> io::Result<Link> {
        stream.set_nodelay(true)?;
        Ok(Link { stream })
    }

    pub fn send(&mut self, frame: &PeerFrame) -> Result<(), LinkError> {
        self.stream.write_all(&frame.encode()).map_err(LinkError::Io)?;
        self.stream.flush().map_err(LinkError::Io)
    }

    /// The next frame; with `wait`, fails with [`LinkError::Timeout`] when the other worker
    /// sends nothing for that long.
    pub fn recv(&mut self, wait: Option<Duration>) -> Result<PeerFrame, LinkError> {
        self.stream.set_read_timeout(wait.filter(|w| !w.is_zero())).map_err(LinkError::Io)?;
        let result = PeerFrame::read_from(&mut self.stream);
        self.stream.set_read_timeout(None).map_err(LinkError::Io)?;
        result
    }

    /// Both workers present the session id and the frame-set version; both must match.
    pub fn hello(&mut self, session: &[u8; 32], wait: Option<Duration>) -> Result<(), String> {
        self.send(&PeerFrame::Hello { session: *session, version: LINK_VERSION }).map_err(|e| format!("control link: {e}"))?;
        match self.recv(wait) {
            Ok(PeerFrame::Hello { session: s, version }) if s == *session && version == LINK_VERSION => Ok(()),
            Ok(PeerFrame::Hello { version, .. }) if version != LINK_VERSION => Err(format!("control link version {version}, expected {LINK_VERSION}")),
            Ok(PeerFrame::Hello { .. }) => Err("control link: the other worker is in another session".into()),
            Ok(other) => Err(format!("control link: expected hello, got {}", other.name())),
            Err(e) => Err(format!("control link: {e}")),
        }
    }

    /// Operation 39: each party sends its bytes and receives the other's, of the same (agreed)
    /// size. Short payloads cross on the wire; long ones go one after the other (leader first),
    /// so that neither party can block writing while the other is not yet reading
    /// (dabit_generator.h `Challenge::transfer`).
    pub fn exchange(&mut self, leader: bool, mine: &[u8]) -> Result<Vec<u8>, String> {
        let take = |link: &mut Link| match link.recv(None) {
            Ok(PeerFrame::Exchange(peer)) if peer.len() == mine.len() => Ok(peer),
            Ok(PeerFrame::Exchange(_)) => Err("exchange size".to_string()),
            Ok(other) => Err(format!("control link: expected an exchange, got {}", other.name())),
            Err(e) => Err(format!("control link: {e}")),
        };
        let give = |link: &mut Link| link.send(&PeerFrame::Exchange(mine.to_vec())).map_err(|e| format!("control link: {e}"));
        if mine.len() <= 4096 || leader {
            give(self)?;
            take(self)
        } else {
            let peer = take(self)?;
            give(self)?;
            Ok(peer)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frames_round_trip() {
        let frames = vec![
            PeerFrame::Hello { session: [3; 32], version: LINK_VERSION },
            PeerFrame::Agreement([9; 32]),
            PeerFrame::Exchange(vec![1, 2, 3]),
            PeerFrame::ServerRecord(vec![23, 3, 3, 0, 1, 0]),
            PeerFrame::ServerRecord(vec![]),
            PeerFrame::ServerClosed,
        ];
        let bytes: Vec<u8> = frames.iter().flat_map(|f| f.encode()).collect();
        let mut r = &bytes[..];
        for f in &frames {
            assert_eq!(&PeerFrame::read_from(&mut r).unwrap(), f);
        }
        assert!(matches!(PeerFrame::read_from(&mut r), Err(LinkError::Closed)));
    }

    #[test]
    fn bounds_are_checked_before_allocation() {
        let mut big = vec![3u8];
        big.extend_from_slice(&((MAX_EXCHANGE + 1) as u32).to_be_bytes());
        assert!(matches!(PeerFrame::read_from(&mut &big[..]), Err(LinkError::Malformed("size"))));
        let mut empty_exchange = vec![3u8];
        empty_exchange.extend_from_slice(&0u32.to_be_bytes());
        assert!(matches!(PeerFrame::read_from(&mut &empty_exchange[..]), Err(LinkError::Malformed("size"))));
        let mut short_agreement = vec![2u8];
        short_agreement.extend_from_slice(&31u32.to_be_bytes());
        short_agreement.extend_from_slice(&[0; 31]);
        assert!(matches!(PeerFrame::read_from(&mut &short_agreement[..]), Err(LinkError::Malformed("size"))));
        let unknown = [9u8, 0, 0, 0, 0];
        assert!(matches!(PeerFrame::read_from(&mut &unknown[..]), Err(LinkError::Malformed("tag"))));
    }
}
