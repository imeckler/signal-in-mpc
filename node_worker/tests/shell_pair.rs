//! Two shells (leader and follower) over a real control link on 127.0.0.1, with stand-in
//! engines and a stand-in TLS server: agreement, connect, send, poll, receive, the exchange,
//! a closed connection reported to both, reset, select, close, and a request disagreement.
use node_worker::engines::{Counters, Engines};
use node_worker::link::Link;
use node_worker::shell::Shell;
use std::io::{Read, Write};
use std::net::{Ipv4Addr, TcpListener};
use std::sync::mpsc;
use std::time::Duration;

#[derive(Default)]
struct Fake {
    legacy: Vec<u8>,
    selected: Vec<u8>,
    resets: usize,
    aborts: usize,
}
impl Engines for Fake {
    fn counters(&mut self) -> Counters {
        Counters::default()
    }
    fn legacy(&mut self, code: u8, _: u64, payload: &[u8]) -> Result<Vec<u8>, String> {
        self.legacy.push(code);
        Ok(payload.iter().rev().copied().collect())
    }
    fn select(&mut self, index: u8) -> Result<(), String> {
        self.selected.push(index);
        Ok(())
    }
    fn reset(&mut self) -> Result<(), String> {
        self.resets += 1;
        Ok(())
    }
    fn abort(&mut self) {
        self.aborts += 1;
    }
    fn profile_report(&mut self, _: &str) {}
}

fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

fn pair() -> (Shell<Fake>, Shell<Fake>) {
    let port = free_port();
    let wait = Some(Duration::from_secs(20));
    let leader = std::thread::spawn(move || Link::listen(Some(Ipv4Addr::LOCALHOST), port).unwrap());
    let mut b = Link::dial(Ipv4Addr::LOCALHOST, port, wait).unwrap();
    let mut a = leader.join().unwrap();
    let t = std::thread::spawn(move || {
        a.hello(&[5; 32], wait).unwrap();
        a
    });
    b.hello(&[5; 32], wait).unwrap();
    let a = t.join().unwrap();
    (Shell::new(true, "s".into(), a, Fake::default(), wait), Shell::new(false, "s".into(), b, Fake::default(), wait))
}

/// Runs the same request on both shells at once; returns (leader's result, follower's).
fn both(a: Shell<Fake>, b: Shell<Fake>, code: u8, seq: u64, pa: Vec<u8>, pb: Vec<u8>) -> (Shell<Fake>, Shell<Fake>, Result<Vec<u8>, String>, Result<Vec<u8>, String>) {
    let (tx, rx) = mpsc::channel();
    let t = std::thread::spawn(move || {
        let mut a = a;
        let r = a.call(code, seq, &pa);
        tx.send(()).unwrap();
        (a, r)
    });
    let mut b = b;
    let rb = b.call(code, seq, &pb);
    rx.recv_timeout(Duration::from_secs(30)).expect("leader finished");
    let (a, ra) = t.join().unwrap();
    (a, b, ra, rb)
}

fn connect_request(port: u16) -> Vec<u8> {
    [&[0u8, 9][..], b"127.0.0.1", &port.to_be_bytes()].concat()
}

#[test]
fn leader_and_follower() {
    let (a, b) = pair();
    let server = TcpListener::bind("127.0.0.1:0").unwrap();
    let server_port = server.local_addr().unwrap().port();
    let record = [&[23u8, 3, 3, 0, 3][..], b"abc"].concat();
    let r2 = record.clone();
    let srv = std::thread::spawn(move || {
        let (mut s, _) = server.accept().unwrap();
        let mut got = vec![0u8; 8];
        s.read_exact(&mut got).unwrap();
        assert_eq!(got, r2);
        s.write_all(&r2).unwrap();
        s.write_all(&r2).unwrap();
        std::thread::sleep(Duration::from_millis(300));
        // then the server closes
    });
    let mut seq = 0;
    let mut step = |a, b, code, pa: Vec<u8>, pb: Vec<u8>| {
        let out = both(a, b, code, seq, pa, pb);
        seq += 1;
        out
    };
    // Connect (the follower opens nothing), send, then a legacy operation.
    let (a, b, ra, rb) = step(a, b, 9, connect_request(server_port), connect_request(server_port));
    assert_eq!((ra.unwrap(), rb.unwrap()), (vec![], vec![]));
    let (a, b, ra, rb) = step(a, b, 10, record.clone(), record.clone());
    assert!(ra.is_ok() && rb.is_ok());
    let (a, b, ra, rb) = step(a, b, 12, vec![1, 2, 3], vec![1, 2, 3]);
    assert_eq!((ra.unwrap(), rb.unwrap()), (vec![3, 2, 1], vec![3, 2, 1]));
    // Receive: the leader reads, the follower gets the same record on the link.
    let (a, b, ra, rb) = step(a, b, 11, vec![], vec![]);
    assert_eq!((ra.unwrap(), rb.unwrap()), (record.clone(), record.clone()));
    // Poll until the second record, then until the closure: both see the same.
    let (mut a, mut b) = (a, b);
    let mut seen = Vec::new();
    for _ in 0..200 {
        let (na, nb, ra, rb) = step(a, b, 17, vec![], vec![]);
        let (ra, rb) = (ra.unwrap(), rb.unwrap());
        assert_eq!(ra, rb);
        a = na;
        b = nb;
        if !ra.is_empty() {
            seen.push(ra.clone());
        }
        if ra == vec![0] {
            break;
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    srv.join().unwrap();
    assert_eq!(seen, vec![record.clone(), vec![0]]);
    assert!(!a.connections.connected() && !b.connections.connected());
    // The exchange: each gets the other's bytes (private bytes, only the size agreed).
    let (a, b, ra, rb) = step(a, b, 39, vec![1; 5000], vec![2; 5000]);
    assert_eq!((ra.unwrap(), rb.unwrap()), (vec![2; 5000], vec![1; 5000]));
    let (a, b, ra, rb) = step(a, b, 39, vec![7], vec![8]);
    assert_eq!((ra.unwrap(), rb.unwrap()), (vec![8], vec![7]));
    // Reset the closed connection, select a new one, the retired operation is refused.
    let (a, b, ra, rb) = step(a, b, 91, vec![], vec![]);
    assert!(ra.is_ok() && rb.is_ok());
    let (a, b, ra, rb) = step(a, b, 90, vec![1], vec![1]);
    assert!(ra.is_ok() && rb.is_ok());
    assert_eq!((a.engines.resets, b.engines.selected.clone()), (1, vec![1]));
    let (a, b, ra, rb) = step(a, b, 90, vec![3], vec![3]);
    assert_eq!((ra.unwrap_err(), rb.unwrap_err()), ("connection index".to_string(), "connection index".to_string()));
    let (a, b, ra, rb) = step(a, b, 21, vec![0; 16], vec![0; 16]);
    assert_eq!(ra.unwrap_err(), "unsupported operation");
    assert!(rb.is_err());
    // Different public requests: both refuse.
    let (_a, _b, ra, rb) = step(a, b, 12, vec![1], vec![2]);
    assert_eq!((ra.unwrap_err(), rb.unwrap_err()), ("request disagreement".to_string(), "request disagreement".to_string()));
}

#[test]
fn close_and_private_prefix() {
    let (a, b) = pair();
    let server = TcpListener::bind("127.0.0.1:0").unwrap();
    let port = server.local_addr().unwrap().port();
    let (a, b, ra, rb) = both(a, b, 9, 0, connect_request(port), connect_request(port));
    assert!(ra.is_ok() && rb.is_ok());
    let (mut s, _) = server.accept().unwrap();
    // 92: both close; the server sees the end of the stream.
    let (a, b, ra, rb) = both(a, b, 92, 1, vec![], vec![]);
    assert!(ra.is_ok() && rb.is_ok());
    let mut buf = [0u8; 1];
    assert_eq!(s.read(&mut buf).unwrap(), 0);
    assert!(!a.connections.connected() && !b.connections.connected());
    // 36: the private part differs between the parties, the public contact id does not.
    let pa = [vec![9u8; 16], vec![1u8; 32]].concat();
    let pb = [vec![9u8; 16], vec![2u8; 32]].concat();
    let (a, b, ra, rb) = both(a, b, 36, 2, pa, pb);
    assert!(ra.is_ok() && rb.is_ok());
    assert_eq!((a.engines.legacy.clone(), b.engines.legacy.clone()), (vec![36], vec![36]));
    // A different public id is a disagreement.
    let (_, _, ra, rb) = both(a, b, 36, 3, [vec![1u8; 16], vec![0; 32]].concat(), [vec![2u8; 16], vec![0; 32]].concat());
    assert!(ra.is_err() && rb.is_err());
}
