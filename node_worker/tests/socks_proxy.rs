//! The leader's proxied connection against local_signal_server/scripts/socks5_test_proxy.py
//! (the harness's stand-in for Tor): username/password, hostname address type, one record each
//! way through it, and the proxy's refusal of an unmapped name. Everything on 127.0.0.1.
use node_worker::server::{MAX_BODY, Server};
use node_worker::socks::Proxy;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpListener;
use std::path::Path;
use std::process::{Child, Command, Stdio};

struct Running(Child);
impl Drop for Running {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

fn start_proxy(target_port: u16, log: &Path) -> (Running, u16) {
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("../local_signal_server/scripts/socks5_test_proxy.py");
    for _ in 0..5 {
        let port = free_port();
        let mut child = Command::new("python3")
            .arg(&script)
            .arg(port.to_string())
            .arg(log)
            .arg(format!("chat.example:443=127.0.0.1:{target_port}"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("python3");
        let mut line = String::new();
        BufReader::new(child.stdout.as_mut().unwrap()).read_line(&mut line).unwrap();
        if line.trim() == format!("listening {port}") {
            return (Running(child), port);
        }
        let _ = child.kill();
        let _ = child.wait();
    }
    panic!("the test proxy did not start");
}

#[test]
fn proxied_connection_through_the_test_proxy() {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("node-worker-socks-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let log = dir.join("proxy.jsonl");
    // The "server": echoes one TLS record back.
    let target = TcpListener::bind("127.0.0.1:0").unwrap();
    let target_port = target.local_addr().unwrap().port();
    let echo = std::thread::spawn(move || {
        let (mut s, _) = target.accept().unwrap();
        let mut head = [0u8; 5];
        s.read_exact(&mut head).unwrap();
        let mut body = vec![0u8; u16::from_be_bytes([head[3], head[4]]) as usize];
        s.read_exact(&mut body).unwrap();
        s.write_all(&head).unwrap();
        s.write_all(&body).unwrap();
    });
    let (_proxy, proxy_port) = start_proxy(target_port, &log);
    let via = Proxy { host: b"127.0.0.1".to_vec(), port: proxy_port, user: b"circuit-7".to_vec(), pass: b"secret-7".to_vec() };
    let mut server = Server::connect_proxied(&via, b"chat.example", 443).expect("proxied connect");
    let record = [&[23u8, 3, 3, 0, 4][..], b"ping"].concat();
    server.send(&record).unwrap();
    assert_eq!(server.record().unwrap(), record);
    echo.join().unwrap();
    // An unmapped name is refused by the proxy, and reported as such.
    let refused = Server::connect_proxied(&via, b"elsewhere.example", 443).err().unwrap();
    assert_eq!(refused, "proxy could not reach the server (SOCKS reply 2)");
    // A non-numeric proxy address is refused before any connection.
    let named = Proxy { host: b"localhost".to_vec(), ..via.clone() };
    assert_eq!(Server::connect_proxied(&named, b"chat.example", 443).err().unwrap(), "proxy address (numeric only)");
    drop(server);
    let text = std::fs::read_to_string(&log).unwrap();
    assert!(text.contains("\"event\": \"open\""), "{text}");
    assert!(text.contains("\"username\": \"circuit-7\"") && text.contains("\"password\": \"secret-7\""), "{text}");
    assert!(text.contains("\"atyp\": 3") && text.contains("\"host\": \"chat.example\""), "{text}");
    assert!(text.contains("not a mapped hostname"), "{text}");
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(MAX_BODY, 16640);
}
