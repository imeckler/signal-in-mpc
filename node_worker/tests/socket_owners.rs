//! Lint (REORGANIZATION_PLAN.md 5.6): only `link.rs` holds the control socket and only
//! `server.rs` holds server sockets. No other source file of the worker may name a socket type
//! or a socket call; foreign functions are declared only in `engines.rs` (whose ABI has no
//! function that takes bytes to send), and raw descriptors are touched only in `pipe.rs`.
use std::path::Path;

const SOCKET_WORDS: &[&str] = &[
    // (Address types such as Ipv4Addr are not sockets and may appear anywhere.)
    "TcpStream", "TcpListener", "UdpSocket", "UnixStream", "UnixListener", "UnixDatagram", "ToSocketAddrs", "socket2", "mio::",
    "libc::socket", "libc::connect", "libc::bind", "libc::listen", "libc::accept", "libc::send", "libc::recv",
];

/// The source without comments (line comments; the sources use no block comments).
fn code(text: &str) -> String {
    text.lines().map(|l| l.split("//").next().unwrap_or("")).collect::<Vec<_>>().join("\n")
}

fn sources(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            sources(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

#[test]
fn only_link_and_server_own_sockets() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    sources(&src, &mut files);
    assert!(files.len() >= 12, "expected the worker's modules under src/");
    let mut found = Vec::new();
    for file in &files {
        let name = file.strip_prefix(&src).unwrap().to_string_lossy().to_string();
        let text = code(&std::fs::read_to_string(file).unwrap());
        if name != "link.rs" && name != "server.rs" {
            for w in SOCKET_WORDS {
                if text.contains(w) {
                    found.push(format!("{name}: {w}"));
                }
            }
        }
        if name != "engines.rs" && text.contains("extern \"C\"") {
            found.push(format!("{name}: foreign function declarations"));
        }
        if name != "pipe.rs" && (text.contains("libc::") || text.contains("from_raw_fd")) {
            found.push(format!("{name}: raw descriptor calls"));
        }
    }
    assert!(found.is_empty(), "socket use outside link.rs / server.rs: {found:?}");
}

#[test]
fn the_engine_abi_has_no_send() {
    let header = Path::new(env!("CARGO_MANIFEST_DIR")).join("../handshake_backend/EmpHybridWork/engine_abi.h");
    let text = std::fs::read_to_string(header).unwrap();
    for line in text.lines().filter(|l| l.trim_start().starts_with("int ea_") || l.trim_start().starts_with("void ea_")) {
        let name = line.split('(').next().unwrap();
        assert!(!name.contains("send") && !name.contains("write") && !name.contains("transfer"), "{line}");
    }
}
