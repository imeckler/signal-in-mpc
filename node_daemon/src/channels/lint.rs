//! The daemon's I/O stays in `channels`: a test that fails when any daemon source outside
//! `src/channels/` names an I/O primitive (sockets, files, processes, environment, standard
//! streams, the clock, randomness, signals). Comments are ignored.
//!
//! Exempt: `bin/notify-app.rs`, the application stand-in (the application's side, not a node's).

use std::fs;
use std::path::{Path, PathBuf};

/// Names that only `channels` may use.
const FORBIDDEN: &[&str] = &[
    "std::net", "tokio::net", "TcpStream", "TcpListener", "UdpSocket", "ToSocketAddrs",
    "std::fs", "File::", "OpenOptions", "read_dir", "remove_file", "create_dir",
    "std::process", "Command::", "Stdio", "std::env", "std::os",
    "std::io", "println!", "eprintln!", "print!", "eprint!", "dbg!",
    "SystemTime", "UNIX_EPOCH", "Instant", "thread::sleep",
    "rand::", "getrandom", "/dev/",
    "libc::",
    // A grouped import (`use std::{fs, …}`) would hide the names above.
    "std::{", "extern crate",
];

const EXEMPT: &[&str] = &["bin/notify-app.rs"];

fn sources(directory: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).unwrap().flatten() {
        let path = entry.path();
        if path.is_dir() {
            sources(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

/// The forbidden names on each line of `text` (outside `//` comments), as (line number, name).
fn violations(text: &str) -> Vec<(usize, &'static str)> {
    let mut found = Vec::new();
    for (number, line) in text.lines().enumerate() {
        let code = line.split("//").next().unwrap_or("");
        for name in FORBIDDEN {
            if code.contains(name) {
                found.push((number + 1, *name));
            }
        }
    }
    found
}

#[test]
fn io_only_in_channels() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    sources(&root, &mut files);
    let mut checked = Vec::new();
    let mut problems = Vec::new();
    for file in files {
        let relative = file.strip_prefix(&root).unwrap().to_string_lossy().replace('\\', "/");
        if relative.starts_with("channels/") || EXEMPT.contains(&relative.as_str()) {
            continue;
        }
        for (line, name) in violations(&fs::read_to_string(&file).unwrap()) {
            problems.push(format!("src/{relative}:{line}: `{name}` (I/O belongs in src/channels/)"));
        }
        checked.push(relative);
    }
    // The scan is not vacuous: the daemon's other sources are all in it.
    for expected in ["lib.rs", "config.rs", "request.rs", "scheduler.rs", "bin/node-daemon.rs"] {
        assert!(checked.iter().any(|f| f == expected), "{expected} was not scanned");
    }
    assert!(problems.is_empty(), "I/O outside channels:\n{}", problems.join("\n"));
}

#[test]
fn the_lint_sees_what_it_should() {
    assert_eq!(violations("use std::fs;\nlet t = Instant::now(); // std::net in a comment"), vec![(1, "std::fs"), (2, "Instant")]);
    assert_eq!(violations("use std::{fs, io};"), vec![(1, "std::{")]);
    assert_eq!(violations("eprintln!(\"x\");"), vec![(1, "println!"), (1, "eprintln!")]);
    assert!(violations("let d = Duration::from_secs(1); // Command::new").is_empty());
}
