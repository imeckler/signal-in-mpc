//! Everything that enters or leaves a node daemon, and nothing else.
//!
//! This directory is the only place in the daemon that touches a socket, a file, a process, the
//! clock, the random generator, a signal or a standard stream (`lint.rs` checks it). A reviewer
//! who wants to know what a daemon can send, write, start or read reads these files:
//!
//! | file | channel | what crosses it |
//! |---|---|---|
//! | `application.rs` | the application's listener (`listen`) | `AppRequest` in, `AppReply` out; optional bearer token |
//! | `peer.rs` | the other daemon (`peer_listen` in, `peer` out) | `PeerMessage` both ways, sealed (HMAC, nonce, clock, replay cache); `PeerReply` sealed |
//! | `controller.rs` | the controller processes it starts | arguments and environment (`SessionEnv`, `Launch`) out; `ControllerLine` in; `ps` and `kill` of their process trees |
//! | `disk.rs` | the state directory and the configuration files | work, journal, events, logs, serve directory; config, network config, keys (read at start) |
//! | `host.rs` | this machine | clock (`unix_now`, `Moment`, `sleep`), randomness (`random_bytes`), stop signals, the log on standard error, the start line on standard output, the arguments, exit |
//!
//! Below, the line protocol both listeners speak: one JSON object per line, one request and one
//! reply per connection.

pub mod application;
pub mod controller;
pub mod disk;
pub mod host;
pub mod peer;

#[cfg(test)]
mod lint;

use crate::MAX_LINE;
use serde_json::{Value, json};
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream, ToSocketAddrs};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

pub fn read_line(stream: &mut impl Read) -> Result<Value, String> {
    let mut line = String::new();
    BufReader::new(stream.take(MAX_LINE)).read_line(&mut line).map_err(|e| format!("read: {e}"))?;
    if !line.ends_with('\n') {
        return Err("incomplete line".into());
    }
    serde_json::from_str(&line).map_err(|e| format!("not JSON: {e}"))
}

pub fn write_line(stream: &mut impl Write, value: &Value) -> Result<(), String> {
    let mut text = value.to_string();
    text.push('\n');
    stream.write_all(text.as_bytes()).and_then(|_| stream.flush()).map_err(|e| format!("write: {e}"))
}

/// One request to a daemon (the other daemon's `peer_listen`, or either listener for the
/// application stand-in). `timeout` bounds connecting and the wait for the reply.
pub fn call(address: &str, request: &Value, timeout: Duration) -> Result<Value, String> {
    let target = address.to_socket_addrs().map_err(|e| format!("{address}: {e}"))?.next().ok_or(format!("{address}: no address"))?;
    let mut stream = TcpStream::connect_timeout(&target, timeout.min(Duration::from_secs(5))).map_err(|e| format!("{address}: {e}"))?;
    stream.set_read_timeout(Some(timeout)).map_err(|e| e.to_string())?;
    stream.set_write_timeout(Some(timeout)).map_err(|e| e.to_string())?;
    write_line(&mut stream, request)?;
    read_line(&mut stream)
}

/// A bound listener of the line protocol.
pub struct Listener(TcpListener);

impl Listener {
    pub fn bind(address: &str) -> Result<Listener, String> {
        TcpListener::bind(address).map(Listener).map_err(|e| format!("{address}: {e}"))
    }

    /// The address it is bound to (with the port the system chose for port 0).
    pub fn address(&self) -> String {
        self.0.local_addr().map(|a| a.to_string()).unwrap_or_default()
    }

    /// Answer every connection on its own thread: one line in (read within 30 s), `handle`'s
    /// value out. A line that cannot be read is answered `{"ok":false,"error":…}`.
    fn serve(self, handle: Arc<dyn Fn(Value) -> Value + Send + Sync>) {
        thread::spawn(move || {
            for stream in self.0.incoming().flatten() {
                let handle = handle.clone();
                thread::spawn(move || {
                    let mut stream = stream;
                    let _ = stream.set_read_timeout(Some(Duration::from_secs(30)));
                    let reply = match read_line(&mut stream) {
                        Ok(message) => handle(message),
                        Err(why) => json!({"ok": false, "error": why}),
                    };
                    let _ = write_line(&mut stream, &reply);
                });
            }
        });
    }
}
