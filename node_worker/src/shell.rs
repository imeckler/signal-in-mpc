//! One worker operation: agreement, then the shell's own operations (the server socket, the
//! connection table, the exchange) or the legacy library (`tls_worker_v3.cpp` `dispatch`, the
//! shell's cases: 9, 10, 11, 17, 39, 90, 91; and the new 92), or a batch of engine
//! instructions (93, S9: interp.rs).
//!
//! Party 0 (the leader) owns the server socket; records it receives are forwarded to the other
//! party on the control link as public data. A connection the server or the proxy closed is
//! reported to both parties at the same operation (a poll's one-byte reply {0}), so neither
//! waits for the other.
use crate::agree;
use crate::connections::{Connections, Endpoint};
use crate::engines::{Engines, is_legacy};
use crate::interp::{self, Interp, Party};
use crate::link::{Link, MAX_EXCHANGE, MAX_RECORD, PeerFrame};
use crate::loader::{Kernels, Programs};
use crate::server::{RecordError, Server, ServerOp};
use std::time::Duration;

pub struct Shell<E: Engines> {
    pub leader: bool,
    /// The full session string (config.rs), part of every agreement.
    pub session: String,
    pub link: Link,
    pub engines: E,
    pub connections: Connections,
    pub peer_wait: Option<Duration>,
    /// The kernels a batch's `run` may name (the circuit manifest's; none without one).
    pub kernels: Kernels,
    /// The V3 field programs a batch's `program` may name ([`Shell::set_programs`]).
    pub programs: Programs,
    /// The batch interpreter's state (interp.rs), carried across batches.
    pub interp: Interp,
}

fn need(ok: bool, what: &str) -> Result<(), String> {
    if ok { Ok(()) } else { Err(what.to_string()) }
}

/// A record forwarded by the leader: within bounds, and exactly one record.
fn check_record(r: &[u8]) -> Result<(), String> {
    need(r.len() >= 5 && r.len() <= MAX_RECORD, "record bound")?;
    need(u16::from_be_bytes([r[3], r[4]]) as usize + 5 == r.len(), "record framing")
}

impl<E: Engines> Shell<E> {
    pub fn new(leader: bool, session: String, link: Link, engines: E, peer_wait: Option<Duration>) -> Self {
        Shell {
            leader,
            session,
            link,
            engines,
            connections: Connections::default(),
            peer_wait,
            kernels: Kernels::default(),
            programs: Programs::default(),
            interp: Interp::default(),
        }
    }

    /// The loaded V3 field programs, at session start: the interpreter's context starts with
    /// their signatures (Lean `Ctx.progs`, `Env.progs`; decision D14).
    pub fn set_programs(&mut self, programs: Programs) {
        self.interp.ctx.progs = programs.sigs();
        self.programs = programs;
    }

    /// One agreed operation (never 8, which is local: see [`Shell::abort`]).
    pub fn call(&mut self, code: u8, sequence: u64, payload: &[u8]) -> Result<Vec<u8>, String> {
        if code == interp::BATCH {
            return self.batch(sequence, payload);
        }
        agree::agree(&mut self.link, &self.session, code, sequence, payload, self.peer_wait)?;
        if ServerOp::is_server_op(code) {
            let op = ServerOp::parse(code, payload)?;
            return self.server(op);
        }
        if code == 39 {
            // Each party sends its private bytes and receives the other's (values safe to
            // reveal, such as parity shares of a consistency check).
            need(!payload.is_empty() && payload.len() <= MAX_EXCHANGE, "exchange")?;
            return self.link.exchange(self.leader, payload);
        }
        if is_legacy(code) {
            return self.engines.legacy(code, sequence, payload);
        }
        Err("unsupported operation".into())
    }

    /// Operation 93: one batch of engine instructions (interp.rs; Engine.lean design note).
    /// Decode and payload check, agreement on the skeleton, `check` over the whole batch, then
    /// the instructions in order; the reply is the encoded reply items.
    fn batch(&mut self, sequence: u64, payload: &[u8]) -> Result<Vec<u8>, String> {
        let me = if self.leader { Party::A } else { Party::B };
        // Lean `usableBatch`, then `agreedBytes`: an unusable batch is still agreed (as
        // `UNUSABLE`), so that the other party stops at the agreement instead of inside an
        // engine call (Lean `unusable_rejected_by_both`).
        let prepared = interp::usable_batch(me, payload);
        let agreed = interp::agreed_bytes(&prepared);
        let agreement = agree::agree_bytes(&mut self.link, &self.session, interp::BATCH, sequence, &agreed, self.peer_wait);
        let batch = prepared?;
        agreement?;
        let kernels = &self.kernels;
        let steps = self.interp.admit(&|name| kernels.sig(name), &batch)?;
        let (leader, link) = (self.leader, &mut self.link);
        let replies =
            self.interp.execute(&mut self.engines, kernels, &self.programs, me, &batch, &steps, &mut |mine| link.exchange(leader, mine))?;
        Ok(interp::encode_replies(&replies))
    }

    /// Operation 8 and every failure: drop the engines' private state and close every socket.
    pub fn abort(&mut self) {
        self.engines.abort();
        self.connections.drop_all();
    }

    fn server(&mut self, op: ServerOp) -> Result<Vec<u8>, String> {
        match op {
            ServerOp::Connect { host, port, proxy } => {
                need(!self.connections.connected(), "connect")?;
                self.connections.note_route(proxy.is_some())?;
                let endpoint = if self.leader {
                    Endpoint::Leader(match &proxy {
                        Some(via) => Server::connect_proxied(via, &host, port)?,
                        None => Server::connect_direct(&host, port)?,
                    })
                } else {
                    Endpoint::Follower
                };
                *self.connections.active() = Some(endpoint);
                Ok(vec![])
            }
            ServerOp::Send(bytes) => {
                need(self.connections.connected(), "send")?;
                if let Some(Endpoint::Leader(server)) = self.connections.active() {
                    // A write to a connection the server or the proxy has closed is dropped:
                    // the next poll reports the closure to both parties.
                    let _ = server.send(&bytes);
                }
                Ok(vec![])
            }
            ServerOp::Receive => {
                need(self.connections.connected(), "receive")?;
                if let Some(Endpoint::Leader(server)) = self.connections.active() {
                    match server.record() {
                        Ok(record) => {
                            self.link.send(&PeerFrame::ServerRecord(record.clone())).map_err(|e| format!("control link: {e}"))?;
                            Ok(record)
                        }
                        Err(e) => {
                            // The other party is told before this fails, so both stop here.
                            let _ = self.link.send(&PeerFrame::ServerClosed);
                            Err(if e == RecordError::Bound { "record bound" } else { "server closed" }.into())
                        }
                    }
                } else {
                    match self.link.recv(None).map_err(|e| format!("control link: {e}"))? {
                        PeerFrame::ServerClosed => Err("server closed (reported by the leader)".into()),
                        PeerFrame::ServerRecord(record) => check_record(&record).map(|_| record),
                        other => Err(format!("control link: expected a record, got {}", other.name())),
                    }
                }
            }
            ServerOp::Poll => {
                need(self.connections.connected(), "poll")?;
                if let Some(Endpoint::Leader(server)) = self.connections.active() {
                    let mut record = Vec::new();
                    let lost = server.readable() && match server.record() {
                        Ok(r) => {
                            record = r;
                            false
                        }
                        Err(_) => true,
                    };
                    if lost {
                        // Not the worker's failure: both parties get {0} (no record is that
                        // short), the connection is gone (91 replaces it), the rest carries on.
                        let _ = self.link.send(&PeerFrame::ServerClosed);
                        *self.connections.active() = None;
                        return Ok(vec![0]);
                    }
                    self.link.send(&PeerFrame::ServerRecord(record.clone())).map_err(|e| format!("control link: {e}"))?;
                    Ok(record)
                } else {
                    match self.link.recv(None).map_err(|e| format!("control link: {e}"))? {
                        PeerFrame::ServerClosed => {
                            *self.connections.active() = None;
                            Ok(vec![0])
                        }
                        PeerFrame::ServerRecord(record) => {
                            if !record.is_empty() {
                                check_record(&record)?;
                            }
                            Ok(record)
                        }
                        other => Err(format!("control link: expected a record, got {}", other.name())),
                    }
                }
            }
            ServerOp::Select(to) => {
                self.connections.check_select(to)?;
                self.engines.select(to)?;
                self.connections.select(to);
                Ok(vec![])
            }
            ServerOp::Reset { legacy } => {
                // Only a connection reported closed is replaced; with the legacy TLS state
                // (`legacy`) the engines check that its TLS session had been retired. Without it
                // (J22: the scripts own the TLS state) only the socket goes; the legacy library's
                // connection is untouched (still fresh).
                need(!self.connections.connected(), "reset connection")?;
                if legacy {
                    self.engines.reset()?;
                }
                Ok(vec![])
            }
            ServerOp::Close => {
                need(self.connections.connected(), "close connection")?;
                *self.connections.active() = None;
                Ok(vec![])
            }
        }
    }
}
