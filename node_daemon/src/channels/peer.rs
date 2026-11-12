//! The link between the two daemons: the line protocol on a listener of its own (`peer_listen`),
//! each message carrying the sender's party, a fresh nonce, the sender's clock and an HMAC-SHA256
//! under a key the two nodes share (`peer_key_file`). Only public values cross it: request
//! digests, session names, ports.
//!
//! A request: {"op": "peer-…", …, "from", "nonce", "at", "mac"}. The receiver accepts it once:
//! the MAC, the sender being the other party (a message reflected back to its sender is refused),
//! the clock within PEER_SKEW_SECS, and a nonce not seen before (`ReplayCache`).
//! A reply: {…, "from", "reply_to" (the request's nonce), "at", "mac"}, checked by the caller
//! against the request it sent, so a reply cannot be forged, replayed, or taken from another call.

use super::host::{log, random_bytes, unix_now};
use super::{Listener, call};
use crate::hmac;
use serde_json::{Value, json};
use std::sync::Arc;
use std::time::Duration;

pub const PEER_SKEW_SECS: u64 = 60;
/// Nonces remembered at most (one per peer request within two minutes; the leader sends a few a second).
pub const REPLAY_CAPACITY: usize = 1 << 16;

/// Everything one daemon can ask the other. Party 0 leads; README "Between the two daemons".
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PeerMessage {
    /// "Are you there?" (tests and diagnostics).
    Ping,
    /// "Do you hold this request too?" Yes only for a request the receiver verified itself.
    Agree { job: String },
    /// Run this request: with a port, in a one-request session of that name; without, hand it to
    /// the long-lived send session of that name.
    Start { job: String, session: String, port: Option<u16> },
    /// (Re)start the receive session.
    Receive { session: String, port: u16 },
    /// (Re)start the long-lived send session.
    Serve { session: String, port: u16 },
    /// "My send session of this name ended": end yours.
    Ended { session: String },
    /// Party 0 gave this notify up: report it failed too.
    Finish { job: String },
}

fn field(message: &Value, name: &str) -> Option<String> {
    message.get(name).and_then(Value::as_str).map(str::to_string)
}

fn port(message: &Value) -> Option<Option<u16>> {
    match message.get("port") {
        None => Some(None),
        Some(value) => value.as_u64().and_then(|p| u16::try_from(p).ok()).map(Some),
    }
}

impl PeerMessage {
    /// The message on the wire (before sealing).
    pub fn encode(&self) -> Value {
        match self {
            PeerMessage::Ping => json!({"op": "peer-ping"}),
            PeerMessage::Agree { job } => json!({"op": "peer-agree", "job": job}),
            PeerMessage::Start { job, session, port: None } => json!({"op": "peer-start", "job": job, "session": session}),
            PeerMessage::Start { job, session, port: Some(port) } => json!({"op": "peer-start", "job": job, "session": session, "port": port}),
            PeerMessage::Receive { session, port } => json!({"op": "peer-receive", "session": session, "port": port}),
            PeerMessage::Serve { session, port } => json!({"op": "peer-serve", "session": session, "port": port}),
            PeerMessage::Ended { session } => json!({"op": "peer-ended", "session": session}),
            PeerMessage::Finish { job } => json!({"op": "peer-finish", "job": job}),
        }
    }

    /// An opened request of the other daemon (the sealing fields are ignored here).
    pub fn decode(message: &Value) -> Result<PeerMessage, String> {
        let op = message.get("op").and_then(Value::as_str).unwrap_or("");
        let session_and_port = || -> Option<(String, u16)> { Some((field(message, "session")?, port(message)??)) };
        match op {
            "peer-ping" => Ok(PeerMessage::Ping),
            "peer-agree" => Ok(PeerMessage::Agree { job: field(message, "job").ok_or("peer-agree: job")? }),
            "peer-start" => {
                let job = field(message, "job").ok_or("peer-start: job")?;
                let session = field(message, "session").ok_or("peer-start: session")?;
                let port = port(message).ok_or("peer-start: port")?;
                Ok(PeerMessage::Start { job, session, port })
            }
            "peer-receive" => session_and_port().map(|(session, port)| PeerMessage::Receive { session, port }).ok_or("peer-receive: session and port".into()),
            "peer-serve" => session_and_port().map(|(session, port)| PeerMessage::Serve { session, port }).ok_or("peer-serve: session and port".into()),
            "peer-ended" => Ok(PeerMessage::Ended { session: field(message, "session").ok_or("peer-ended: session")? }),
            "peer-finish" => Ok(PeerMessage::Finish { job: field(message, "job").ok_or("peer-finish: job")? }),
            _ => Err("unknown peer message".into()),
        }
    }
}

/// The answer to a `PeerMessage`: `{"ok"[, "busy": true][, "error"]}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PeerReply {
    pub ok: bool,
    /// The refusal is only because the receiver is running something else (try again later).
    pub busy: bool,
    pub error: Option<String>,
}

impl PeerReply {
    pub fn yes() -> PeerReply {
        PeerReply { ok: true, busy: false, error: None }
    }

    pub fn no() -> PeerReply {
        PeerReply { ok: false, busy: false, error: None }
    }

    pub fn refused(why: impl Into<String>) -> PeerReply {
        PeerReply { ok: false, busy: false, error: Some(why.into()) }
    }

    pub fn busy(why: Option<&str>) -> PeerReply {
        PeerReply { ok: false, busy: true, error: why.map(str::to_string) }
    }

    pub fn encode(&self) -> Value {
        let mut reply = json!({"ok": self.ok});
        if self.busy {
            reply["busy"] = json!(true);
        }
        if let Some(error) = &self.error {
            reply["error"] = json!(error);
        }
        reply
    }

    pub fn decode(reply: &Value) -> PeerReply {
        PeerReply { ok: reply["ok"] == json!(true), busy: reply["busy"] == json!(true), error: field(reply, "error") }
    }
}

// ---- Sealing and opening.

fn mac_of(key: &[u8], body: &Value) -> String {
    hex::encode(hmac(key, body.to_string().as_bytes()))
}

fn sealed(key: &[u8], mut message: Value, now: u64) -> Value {
    message["at"] = json!(now);
    let mac = mac_of(key, &message);
    message["mac"] = json!(mac);
    message
}

/// The MAC and the clock of a sealed message; returns the body without `mac`.
fn verified(key: &[u8], message: &Value, now: u64) -> Result<Value, String> {
    let mut body = message.clone();
    let given = body.as_object_mut().and_then(|o| o.remove("mac")).and_then(|m| m.as_str().map(str::to_string)).ok_or("peer message without mac")?;
    let expected = mac_of(key, &body);
    let same = given.len() == expected.len() && given.bytes().zip(expected.bytes()).fold(0u8, |acc, (a, b)| acc | (a ^ b)) == 0;
    if !same {
        return Err("peer message not authenticated".into());
    }
    let at = body.get("at").and_then(Value::as_u64).ok_or("peer message without time")?;
    if at > now + PEER_SKEW_SECS || at + PEER_SKEW_SECS < now {
        return Err("peer message is stale".into());
    }
    Ok(body)
}

fn from_other(body: &Value, me: u8) -> Result<(), String> {
    match body.get("from").and_then(Value::as_u64) {
        Some(from) if from <= 1 && from != me as u64 => Ok(()),
        Some(_) => Err("peer message from this node itself".into()),
        None => Err("peer message without sender".into()),
    }
}

/// A request to the other daemon, from party `from`, with a fresh nonce.
pub fn seal_request(key: &[u8], from: u8, mut message: Value) -> Result<Value, String> {
    message["from"] = json!(from);
    message["nonce"] = json!(hex::encode(random_bytes(16)?));
    Ok(sealed(key, message, unix_now()))
}

/// The reply to `request` (already opened), from party `from`.
pub fn seal_reply(key: &[u8], from: u8, request: &Value, mut reply: Value) -> Value {
    if !reply.is_object() {
        reply = json!({"ok": false, "error": "invalid reply"});
    }
    reply["from"] = json!(from);
    reply["reply_to"] = request.get("nonce").cloned().unwrap_or(Value::Null);
    sealed(key, reply, unix_now())
}

/// The nonces of the requests accepted within the freshness window.
#[derive(Default)]
pub struct ReplayCache {
    /// nonce -> the time after which its request would be stale anyway.
    seen: std::sync::Mutex<std::collections::HashMap<String, u64>>,
}

impl ReplayCache {
    fn admit(&self, nonce: &str, at: u64, now: u64) -> Result<(), String> {
        let mut seen = self.seen.lock().unwrap_or_else(|p| p.into_inner());
        seen.retain(|_, until| *until >= now);
        if seen.contains_key(nonce) {
            return Err("peer message replayed".into());
        }
        if seen.len() >= REPLAY_CAPACITY {
            return Err("too many peer messages".into());
        }
        seen.insert(nonce.to_string(), at + PEER_SKEW_SECS);
        Ok(())
    }
}

/// A request of the other daemon to party `me`, accepted at most once.
pub fn open_request(key: &[u8], me: u8, message: &Value, seen: &ReplayCache) -> Result<(), String> {
    open_request_at(key, me, message, seen, unix_now())
}

fn open_request_at(key: &[u8], me: u8, message: &Value, seen: &ReplayCache, now: u64) -> Result<(), String> {
    let body = verified(key, message, now)?;
    from_other(&body, me)?;
    if body.get("reply_to").is_some() || !body.get("op").and_then(Value::as_str).is_some_and(|op| op.starts_with("peer-")) {
        return Err("not a peer request".into());
    }
    let nonce = body.get("nonce").and_then(Value::as_str).filter(|n| n.len() == 32 && n.bytes().all(|b| b.is_ascii_hexdigit()))
        .ok_or("peer message without nonce")?;
    seen.admit(nonce, body["at"].as_u64().unwrap_or(0), now)
}

/// The other daemon's reply to `request`, which party `me` sent.
pub fn open_reply(key: &[u8], me: u8, request: &Value, reply: &Value) -> Result<(), String> {
    let body = verified(key, reply, unix_now()).map_err(|why| format!("reply: {why}"))?;
    from_other(&body, me).map_err(|why| format!("reply: {why}"))?;
    match (body.get("reply_to"), request.get("nonce")) {
        (Some(a), Some(b)) if a == b && a.is_string() => Ok(()),
        _ => Err("reply: not the reply to this request".into()),
    }
}

// ---- The two ends.

/// This daemon's side of the link, as the caller.
pub struct Link {
    /// The other daemon's `peer_listen`.
    pub address: String,
    pub key: Vec<u8>,
    /// This node's party.
    pub party: u8,
}

impl Link {
    /// A request to the other daemon; its reply only if it is sealed and answers this request.
    pub fn call(&self, message: &PeerMessage) -> Result<PeerReply, String> {
        let request = seal_request(&self.key, self.party, message.encode())?;
        let reply = call(&self.address, &request, Duration::from_secs(5))?;
        open_reply(&self.key, self.party, &request, &reply)?;
        Ok(PeerReply::decode(&reply))
    }
}

/// Answer the other daemon on `listener` (`peer_listen`): each request is opened (refused
/// unsealed, with the reason, when it is not authentic, fresh, from the other party and new),
/// decoded, given to `handle`, and its reply sealed.
pub fn serve(listener: Listener, key: Vec<u8>, party: u8, handle: impl Fn(PeerMessage) -> PeerReply + Send + Sync + 'static) {
    let replay = ReplayCache::default();
    listener.serve(Arc::new(move |message: Value| match open_request(&key, party, &message, &replay) {
        Ok(()) => {
            let reply = match PeerMessage::decode(&message) {
                Ok(decoded) => handle(decoded),
                Err(why) => PeerReply::refused(why),
            };
            seal_reply(&key, party, &message, reply.encode())
        }
        Err(why) => {
            log(&format!("peer message refused: {why}"));
            json!({"ok": false, "error": why})
        }
    }));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn every_variant() -> Vec<(PeerMessage, Value)> {
        let (job, session) = ("ab".repeat(32), "cd".repeat(32));
        vec![
            (PeerMessage::Ping, json!({"op": "peer-ping"})),
            (PeerMessage::Agree { job: job.clone() }, json!({"op": "peer-agree", "job": job})),
            (PeerMessage::Start { job: job.clone(), session: session.clone(), port: Some(23040) },
                json!({"op": "peer-start", "job": job, "session": session, "port": 23040})),
            (PeerMessage::Start { job: job.clone(), session: session.clone(), port: None }, json!({"op": "peer-start", "job": job, "session": session})),
            (PeerMessage::Receive { session: session.clone(), port: 23320 }, json!({"op": "peer-receive", "session": session, "port": 23320})),
            (PeerMessage::Serve { session: session.clone(), port: 23000 }, json!({"op": "peer-serve", "session": session, "port": 23000})),
            (PeerMessage::Ended { session: session.clone() }, json!({"op": "peer-ended", "session": session})),
            (PeerMessage::Finish { job: job.clone() }, json!({"op": "peer-finish", "job": job})),
        ]
    }

    /// Each variant: its wire form (unchanged from the untyped daemon), sealed by party 0, opened
    /// and decoded by party 1 to the same message; then refused as a replay, refused when
    /// reflected to its sender, refused when a field is altered; its sealed reply opens.
    #[test]
    fn each_peer_message() {
        for (message, wire) in every_variant() {
            assert_eq!(message.encode(), wire, "{message:?}");
            assert_eq!(PeerMessage::decode(&wire), Ok(message.clone()));
            let cache = ReplayCache::default();
            let request = seal_request(b"key", 0, message.encode()).unwrap();
            assert!(open_request(b"key", 0, &request, &cache).is_err(), "{message:?} reflected");
            assert_eq!(open_request(b"key", 1, &request, &cache), Ok(()), "{message:?}");
            assert_eq!(PeerMessage::decode(&request), Ok(message.clone()));
            assert_eq!(open_request(b"key", 1, &request, &cache), Err("peer message replayed".to_string()), "{message:?}");
            assert!(open_request(b"key", 1, &request, &ReplayCache::default()).is_ok());   // a fresh cache: only the cache refused it
            let mut altered = request.clone();
            altered["op"] = json!(if wire["op"] == json!("peer-ping") { "peer-agree" } else { "peer-ping" });
            assert_eq!(open_request(b"key", 1, &altered, &ReplayCache::default()), Err("peer message not authenticated".to_string()));
            for reply in [PeerReply::yes(), PeerReply::no(), PeerReply::refused("expired"), PeerReply::busy(None), PeerReply::busy(Some("not idle"))] {
                let sealed = seal_reply(b"key", 1, &request, reply.encode());
                assert_eq!(open_reply(b"key", 0, &request, &sealed), Ok(()));
                assert_eq!(PeerReply::decode(&sealed), reply);
            }
        }
    }

    #[test]
    fn peer_reply_wire() {
        assert_eq!(PeerReply::yes().encode(), json!({"ok": true}));
        assert_eq!(PeerReply::no().encode(), json!({"ok": false}));
        assert_eq!(PeerReply::busy(None).encode(), json!({"ok": false, "busy": true}));
        assert_eq!(PeerReply::busy(Some("x")).encode(), json!({"ok": false, "busy": true, "error": "x"}));
        assert_eq!(PeerReply::refused("expired").encode(), json!({"ok": false, "error": "expired"}));
    }

    #[test]
    fn malformed_peer_messages() {
        let refused = |value: Value| PeerMessage::decode(&value).unwrap_err();
        assert_eq!(refused(json!({"op": "peer-nothing"})), "unknown peer message");
        assert_eq!(refused(json!({"op": "status"})), "unknown peer message");
        assert_eq!(refused(json!({"op": "peer-agree"})), "peer-agree: job");
        assert_eq!(refused(json!({"op": "peer-finish", "job": 7})), "peer-finish: job");
        assert_eq!(refused(json!({"op": "peer-start", "job": "j"})), "peer-start: session");
        assert_eq!(refused(json!({"op": "peer-start", "job": "j", "session": "s", "port": 70000})), "peer-start: port");
        assert_eq!(refused(json!({"op": "peer-start", "job": "j", "session": "s", "port": "1"})), "peer-start: port");
        assert_eq!(refused(json!({"op": "peer-receive", "session": "s"})), "peer-receive: session and port");
        assert_eq!(refused(json!({"op": "peer-serve", "port": 1})), "peer-serve: session and port");
        assert_eq!(refused(json!({"op": "peer-serve", "session": "s", "port": -1})), "peer-serve: session and port");
        assert_eq!(refused(json!({"op": "peer-ended"})), "peer-ended: session");
    }

    #[test]
    fn peer_messages() {
        let cache = ReplayCache::default();
        let sealed = seal_request(b"key", 0, json!({"op": "peer-agree", "job": "ab"})).unwrap();
        assert!(open_request(b"other", 1, &sealed, &cache).is_err());   // wrong key
        let mut changed = sealed.clone();
        changed["job"] = json!("cd");
        assert!(open_request(b"key", 1, &changed, &cache).is_err());   // forged field
        assert!(open_request(b"key", 0, &sealed, &cache).is_err());   // reflected to its sender
        assert!(open_request(b"key", 1, &sealed, &cache).is_ok());
        assert_eq!(open_request(b"key", 1, &sealed, &cache), Err("peer message replayed".to_string()));
    }

    #[test]
    fn peer_freshness_and_replay_window() {
        let cache = ReplayCache::default();
        let now = 1_800_000_000;
        let request = sealed(b"key", json!({"op": "peer-ended", "session": "s", "from": 0, "nonce": "00".repeat(16)}), now);
        assert_eq!(open_request_at(b"key", 1, &request, &cache, now + PEER_SKEW_SECS + 1), Err("peer message is stale".to_string()));
        assert!(open_request_at(b"key", 1, &request, &cache, now - PEER_SKEW_SECS).is_ok());
        // Replayed anywhere in the window it is accepted in: refused.
        for t in [now - PEER_SKEW_SECS, now, now + PEER_SKEW_SECS] {
            assert_eq!(open_request_at(b"key", 1, &request, &cache, t), Err("peer message replayed".to_string()));
        }
        // Expired nonces are forgotten only once their message is stale anyway.
        assert!(cache.seen.lock().unwrap().len() == 1);
        assert!(open_request_at(b"key", 1, &request, &cache, now + PEER_SKEW_SECS + 1).is_err());
        let later = sealed(b"key", json!({"op": "peer-ping", "from": 0, "nonce": "22".repeat(16)}), now + PEER_SKEW_SECS + 1);
        assert!(open_request_at(b"key", 1, &later, &cache, now + PEER_SKEW_SECS + 1).is_ok());
        assert!(cache.seen.lock().unwrap().keys().eq(["22".repeat(16)].iter()));
        // Without a nonce, or with a malformed one: refused.
        let bare = sealed(b"key", json!({"op": "peer-ping", "from": 0}), now);
        assert!(open_request_at(b"key", 1, &bare, &cache, now).is_err());
        let short = sealed(b"key", json!({"op": "peer-ping", "from": 0, "nonce": "ab"}), now);
        assert!(open_request_at(b"key", 1, &short, &cache, now).is_err());
        // A reply is not a request.
        let reply = sealed(b"key", json!({"op": "peer-ping", "from": 0, "nonce": "11".repeat(16), "reply_to": "x"}), now);
        assert_eq!(open_request_at(b"key", 1, &reply, &cache, now), Err("not a peer request".to_string()));
    }

    /// The same nonce under a different body (a replay with a fresh time and MAC, by someone who
    /// holds the key) is still refused while the first is remembered; the cache has a bound.
    #[test]
    fn replay_by_nonce_and_capacity() {
        let cache = ReplayCache::default();
        let now = 1_800_000_000;
        let first = sealed(b"key", json!({"op": "peer-ping", "from": 0, "nonce": "33".repeat(16)}), now);
        let again = sealed(b"key", json!({"op": "peer-finish", "job": "j", "from": 0, "nonce": "33".repeat(16)}), now + 5);
        assert!(open_request_at(b"key", 1, &first, &cache, now).is_ok());
        assert_eq!(open_request_at(b"key", 1, &again, &cache, now + 5), Err("peer message replayed".to_string()));
        let full = ReplayCache::default();
        {
            let mut seen = full.seen.lock().unwrap();
            for i in 0..REPLAY_CAPACITY {
                seen.insert(format!("{i:032x}"), now + PEER_SKEW_SECS);
            }
        }
        let fresh = sealed(b"key", json!({"op": "peer-ping", "from": 0, "nonce": "44".repeat(16)}), now);
        assert_eq!(open_request_at(b"key", 1, &fresh, &full, now), Err("too many peer messages".to_string()));
        // Once the remembered ones are stale they are dropped and new requests are taken again.
        assert!(open_request_at(b"key", 1, &sealed(b"key", json!({"op": "peer-ping", "from": 0, "nonce": "44".repeat(16)}), now + PEER_SKEW_SECS + 1),
            &full, now + PEER_SKEW_SECS + 1).is_ok());
    }

    #[test]
    fn peer_replies() {
        let request = seal_request(b"key", 0, json!({"op": "peer-start", "job": "ab"})).unwrap();
        let reply = seal_reply(b"key", 1, &request, json!({"ok": true}));
        assert!(open_reply(b"key", 0, &request, &reply).is_ok());
        assert_eq!(reply["ok"], json!(true));
        // Unsealed (what an attacker on the link could write), forged, wrong key, own reply reflected.
        assert!(open_reply(b"key", 0, &request, &json!({"ok": true})).is_err());
        let mut forged = reply.clone();
        forged["ok"] = json!(false);
        assert!(open_reply(b"key", 0, &request, &forged).is_err());
        assert!(open_reply(b"other", 0, &request, &reply).is_err());
        assert!(open_reply(b"key", 1, &request, &reply).is_err());
        // The reply to another request (an old one replayed): refused.
        let other = seal_request(b"key", 0, json!({"op": "peer-start", "job": "ab"})).unwrap();
        assert_eq!(open_reply(b"key", 0, &other, &reply), Err("reply: not the reply to this request".to_string()));
    }

    /// Both ends over a loopback socket: every variant reaches the handler decoded, its reply
    /// comes back sealed and checked; the same sealed request sent again is refused.
    #[test]
    fn link_end_to_end() {
        let listener = Listener::bind("127.0.0.1:0").unwrap();
        let address = listener.address();
        let (sender, received) = std::sync::mpsc::channel::<PeerMessage>();
        let sender = std::sync::Mutex::new(sender);
        serve(listener, b"shared key".to_vec(), 1, move |message| {
            let busy = matches!(message, PeerMessage::Start { .. });
            sender.lock().unwrap().send(message).unwrap();
            if busy { PeerReply::busy(None) } else { PeerReply::yes() }
        });
        let link = Link { address: address.clone(), key: b"shared key".to_vec(), party: 0 };
        for (message, _) in every_variant() {
            let reply = link.call(&message).unwrap();
            assert_eq!(received.recv().unwrap(), message);
            assert_eq!(reply, if matches!(message, PeerMessage::Start { .. }) { PeerReply::busy(None) } else { PeerReply::yes() });
        }
        // A link with the wrong key, or the wrong party: refused unsealed, so the caller refuses the reply.
        assert!(Link { address: address.clone(), key: b"other key".to_vec(), party: 0 }.call(&PeerMessage::Ping).is_err());
        assert!(Link { address: address.clone(), key: b"shared key".to_vec(), party: 1 }.call(&PeerMessage::Ping).is_err());
        // The same sealed request twice.
        let request = seal_request(b"shared key", 0, PeerMessage::Ping.encode()).unwrap();
        let first = call(&address, &request, Duration::from_secs(5)).unwrap();
        assert!(open_reply(b"shared key", 0, &request, &first).is_ok() && first["ok"] == json!(true));
        let second = call(&address, &request, Duration::from_secs(5)).unwrap();
        assert_eq!(second, json!({"ok": false, "error": "peer message replayed"}));
        assert!(received.try_recv().is_ok() && received.try_recv().is_err());
    }
}
