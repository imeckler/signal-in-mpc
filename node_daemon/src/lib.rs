//! What the node daemon and the application stand-in share: the application's signed requests
//! (the exact bytes the database nodes verify), the line protocol, and the daemons' link.
//! Everything here is public data. See ../README.md.

use ed25519_dalek::{Signature, VerifyingKey};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// The account's own row on the database nodes; no request may list it (`handoff::ACCOUNT_ID`).
pub const ACCOUNT_ID: u128 = u128::MAX - 1;
/// `handoff::MAX_NOTIFY_IDS`.
pub const MAX_IDS: usize = 100_000;
/// `handoff::MAX_CLOCK_SKEW_SECS`.
pub const MAX_CLOCK_SKEW_SECS: u64 = 30;
/// The longest line either side of a connection accepts.
pub const MAX_LINE: u64 = 16 << 20;
/// The controller's limit on a notify text (bytes of UTF-8).
pub const MAX_MESSAGE_BYTES: usize = 256;

pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out.copy_from_slice(Sha256::digest(data).as_slice());
    out
}

pub fn hmac(key: &[u8], data: &[u8]) -> [u8; 32] {
    let mut block = [0u8; 64];
    if key.len() > 64 {
        block[..32].copy_from_slice(&sha256(key));
    } else {
        block[..key.len()].copy_from_slice(key);
    }
    let mut inner: Vec<u8> = block.iter().map(|b| b ^ 0x36).collect();
    inner.extend_from_slice(data);
    let mut outer: Vec<u8> = block.iter().map(|b| b ^ 0x5c).collect();
    outer.extend_from_slice(&sha256(&inner));
    sha256(&outer)
}

pub fn unix_now() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

pub fn random_bytes(count: usize) -> Result<Vec<u8>, String> {
    let mut out = vec![0u8; count];
    std::fs::File::open("/dev/urandom").and_then(|mut f| f.read_exact(&mut out)).map_err(|e| format!("randomness: {e}"))?;
    Ok(out)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    Notify,
    Delete,
}

impl Kind {
    pub fn name(self) -> &'static str {
        match self {
            Kind::Notify => "notify",
            Kind::Delete => "delete",
        }
    }
}

/// The application's signed request, as `handoff_client sign-request` / `sign-delete` write it.
#[derive(Clone, Debug)]
pub struct Request {
    pub kind: Kind,
    /// Strictly increasing.
    pub ids: Vec<u128>,
    /// SHA-256 of the message text (notify only).
    pub message_hash: [u8; 32],
    pub nonce: [u8; 16],
    pub issued_at: u64,
    pub signature: [u8; 64],
}

fn fixed<const N: usize>(value: &Value, name: &str) -> Result<[u8; N], String> {
    let text = value.get(name).and_then(Value::as_str).ok_or(format!("request: {name} is missing"))?;
    let bytes = hex::decode(text).map_err(|_| format!("request: {name} is not hex"))?;
    <[u8; N]>::try_from(bytes.as_slice()).map_err(|_| format!("request: {name} must be {N} bytes"))
}

impl Request {
    /// From the request file's JSON. Checks the shape and the id list (not empty, at most
    /// `MAX_IDS`, strictly increasing, without the account's id): `handoff::check_id_list`.
    pub fn parse(kind: Kind, value: &Value) -> Result<Request, String> {
        let is_delete = value.get("kind").and_then(Value::as_str) == Some("delete");
        if value.get("kind").is_some() && !is_delete {
            return Err("request: unknown kind".into());
        }
        if is_delete != (kind == Kind::Delete) {
            return Err(format!("request: not a {} request", kind.name()));
        }
        let list = value.get("ids").and_then(Value::as_array).ok_or("request: ids are missing")?;
        let mut ids = Vec::with_capacity(list.len());
        for entry in list {
            let text = entry.as_str().ok_or("request: an id is not a decimal string")?;
            if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
                return Err("request: an id is not a decimal string".into());
            }
            ids.push(text.parse::<u128>().map_err(|_| "request: an id is not a u128")?);
        }
        if ids.is_empty() {
            return Err("request lists no ids".into());
        }
        if ids.contains(&ACCOUNT_ID) {
            return Err("request lists the reserved account id".into());
        }
        if ids.len() > MAX_IDS {
            return Err("request lists too many ids".into());
        }
        if ids.windows(2).any(|w| w[0] >= w[1]) {
            return Err("request ids are not sorted and distinct".into());
        }
        Ok(Request {
            kind,
            ids,
            message_hash: if kind == Kind::Notify { fixed(value, "message_hash")? } else { [0; 32] },
            nonce: fixed(value, "nonce")?,
            issued_at: value.get("issued_at").and_then(Value::as_u64).ok_or("request: issued_at is missing")?,
            signature: fixed(value, "signature")?,
        })
    }

    /// The signed bytes (`handoff::NotifyRequest::encode`, `handoff::DeleteRequest::encode`):
    /// label ‖ issued_at (u64 LE) ‖ nonce (16) [‖ message_hash (32)] ‖ count (u32 LE) ‖ ids (16 bytes BE each).
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(17 + 8 + 16 + 32 + 4 + 16 * self.ids.len());
        out.extend_from_slice(match self.kind {
            Kind::Notify => b"NOTIFY_REQUEST_V1",
            Kind::Delete => b"DELETE_REQUEST_V1",
        });
        out.extend_from_slice(&self.issued_at.to_le_bytes());
        out.extend_from_slice(&self.nonce);
        if self.kind == Kind::Notify {
            out.extend_from_slice(&self.message_hash);
        }
        out.extend_from_slice(&(self.ids.len() as u32).to_le_bytes());
        for id in &self.ids {
            out.extend_from_slice(&id.to_be_bytes());
        }
        out
    }

    /// SHA-256 of the signed bytes: the request's name everywhere (the database nodes' too).
    pub fn digest(&self) -> [u8; 32] {
        sha256(&self.encode())
    }

    /// The application's signature (strict Ed25519, as the nodes check it).
    pub fn verify_signature(&self, key: &[u8; 32]) -> Result<(), String> {
        let key = VerifyingKey::from_bytes(key).map_err(|_| "the application's public key is invalid")?;
        key.verify_strict(&self.encode(), &Signature::from_bytes(&self.signature))
            .map_err(|_| "request signature is invalid".to_string())
    }

    /// `handoff::check_freshness`: issued_at in [now - max_age, now + MAX_CLOCK_SKEW_SECS].
    pub fn check_freshness(&self, now: u64, max_age: u64) -> Result<(), String> {
        if self.issued_at > now.saturating_add(MAX_CLOCK_SKEW_SECS) {
            return Err("request is dated in the future".into());
        }
        if self.issued_at < now.saturating_sub(max_age) {
            return Err("request has expired".into());
        }
        Ok(())
    }

    /// The file the database client takes (`--request`).
    pub fn file_json(&self) -> Value {
        let ids: Vec<String> = self.ids.iter().map(|id| id.to_string()).collect();
        match self.kind {
            Kind::Notify => json!({"ids": ids, "message_hash": hex::encode(self.message_hash), "nonce": hex::encode(self.nonce),
                "issued_at": self.issued_at, "signature": hex::encode(self.signature)}),
            Kind::Delete => json!({"kind": "delete", "ids": ids, "nonce": hex::encode(self.nonce),
                "issued_at": self.issued_at, "signature": hex::encode(self.signature)}),
        }
    }
}

/// A 32-byte public key in base64 (as the database network config spells it).
pub fn public_key(text: &str) -> Result<[u8; 32], String> {
    use base64::Engine;
    let bytes = base64::engine::general_purpose::STANDARD.decode(text.trim()).map_err(|_| "public key is not base64")?;
    <[u8; 32]>::try_from(bytes.as_slice()).map_err(|_| "public key must be 32 bytes".to_string())
}

/// The digest both daemons' results must share: over the fields that are the same on both
/// nodes by construction. serde_json writes object keys in sorted order.
pub fn result_digest(common: &Value) -> String {
    hex::encode(sha256(common.to_string().as_bytes()))
}

// ---- The line protocol: one JSON object per line, one request and one reply per connection.

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

/// One request to a daemon. `timeout` bounds connecting and the wait for the reply.
pub fn call(address: &str, request: &Value, timeout: Duration) -> Result<Value, String> {
    let target = address.to_socket_addrs().map_err(|e| format!("{address}: {e}"))?.next().ok_or(format!("{address}: no address"))?;
    let mut stream = TcpStream::connect_timeout(&target, timeout.min(Duration::from_secs(5))).map_err(|e| format!("{address}: {e}"))?;
    stream.set_read_timeout(Some(timeout)).map_err(|e| e.to_string())?;
    stream.set_write_timeout(Some(timeout)).map_err(|e| e.to_string())?;
    write_line(&mut stream, request)?;
    read_line(&mut stream)
}

// ---- The link between the two daemons: the same line protocol (on its own listener,
// `peer_listen`), each message carrying the sender's party, a fresh nonce, the sender's clock and
// an HMAC-SHA256 under a key the two nodes share.
//
// A request: {"op": "peer-…", …, "from", "nonce", "at", "mac"}. The receiver accepts it once:
// the MAC, the sender being the other party (a message reflected back to its sender is refused),
// the clock within PEER_SKEW_SECS, and a nonce not seen before (`ReplayCache`).
// A reply: {…, "from", "reply_to" (the request's nonce), "at", "mac"}, checked by the caller
// against the request it sent, so a reply cannot be forged, replayed, or taken from another call.

pub const PEER_SKEW_SECS: u64 = 60;
/// Nonces remembered at most (one per peer request within two minutes; the leader sends a few a second).
pub const REPLAY_CAPACITY: usize = 1 << 16;

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

#[cfg(test)]
mod tests {
    use super::*;

    // A request file written by `handoff_client sign-request` (five test nodes' application key).
    #[test]
    fn notify_request_of_the_database_client_verifies() {
        let file = json!({"ids": ["1", "2", "3"], "message_hash": "e88199c423228a456677d367059b4f9b9fc769bae4a5c88aef9f7d0fcbe0726b",
            "nonce": "d45ce41ccbd6657314d1c01b7418c4a8", "issued_at": 1794438273u64,
            "signature": "dd5d75ffa3e08f149a7252cfd88694a3a8b144a64c05939fe11bbbcb2e4fba3d660d1fbd0e1a93e2ce99e8effc537d92e6b8589c46c4b8bf4dab87cebc9d9503"});
        let key = public_key("xtRBqabaPZLqaUJuWOWU4aZqI9dnHm+CxEbQOK4sSE8=").unwrap();
        let request = Request::parse(Kind::Notify, &file).unwrap();
        request.verify_signature(&key).unwrap();
        assert_eq!(request.file_json(), file);
        let mut other = request.clone();
        other.ids.push(9);
        assert!(other.verify_signature(&key).is_err());
        let mut as_delete = request.clone();
        as_delete.kind = Kind::Delete;
        assert!(as_delete.verify_signature(&key).is_err());
        assert!(request.check_freshness(1794438273 + 120, 120).is_ok());
        assert!(request.check_freshness(1794438273 + 121, 120).is_err());
        assert!(request.check_freshness(1794438273 - 31, 120).is_err());
    }

    #[test]
    fn id_lists() {
        let base = |ids: Value| json!({"ids": ids, "message_hash": "00".repeat(32), "nonce": "00".repeat(16), "issued_at": 1, "signature": "00".repeat(64)});
        assert!(Request::parse(Kind::Notify, &base(json!(["1", "2"]))).is_ok());
        assert!(Request::parse(Kind::Notify, &base(json!([]))).is_err());
        assert!(Request::parse(Kind::Notify, &base(json!(["2", "1"]))).is_err());
        assert!(Request::parse(Kind::Notify, &base(json!(["1", "1"]))).is_err());
        assert!(Request::parse(Kind::Notify, &base(json!([ACCOUNT_ID.to_string()]))).is_err());
        assert!(Request::parse(Kind::Notify, &base(json!([1]))).is_err());
        assert!(Request::parse(Kind::Delete, &base(json!(["1"]))).is_err());
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
        // RFC 4231 test case 2.
        assert_eq!(hex::encode(hmac(b"Jefe", b"what do ya want for nothing?")), "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843");
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
}
