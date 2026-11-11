//! lss-provision: a small CONVENTIONAL Signal client for the LOCAL Signal-Server only.
//!
//! It creates the server-side and client-side state that the MPC client needs, using
//! libsignal-protocol v0.106.1 (the same source tls-mpc's oracles use) and the chat
//! WebSocket request sub-protocol (the same framing the MPC client uses).
//!
//! The server address is fixed to the local plain port 127.0.0.1:18080 (override with
//! LSS_SERVER=127.0.0.1:PORT; any non-loopback host is refused). It never talks to Signal.
//!
//! Commands (state lives in ../state/accounts/<name>.json, git-ignored, LOCAL TEST KEYS ONLY):
//!   register  NAME NUMBER          verification session (stub: captcha noop, any code),
//!                                  POST /v1/registration, PUT /v2/keys, GET /v1/certificate/delivery
//!   establish FROM TO              FROM fetches TO's bundle, sends a sealed-sender PreKey message,
//!                                  TO receives + decrypts and replies, FROM receives the reply
//!                                  (both sessions are then "established", i.e. send SignalMessages)
//!   send      FROM TO TEXT         sealed-sender text, unauthenticated socket + Unidentified-Access-Key
//!   mpc-send  FROM TO TEXT         same send, but with the MPC client's exact request bytes
//!                                  (PublicRequest.build) on FROM's AUTHENTICATED socket; saves
//!                                  request/response bytes to ../state/transcripts/
//!   receive   NAME [SECONDS]       authenticated socket; decrypt and print every delivered message
//!                                  (NAME.2 receives as the device that `link NAME` added)
//!   link      NAME [ONE_TIME]      link a further device to NAME's account (provisioning code from the
//!                                  primary, PUT /v1/devices/link), with ONE_TIME one-time prekeys
//!                                  (default 0); saved as account NAME.<device id>
//!   keys-dump NAME OUT             raw body of GET /v2/keys/{aci}/* (every device's prekey bundle)
//!   reregister NAME                register NAME's number again: same account id and profile key,
//!                                  new identity key (what a contact's reinstall looks like)
//!   unlink NAME DEVICE             the primary removes linked device DEVICE
//!   delete NAME                    delete NAME's account on the server
//!   rotate-access NAME             new profile key, so the account's access key changes
//!   provision                      register sender + recipient + recipient2, establish both,
//!                                  send + receive one text
//!   export-mpc [SENDER CONTACT..]  write ../state/mpc-export.json: everything the MPC client needs
//!                                  (credentials, identity secret, conversation records); see mpc.rs
//!   ref-send  TEXT                 reference sender reading ONLY the export: one MPC-shaped send per
//!                                  contact on an UNAUTHENTICATED socket; writes the advanced records back
//!   probe-sockets DIR [IDLE_SECS]  unauthenticated vs authenticated socket: queue/empty, keepalive
//!                                  request/response bytes (saved to DIR), idle close behaviour
//!   show      NAME                 print the public parts of an account (aci, device, registration id, ...)
use base64::Engine;
use base64::engine::general_purpose::{STANDARD, STANDARD_NO_PAD};
use libsignal_core::DeviceId;
use libsignal_protocol::*;
use prost::Message as _;
use rand::Rng;
use serde_json::{Value, json};
use std::net::TcpStream;
use std::path::PathBuf;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use tungstenite::client::IntoClientRequest;

mod wsproto {
    include!(concat!(env!("OUT_DIR"), "/signal.proto.chat_websocket.rs"));
}
/// libsignal storage.proto (SessionRecord); same module name as in signal_backend/Oracle.
#[allow(dead_code, clippy::all)]
mod storage {
    include!(concat!(env!("OUT_DIR"), "/signal.proto.storage.rs"));
}
/// SPQR pq_ratchet.proto; same module name as in signal_backend/Oracle.
#[allow(dead_code, clippy::all)]
mod pqr {
    include!(concat!(env!("OUT_DIR"), "/signal.proto.pq_ratchet.rs"));
}
mod mpc;
use wsproto::{WebSocketMessage, WebSocketRequestMessage, WebSocketResponseMessage, web_socket_message};

type R<T> = Result<T, Box<dyn std::error::Error>>;

/// Upstream Signal-Server test trust root (service/src/test/resources/config/test-secrets-bundle.yml,
/// "Trust root for the certificate in test.yml"). Sender certificates from the local server chain to it.
const TEST_TRUST_ROOT: &str = "BS/lfaNHzWJDFSjarF+7KQcw//aEr8TPwu2QmV9Yyzt0";
/// Accepted by the stub registration service / captcha checker in LocalWhisperServerService.
const NOOP_CAPTCHA: &str = "noop.noop.registration.noop";
/// The MPC client's password slot is exactly 22 bytes (service_kernels.h: PASSWORD=22).
const PASSWORD_LEN: usize = 22;
const ONE_TIME_PREKEYS: u32 = 10;

fn server() -> R<String> {
    let s = std::env::var("LSS_SERVER").unwrap_or_else(|_| "127.0.0.1:18080".into());
    let host = s.rsplit_once(':').map(|(h, _)| h).unwrap_or("");
    if !matches!(host, "127.0.0.1" | "localhost" | "[::1]") {
        return Err(format!("refusing non-local server {s}").into());
    }
    Ok(s)
}

fn now_ms() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis() as u64
}
fn b64(b: &[u8]) -> String {
    STANDARD.encode(b)
}
fn unb64(s: &str) -> R<Vec<u8>> {
    Ok(STANDARD.decode(s).or_else(|_| STANDARD_NO_PAD.decode(s.trim_end_matches('=')))?)
}
fn device1() -> DeviceId {
    DeviceId::new(1).unwrap()
}

// ---------------------------------------------------------------------------------------------
// Chat WebSocket (request/response sub-protocol)

/// A server-initiated request (e.g. PUT /api/v1/message with an Envelope body).
struct Pushed {
    path: String,
    body: Vec<u8>,
}

/// TCP stream that records every byte in each direction (for byte-exact samples in testdata/).
struct Tee {
    inner: TcpStream,
    rx: std::rc::Rc<std::cell::RefCell<Vec<u8>>>,
    tx: std::rc::Rc<std::cell::RefCell<Vec<u8>>>,
}
impl std::io::Read for Tee {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let n = self.inner.read(buf)?;
        self.rx.borrow_mut().extend_from_slice(&buf[..n]);
        Ok(n)
    }
}
impl std::io::Write for Tee {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let n = self.inner.write(buf)?;
        self.tx.borrow_mut().extend_from_slice(&buf[..n]);
        Ok(n)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
    }
}

struct Chat {
    ws: tungstenite::WebSocket<Tee>,
    /// Raw bytes received from / sent to the server on this connection (HTTP head + frames).
    server_bytes: std::rc::Rc<std::cell::RefCell<Vec<u8>>>,
    client_bytes: std::rc::Rc<std::cell::RefCell<Vec<u8>>>,
    next_id: u64,
    inbox: Vec<Pushed>,
    queue_empty: bool,
    /// Raw WebSocketMessage bytes of the last response read (for offline parser checks).
    last_response_raw: Vec<u8>,
}

impl Chat {
    fn connect(auth: Option<(&str, &str)>) -> R<Chat> {
        let addr = server()?;
        let stream = TcpStream::connect(&addr)?;
        stream.set_read_timeout(Some(Duration::from_millis(500)))?;
        let mut req = format!("ws://{addr}/v1/websocket/").into_client_request()?;
        let h = req.headers_mut();
        h.insert("User-Agent", "lss-provision".parse()?);
        h.insert("X-Signal-Receive-Stories", "false".parse()?);
        h.insert("Accept-Language", "en".parse()?);
        if let Some((u, p)) = auth {
            h.insert("Authorization", format!("Basic {}", b64(format!("{u}:{p}").as_bytes())).parse()?);
        }
        let rx = std::rc::Rc::new(std::cell::RefCell::new(vec![]));
        let tx = std::rc::Rc::new(std::cell::RefCell::new(vec![]));
        let tee = Tee { inner: stream, rx: rx.clone(), tx: tx.clone() };
        let (ws, resp) = tungstenite::client::client(req, tee).map_err(|e| format!("websocket upgrade failed: {e}"))?;
        if resp.status().as_u16() != 101 {
            return Err(format!("upgrade status {}", resp.status()).into());
        }
        Ok(Chat { ws, server_bytes: rx, client_bytes: tx, next_id: 1, inbox: vec![], queue_empty: false, last_response_raw: vec![] })
    }

    fn send_frame(&mut self, m: WebSocketMessage) -> R<()> {
        self.ws.send(tungstenite::Message::Binary(m.encode_to_vec().into()))?;
        Ok(())
    }

    /// Read one frame (None on read timeout). Server requests are acknowledged with 200 and queued.
    fn poll(&mut self) -> R<Option<WebSocketResponseMessage>> {
        let frame = match self.ws.read() {
            Ok(f) => f,
            Err(tungstenite::Error::Io(e))
                if matches!(e.kind(), std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut) =>
            {
                return Ok(None);
            }
            Err(e) => return Err(e.into()),
        };
        let data = match frame {
            tungstenite::Message::Binary(b) => b,
            tungstenite::Message::Close(c) => return Err(format!("server closed websocket: {c:?}").into()),
            _ => return Ok(None), // ping/pong handled by tungstenite
        };
        let m = WebSocketMessage::decode(&data[..])?;
        match m.r#type() {
            web_socket_message::Type::Response => {
                self.last_response_raw = data.to_vec();
                Ok(m.response)
            }
            web_socket_message::Type::Request => {
                let q = m.request.unwrap_or_default();
                let ack = WebSocketMessage {
                    r#type: Some(web_socket_message::Type::Response as i32),
                    request: None,
                    response: Some(WebSocketResponseMessage {
                        id: q.id,
                        status: Some(200),
                        message: Some("OK".into()),
                        headers: vec![],
                        body: None,
                    }),
                };
                self.send_frame(ack)?;
                let path = q.path.clone().unwrap_or_default();
                if path == "/api/v1/queue/empty" {
                    self.queue_empty = true;
                } else {
                    self.inbox.push(Pushed { path, body: q.body.unwrap_or_default() });
                }
                Ok(None)
            }
            _ => Err("unknown websocket message type".into()),
        }
    }

    /// Send a request and wait for its response. Returns (status, body).
    fn request(&mut self, verb: &str, path: &str, headers: &[(&str, String)], body: Option<Value>) -> R<(u32, Vec<u8>)> {
        let id = self.next_id;
        self.next_id += 1;
        let mut hs: Vec<String> = headers.iter().map(|(k, v)| format!("{k}: {v}")).collect();
        let body = body.map(|b| {
            hs.push("content-type: application/json".into());
            b.to_string().into_bytes()
        });
        self.send_frame(WebSocketMessage {
            r#type: Some(web_socket_message::Type::Request as i32),
            request: Some(WebSocketRequestMessage { verb: Some(verb.into()), path: Some(path.into()), body, headers: hs, id: Some(id) }),
            response: None,
        })?;
        let deadline = Instant::now() + Duration::from_secs(60);
        while Instant::now() < deadline {
            if let Some(r) = self.poll()? {
                if r.id == Some(id) {
                    let status = r.status.unwrap_or(0);
                    let body = r.body.unwrap_or_default();
                    eprintln!("  {verb} {} -> {status}", path.split('?').next().unwrap_or(path));
                    return Ok((status, body));
                }
            }
        }
        Err(format!("timeout waiting for {verb} {path}").into())
    }

    fn expect(&mut self, verb: &str, path: &str, headers: &[(&str, String)], body: Option<Value>, ok: &[u32]) -> R<Value> {
        let (status, bytes) = self.request(verb, path, headers, body)?;
        if !ok.contains(&status) {
            return Err(format!("{verb} {path}: status {status} body {}", String::from_utf8_lossy(&bytes)).into());
        }
        Ok(if bytes.is_empty() { Value::Null } else { serde_json::from_slice(&bytes).unwrap_or(Value::Null) })
    }

    /// Wait until `n` message deliveries are queued (or the timeout passes).
    fn wait_messages(&mut self, n: usize, timeout: Duration) -> R<Vec<Pushed>> {
        let deadline = Instant::now() + timeout;
        while Instant::now() < deadline && self.inbox.iter().filter(|p| p.path == "/api/v1/message").count() < n {
            self.poll()?;
        }
        Ok(std::mem::take(&mut self.inbox).into_iter().filter(|p| p.path == "/api/v1/message").collect())
    }

    fn close(mut self) {
        let _ = self.ws.close(None);
        let _ = self.ws.flush();
    }
}

// ---------------------------------------------------------------------------------------------
// Protobufs not in the chat schema

/// Signal-Server service/src/main/proto/TextSecure.proto `Envelope` (subset).
#[derive(Clone, PartialEq, prost::Message)]
struct Envelope {
    #[prost(int32, optional, tag = "1")]
    r#type: Option<i32>,
    #[prost(uint64, optional, tag = "5")]
    client_timestamp: Option<u64>,
    #[prost(uint32, optional, tag = "7")]
    source_device: Option<u32>,
    #[prost(string, optional, tag = "11")]
    source_service_id: Option<String>,
    #[prost(bytes = "vec", optional, tag = "8")]
    content: Option<Vec<u8>>,
    #[prost(uint64, optional, tag = "10")]
    server_timestamp: Option<u64>,
    #[prost(string, optional, tag = "13")]
    destination_service_id: Option<String>,
    #[prost(bool, optional, tag = "14")]
    urgent: Option<bool>,
}

/// Signal Content { DataMessage dataMessage = 1 } / DataMessage { body = 1, timestamp = 7 } (subset).
#[derive(Clone, PartialEq, prost::Message)]
struct Content {
    #[prost(message, optional, tag = "1")]
    data_message: Option<DataMessage>,
}
#[derive(Clone, PartialEq, prost::Message)]
struct DataMessage {
    #[prost(string, optional, tag = "1")]
    body: Option<String>,
    #[prost(bytes = "vec", optional, tag = "6")]
    profile_key: Option<Vec<u8>>,
    #[prost(uint64, optional, tag = "7")]
    timestamp: Option<u64>,
}

/// Content bytes with Signal's transport padding (0x80 terminator, zero fill to a multiple of 80).
fn text_content(text: &str, timestamp: u64) -> Vec<u8> {
    content_with(text, timestamp, None)
}
/// The same with the sender's profile key (what a client sends to a contact it shares its profile with).
fn content_with(text: &str, timestamp: u64, profile_key: Option<Vec<u8>>) -> Vec<u8> {
    let mut v = Content { data_message: Some(DataMessage { body: Some(text.into()), profile_key, timestamp: Some(timestamp) }) }.encode_to_vec();
    v.push(0x80);
    while v.len() % 80 != 0 {
        v.push(0);
    }
    v
}
fn parse_content(padded: &[u8]) -> R<(String, u64)> {
    let mut end = padded.len();
    while end > 0 && padded[end - 1] == 0 {
        end -= 1;
    }
    if end == 0 || padded[end - 1] != 0x80 {
        return Err("bad content padding".into());
    }
    let c = Content::decode(&padded[..end - 1])?;
    let d = c.data_message.ok_or("no dataMessage")?;
    Ok((d.body.unwrap_or_default(), d.timestamp.unwrap_or(0)))
}

/// zkgroup ProfileKey::derive_access_key: AES-256-GCM(profile key, zero nonce) over 16 zero bytes.
fn access_key(profile_key: &[u8; 32]) -> [u8; 16] {
    let mut buf = [0u8; 16];
    let mut c = signal_crypto::Aes256GcmEncryption::new(profile_key, &[0u8; 12], &[]).unwrap();
    c.encrypt(&mut buf);
    buf
}

// ---------------------------------------------------------------------------------------------
// Account state

struct Account {
    name: String,
    number: String,
    aci: String,
    pni: String,
    password: String,
    registration_id: u32,
    pni_registration_id: u32,
    profile_key: [u8; 32],
    pni_identity: IdentityKeyPair,
    store: InMemSignalProtocolStore,
    sender_certificate: Option<Vec<u8>>,
    peers: Vec<String>,
    /// 1 for the primary device; a linked device (`link`) has its own file `<name>.<id>.json`.
    device_id: u8,
}

fn state_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../state/accounts")
}

impl Account {
    fn path(name: &str) -> PathBuf {
        state_dir().join(format!("{name}.json"))
    }
    fn address(&self) -> ProtocolAddress {
        ProtocolAddress::new(self.aci.clone(), DeviceId::new(self.device_id).unwrap())
    }
    /// The chat socket's user name: the account id, with `.DEVICE` for a linked device.
    fn login(&self) -> String {
        if self.device_id == 1 { self.aci.clone() } else { format!("{}.{}", self.aci, self.device_id) }
    }
    fn access_key(&self) -> [u8; 16] {
        access_key(&self.profile_key)
    }

    async fn save(&self) -> R<()> {
        let s = &self.store;
        let mut prekeys = serde_json::Map::new();
        for id in s.all_pre_key_ids().cloned().collect::<Vec<_>>() {
            prekeys.insert(u32::from(id).to_string(), b64(&s.get_pre_key(id).await?.serialize()?).into());
        }
        let mut signed = serde_json::Map::new();
        for id in s.all_signed_pre_key_ids().cloned().collect::<Vec<_>>() {
            signed.insert(u32::from(id).to_string(), b64(&s.get_signed_pre_key(id).await?.serialize()?).into());
        }
        let mut kyber = serde_json::Map::new();
        for id in s.all_kyber_pre_key_ids().cloned().collect::<Vec<_>>() {
            kyber.insert(u32::from(id).to_string(), b64(&s.get_kyber_pre_key(id).await?.serialize()?).into());
        }
        let mut sessions = serde_json::Map::new();
        let mut identities = serde_json::Map::new();
        for peer in &self.peers {
            let a = ProtocolAddress::new(peer.clone(), device1());
            if let Some(r) = s.load_session(&a).await? {
                sessions.insert(format!("{peer}.1"), b64(&r.serialize()?).into());
            }
            if let Some(k) = s.get_identity(&a).await? {
                identities.insert(format!("{peer}.1"), b64(&k.serialize()).into());
            }
        }
        let v = json!({
            "WARNING": "LOCAL TEST ACCOUNT on the local Signal-Server only; never use against Signal's service",
            "name": self.name, "number": self.number, "aci": self.aci, "pni": self.pni, "device_id": self.device_id,
            "password": self.password, "registration_id": self.registration_id,
            "pni_registration_id": self.pni_registration_id,
            "profile_key": b64(&self.profile_key), "access_key": b64(&self.access_key()),
            "aci_identity_key_pair": b64(&s.get_identity_key_pair().await?.serialize()),
            "aci_identity_key": b64(&s.get_identity_key_pair().await?.identity_key().serialize()),
            "pni_identity_key_pair": b64(&self.pni_identity.serialize()),
            "sender_certificate": self.sender_certificate.as_ref().map(|c| b64(c)),
            "trust_root": TEST_TRUST_ROOT,
            "prekeys": prekeys, "signed_prekeys": signed, "kyber_prekeys": kyber,
            "peers": self.peers, "sessions": sessions, "identities": identities,
        });
        std::fs::create_dir_all(state_dir())?;
        let path = Self::path(&self.name);
        std::fs::write(&path, serde_json::to_string_pretty(&v)? + "\n")?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600))?;
        }
        Ok(())
    }

    async fn load(name: &str) -> R<Account> {
        let v: Value = serde_json::from_str(&std::fs::read_to_string(Self::path(name))?)?;
        let st = |k: &str| -> R<String> { Ok(v[k].as_str().ok_or(format!("missing {k}"))?.to_string()) };
        let identity = IdentityKeyPair::try_from(&unb64(&st("aci_identity_key_pair")?)?[..])?;
        let mut store = InMemSignalProtocolStore::new(identity, v["registration_id"].as_u64().ok_or("registration_id")? as u32)?;
        for (id, rec) in v["prekeys"].as_object().into_iter().flatten() {
            store.save_pre_key(id.parse::<u32>()?.into(), &PreKeyRecord::deserialize(&unb64(rec.as_str().unwrap())?)?).await?;
        }
        for (id, rec) in v["signed_prekeys"].as_object().into_iter().flatten() {
            store.save_signed_pre_key(id.parse::<u32>()?.into(), &SignedPreKeyRecord::deserialize(&unb64(rec.as_str().unwrap())?)?).await?;
        }
        for (id, rec) in v["kyber_prekeys"].as_object().into_iter().flatten() {
            store.save_kyber_pre_key(id.parse::<u32>()?.into(), &KyberPreKeyRecord::deserialize(&unb64(rec.as_str().unwrap())?)?).await?;
        }
        let peers: Vec<String> = v["peers"].as_array().into_iter().flatten().filter_map(|p| p.as_str().map(String::from)).collect();
        for peer in &peers {
            let a = ProtocolAddress::new(peer.clone(), device1());
            if let Some(r) = v["sessions"][format!("{peer}.1")].as_str() {
                store.store_session(&a, &SessionRecord::deserialize(&unb64(r)?)?).await?;
            }
            if let Some(k) = v["identities"][format!("{peer}.1")].as_str() {
                store.save_identity(&a, &IdentityKey::decode(&unb64(k)?)?).await?;
            }
        }
        let mut profile_key = [0u8; 32];
        profile_key.copy_from_slice(&unb64(&st("profile_key")?)?);
        Ok(Account {
            name: st("name")?,
            number: st("number")?,
            aci: st("aci")?,
            pni: st("pni")?,
            password: st("password")?,
            registration_id: v["registration_id"].as_u64().unwrap() as u32,
            pni_registration_id: v["pni_registration_id"].as_u64().unwrap() as u32,
            profile_key,
            pni_identity: IdentityKeyPair::try_from(&unb64(&st("pni_identity_key_pair")?)?[..])?,
            store,
            sender_certificate: v["sender_certificate"].as_str().map(unb64).transpose()?,
            peers,
            device_id: v["device_id"].as_u64().unwrap_or(1) as u8,
        })
    }

    fn add_peer(&mut self, aci: &str) {
        if !self.peers.iter().any(|p| p == aci) {
            self.peers.push(aci.to_string());
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Key material helpers

fn signed_prekey<Rn: Rng + rand::CryptoRng>(identity: &IdentityKeyPair, id: u32, rng: &mut Rn) -> R<SignedPreKeyRecord> {
    let pair = KeyPair::generate(rng);
    let sig = identity.private_key().calculate_signature(&pair.public_key.serialize(), rng)?;
    Ok(SignedPreKeyRecord::new(id.into(), Timestamp::from_epoch_millis(now_ms()), &pair, &sig))
}
fn kyber_prekey(identity: &IdentityKeyPair, id: u32) -> R<KyberPreKeyRecord> {
    Ok(KyberPreKeyRecord::generate(kem::KeyType::Kyber1024, id.into(), identity.private_key())?)
}
fn ec_signed_json(r: &SignedPreKeyRecord) -> R<Value> {
    Ok(json!({"keyId": u32::from(r.id()?), "publicKey": b64(&r.public_key()?.serialize()), "signature": b64(&r.signature()?)}))
}
fn kem_signed_json(r: &KyberPreKeyRecord) -> R<Value> {
    Ok(json!({"keyId": u32::from(r.id()?), "publicKey": b64(&r.public_key()?.serialize()), "signature": b64(&r.signature()?)}))
}

// ---------------------------------------------------------------------------------------------
// Commands

async fn register(name: &str, number: &str) -> R<()> {
    register_with(name, number, false).await
}
/// `unrestricted`: the account accepts sealed-sender messages from anyone, without its access
/// key. An account that strangers sign up to (the MPC client's) needs this: a new user does not
/// know its profile key, and without sealed sender the server would learn who signs up.
async fn register_with(name: &str, number: &str, unrestricted: bool) -> R<()> {
    register_full(name, number, unrestricted, None).await
}
/// `profile_key`: keep this profile key (so the account's access key stays what its contacts
/// hold) instead of generating one; used by `reregister`.
async fn register_full(name: &str, number: &str, unrestricted: bool, profile_key: Option<[u8; 32]>) -> R<()> {
    eprintln!("register {name} ({number})");
    let mut rng = rand::rng();
    let aci_identity = IdentityKeyPair::generate(&mut rng);
    let pni_identity = IdentityKeyPair::generate(&mut rng);
    let registration_id = rng.random_range(1..=0x3fff_u32);
    let pni_registration_id = rng.random_range(1..=0x3fff_u32);
    const ALPHABET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    let password: String = (0..PASSWORD_LEN).map(|_| ALPHABET[rng.random_range(0..ALPHABET.len())] as char).collect();
    let profile_key: [u8; 32] = match profile_key {
        Some(kept) => kept,
        None => rng.random(),
    };
    let recovery_password: [u8; 32] = rng.random();

    let aci_spk = signed_prekey(&aci_identity, 1, &mut rng)?;
    let pni_spk = signed_prekey(&pni_identity, 1, &mut rng)?;
    let aci_kyber_lr = kyber_prekey(&aci_identity, 1)?;
    let pni_kyber_lr = kyber_prekey(&pni_identity, 1)?;

    // 1. Verification session over the unauthenticated socket (stub registration service locally).
    let mut chat = Chat::connect(None)?;
    let session = chat.expect("POST", "/v1/verification/session", &[], Some(json!({"number": number})), &[200])?;
    let id = session["id"].as_str().ok_or("no session id")?.to_string();
    let requested: Vec<String> = session["requestedInformation"].as_array().into_iter().flatten().filter_map(|x| x.as_str().map(String::from)).collect();
    eprintln!("  session requestedInformation={requested:?} allowedToRequestCode={}", session["allowedToRequestCode"]);
    let mut session = session;
    if requested.iter().any(|r| r == "captcha") {
        session = chat.expect("PATCH", &format!("/v1/verification/session/{id}"), &[], Some(json!({"captcha": NOOP_CAPTCHA})), &[200])?;
    }
    if session["allowedToRequestCode"] != json!(true) {
        return Err(format!("session does not allow requesting a code: {session}").into());
    }
    chat.expect("POST", &format!("/v1/verification/session/{id}/code"), &[("accept-language", "en".into())],
        Some(json!({"transport": "sms", "client": "lss-provision"})), &[200])?;
    let verified = chat.expect("PUT", &format!("/v1/verification/session/{id}/code"), &[], Some(json!({"code": "123456"})), &[200])?;
    if verified["verified"] != json!(true) {
        return Err(format!("session not verified: {verified}").into());
    }

    // 2. Register (Basic auth = number:password; the password becomes the account's chat password).
    let auth = format!("Basic {}", b64(format!("{number}:{password}").as_bytes()));
    let body = json!({
        "sessionId": id,
        "accountAttributes": {
            "fetchesMessages": true,
            "registrationId": registration_id,
            "pniRegistrationId": pni_registration_id,
            "capabilities": {"spqr": true},
            "unidentifiedAccessKey": b64(&access_key(&profile_key)),
            "unrestrictedUnidentifiedAccess": unrestricted,
            "discoverableByPhoneNumber": false,
            "recoveryPassword": b64(&recovery_password),
        },
        "skipDeviceTransfer": true,
        "aciIdentityKey": b64(&aci_identity.identity_key().serialize()),
        "pniIdentityKey": b64(&pni_identity.identity_key().serialize()),
        "aciSignedPreKey": ec_signed_json(&aci_spk)?,
        "pniSignedPreKey": ec_signed_json(&pni_spk)?,
        "aciPqLastResortPreKey": kem_signed_json(&aci_kyber_lr)?,
        "pniPqLastResortPreKey": kem_signed_json(&pni_kyber_lr)?,
    });
    let reg = chat.expect("POST", "/v1/registration", &[("authorization", auth)], Some(body), &[200])?;
    chat.close();
    let aci = reg["uuid"].as_str().ok_or("no uuid")?.to_string();
    let pni = reg["pni"].as_str().unwrap_or_default().to_string();
    eprintln!("  registered aci={aci}");

    let mut store = InMemSignalProtocolStore::new(aci_identity.clone(), registration_id)?;
    store.save_signed_pre_key(1.into(), &aci_spk).await?;
    store.save_kyber_pre_key(1.into(), &aci_kyber_lr).await?;

    // 3. One-time EC prekeys (ACI) on the authenticated socket. One-time PQ prekeys are NOT uploaded:
    //    the server keeps them in S3, which the local configuration deliberately disables (no AWS);
    //    bundles then carry the signed last-resort PQ key (id 1), which is valid PQXDH.
    let mut prekeys = vec![];
    for i in 0..ONE_TIME_PREKEYS {
        let pid = 100 + i;
        let pair = KeyPair::generate(&mut rng);
        let rec = PreKeyRecord::new(pid.into(), &pair);
        store.save_pre_key(pid.into(), &rec).await?;
        prekeys.push(json!({"keyId": pid, "publicKey": b64(&pair.public_key.serialize())}));
    }
    let mut chat = Chat::connect(Some((&aci, &password)))?;
    chat.expect("PUT", "/v2/keys?identity=aci", &[], Some(json!({"preKeys": prekeys, "pqPreKeys": []})), &[200, 204])?;
    let counts = chat.expect("GET", "/v2/keys?identity=aci", &[], None, &[200])?;
    eprintln!("  prekey counts {counts}");

    // 4. Sender certificate (without e164).
    let cert = chat.expect("GET", "/v1/certificate/delivery?includeE164=false", &[], None, &[200])?;
    let cert = unb64(cert["certificate"].as_str().ok_or("no certificate")?)?;
    let parsed = SenderCertificate::deserialize(&cert)?;
    let root = PublicKey::deserialize(&unb64(TEST_TRUST_ROOT)?)?;
    if !parsed.validate(&root, Timestamp::from_epoch_millis(now_ms()))? {
        return Err("sender certificate does not validate against the test trust root".into());
    }
    eprintln!("  sender certificate ok ({} bytes, expires {})", cert.len(), parsed.expiration()?.epoch_millis());
    chat.close();

    Account {
        name: name.into(), number: number.into(), aci, pni, password, registration_id, pni_registration_id,
        profile_key, pni_identity, store, sender_certificate: Some(cert), peers: vec![], device_id: 1,
    }
    .save()
    .await?;
    eprintln!("  saved {}", Account::path(name).display());
    Ok(())
}

/// Sealed-sender send from `from` to `to` over the unauthenticated socket with `to`'s access key.
async fn sealed_send(from: &mut Account, to: &Account, text: &str) -> R<u64> {
    sealed_send_content(from, to, text, false).await
}
async fn sealed_send_content(from: &mut Account, to: &Account, text: &str, with_profile_key: bool) -> R<u64> {
    let mut rng = rand::rng();
    let ts = now_ms();
    let cert = SenderCertificate::deserialize(from.sender_certificate.as_ref().ok_or("sender has no certificate")?)?;
    let profile = if with_profile_key { Some(from.profile_key.to_vec()) } else { None };
    let wire = sealed_sender_encrypt(&to.address(), &cert, &content_with(text, ts, profile),
        &mut from.store.session_store, &mut from.store.identity_store, SystemTime::now(), &mut rng).await?;
    let mut chat = Chat::connect(None)?;
    let body = json!({
        "messages": [{"type": 6, "destinationDeviceId": 1, "destinationRegistrationId": to.registration_id, "content": b64(&wire)}],
        "online": false, "urgent": true, "timestamp": ts,
    });
    chat.expect("PUT", &format!("/v1/messages/{}?story=false", to.aci),
        &[("unidentified-access-key", header_key(to))], Some(body), &[200])?;
    chat.close();
    Ok(ts)
}

/// Receive and decrypt sealed-sender messages for `me` on its authenticated socket.
async fn receive(me: &mut Account, expect: usize, timeout: Duration) -> R<Vec<(String, String, u64)>> {
    Ok(receive_envelopes(me, expect, timeout).await?.into_iter().map(|(f, t, ts, _)| (f, t, ts)).collect())
}

/// Like `receive`, also returning each envelope's source fields as JSON (they must be absent for
/// a sealed-sender message; present means the server treated the send as identified).
async fn receive_envelopes(me: &mut Account, expect: usize, timeout: Duration) -> R<Vec<(String, String, u64, Value)>> {
    let mut chat = Chat::connect(Some((&me.login(), &me.password.clone())))?;
    let pushed = chat.wait_messages(expect, timeout)?;
    chat.close();
    let root = PublicKey::deserialize(&unb64(TEST_TRUST_ROOT)?)?;
    let mut out = vec![];
    for p in pushed {
        let env = Envelope::decode(&p.body[..])?;
        // A sealed-sender envelope must NOT carry the sender's identity; if the server put it
        // there, the send was treated as identified (e.g. sent on an authenticated socket).
        eprintln!("  envelope type={:?} source_service_id={:?} source_device={:?}",
            env.r#type, env.source_service_id, env.source_device);
        if env.r#type != Some(6) {
            eprintln!("  skipping envelope type {:?}", env.r#type);
            continue;
        }
        let s = &mut me.store;
        let r = sealed_sender_decrypt(env.content.as_deref().unwrap_or_default(), &root, Timestamp::from_epoch_millis(now_ms()),
            None, me.aci.clone(), DeviceId::new(me.device_id)?, &mut s.identity_store, &mut s.session_store, &mut s.pre_key_store,
            &s.signed_pre_key_store, &mut s.kyber_pre_key_store).await?;
        let (text, ts) = parse_content(&r.message)?;
        eprintln!("  {} received from {}: {:?} (timestamp {ts}, server {:?})", me.name, r.sender_uuid, text, env.server_timestamp);
        let sender = r.sender_uuid.clone();
        me.add_peer(&sender);
        let envelope = json!({"type": env.r#type, "source_service_id": env.source_service_id,
            "source_device": env.source_device, "server_timestamp": env.server_timestamp});
        out.push((sender, text, ts, envelope));
    }
    me.save().await?;
    Ok(out)
}

/// Protobuf length-delimited field exactly as PublicRequest.field in PublicServiceController.lean.
fn pb_field(tag: u8, payload: &[u8]) -> Vec<u8> {
    let mut v = vec![tag];
    let mut n = payload.len() as u64;
    loop {
        let b = (n & 127) as u8;
        n >>= 7;
        if n == 0 {
            v.push(b);
            break;
        }
        v.push(b | 128);
    }
    v.extend_from_slice(payload);
    v
}
fn pb_varint(mut n: u64) -> Vec<u8> {
    let mut v = vec![];
    loop {
        let b = (n & 127) as u8;
        n >>= 7;
        if n == 0 {
            v.push(b);
            return v;
        }
        v.push(b | 128);
    }
}
/// Left-aligned decimal padded with spaces to `width` (HybridKernels.paddedDecimal).
fn padded(n: u64, width: usize) -> String {
    format!("{n:<width$}")
}

/// Send one sealed-sender text with the MPC client's exact request bytes
/// (PublicRequest.build): field order verb/path/body/id/headers, request id >= 2^63, space-padded
/// device and registration ids, on the AUTHENTICATED socket of the sender with the recipient's
/// Unidentified-Access-Key header. Prints the server's response and saves its raw bytes.
async fn mpc_send(from_name: &str, to_name: &str, text: &str) -> R<()> {
    let mut from = Account::load(from_name).await?;
    let to = Account::load(to_name).await?;
    let mut rng = rand::rng();
    let ts = now_ms();
    let cert = SenderCertificate::deserialize(from.sender_certificate.as_ref().ok_or("no certificate")?)?;
    let wire = sealed_sender_encrypt(&to.address(), &cert, &text_content(text, ts),
        &mut from.store.session_store, &mut from.store.identity_store, SystemTime::now(), &mut rng).await?;
    let json = format!(
        "{{\"messages\":[{{\"content\":\"{}\",\"destinationDeviceId\":{},\"destinationRegistrationId\":{},\"type\":6}}],\"online\":false,\"timestamp\":{},\"urgent\":true}}",
        b64(&wire), padded(1, 3), padded(to.registration_id as u64, 10), ts);
    let id: u64 = (1u64 << 63) + rng.random_range(0..1000u64);
    let mut request = pb_field(10, b"PUT");
    request.extend(pb_field(18, format!("/v1/messages/{}?story=false", to.aci).as_bytes()));
    request.extend(pb_field(26, json.as_bytes()));
    request.push(32);
    request.extend(pb_varint(id));
    request.extend(pb_field(42, b"content-type: application/json"));
    request.extend(pb_field(42, format!("unidentified-access-key: {}", b64(&to.access_key())).as_bytes()));
    let mut message = vec![8u8, 1];
    message.extend(pb_field(18, &request));

    let (aci, password) = (from.aci.clone(), from.password.clone());
    let mut chat = Chat::connect(Some((&aci, &password)))?;
    chat.ws.send(tungstenite::Message::Binary(message.clone().into()))?;
    let deadline = Instant::now() + Duration::from_secs(30);
    let mut response = None;
    while Instant::now() < deadline && response.is_none() {
        if let Some(r) = chat.poll()? {
            if r.id == Some(id) {
                response = Some(r);
            }
        }
    }
    let server_pushes: Vec<String> = chat.inbox.iter().map(|p| p.path.clone()).collect();
    let queue_empty_seen = chat.queue_empty;
    let raw = chat.last_response_raw.clone();
    chat.close();
    from.save().await?;
    let r = response.ok_or("no response")?;
    let dir = state_dir().join("../transcripts");
    std::fs::create_dir_all(&dir)?;
    std::fs::write(dir.join("mpc-send-request.bin"), &message)?;
    std::fs::write(dir.join("mpc-send-response.bin"), &raw)?;
    println!("{}", json!({
        "request_id": id.to_string(), "status": r.status, "message": r.message, "headers": r.headers,
        "body": r.body.as_ref().map(|b| String::from_utf8_lossy(b).to_string()),
        "queue_empty_seen": queue_empty_seen, "other_server_requests": server_pushes,
        "request_bytes": message.len(), "response_bytes": raw.len(), "timestamp": ts,
    }));
    Ok(())
}
/// A NEW user's first contact with `to`: register if needed, fetch `to`'s prekey bundle, and send
/// one sealed-sender PreKey message carrying `text` and the new user's profile key. Nothing is
/// received here: `to` is expected to be the MPC client.
static STRANGER: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
/// The Unidentified-Access-Key header for a send to `to`: its access key, or, from a stranger
/// that cannot know it, random bytes (accepted only if `to` allows unrestricted access).
fn header_key(to: &Account) -> String {
    if STRANGER.load(std::sync::atomic::Ordering::Relaxed) {
        b64(&rand::rng().random::<[u8; 16]>())
    } else {
        b64(&to.access_key())
    }
}
async fn signup(name: &str, number: &str, to_name: &str, text: &str) -> R<()> {
    // Always a fresh registration: an account file from an earlier server instance names an
    // account this server does not have.
    register(name, number).await?;
    // A stranger: it does not know the recipient's access key.
    STRANGER.store(true, std::sync::atomic::Ordering::Relaxed);
    let mut from = Account::load(name).await?;
    let to = Account::load(to_name).await?;
    start_session(&mut from, &to).await?;
    let ts = sealed_send_content(&mut from, &to, text, true).await?;
    from.save().await?;
    println!("{}", json!({"signup": name, "aci": from.aci, "to": to.aci, "timestamp": ts,
        "registration_id": from.registration_id, "access_key_hex": mpc::hex(&from.access_key())}));
    Ok(())
}

async fn establish(from_name: &str, to_name: &str) -> R<()> {
    eprintln!("establish {from_name} -> {to_name}");
    let mut from = Account::load(from_name).await?;
    let mut to = Account::load(to_name).await?;
    start_session(&mut from, &to).await?;

    sealed_send(&mut from, &to, "lss establish: hello").await?;
    from.save().await?;
    let got = receive(&mut to, 1, Duration::from_secs(15)).await?;
    if got.len() != 1 || got[0].0 != from.aci {
        return Err("recipient did not decrypt the PreKey message".into());
    }
    // Reply, so FROM's session is acknowledged (it then sends SignalMessages, not PreKey messages).
    sealed_send(&mut to, &from, "lss establish: reply").await?;
    to.save().await?;
    let got = receive(&mut from, 1, Duration::from_secs(15)).await?;
    if got.len() != 1 || got[0].0 != to.aci {
        return Err("sender did not decrypt the reply".into());
    }
    let s = from.store.load_session(&to.address()).await?.ok_or("no session")?;
    eprintln!("  {} -> {} session established (has_usable_sender_chain={})", from_name, to_name,
        s.has_usable_sender_chain(SystemTime::now(), SessionUsabilityRequirements::all())?);
    Ok(())
}

/// FROM fetches TO's prekey bundle and starts a session from it (no message is sent).
async fn start_session(from: &mut Account, to: &Account) -> R<()> {
    let mut rng = rand::rng();

    // Fetch TO's prekey bundle with TO's access key (unauthenticated socket, like a sealed-sender client).
    let mut chat = Chat::connect(None)?;
    let keys = chat.expect("GET", &format!("/v2/keys/{}/1", to.aci), &[("unidentified-access-key", header_key(to))], None, &[200])?;
    chat.close();
    let d = &keys["devices"][0];
    let pre = &d["preKey"];
    let pre_key = if pre.is_object() {
        Some((PreKeyId::from(pre["keyId"].as_u64().unwrap() as u32), PublicKey::deserialize(&unb64(pre["publicKey"].as_str().unwrap())?)?))
    } else {
        None
    };
    let spk = &d["signedPreKey"];
    let pq = &d["pqPreKey"];
    let bundle = PreKeyBundle::new(
        d["registrationId"].as_u64().ok_or("registrationId")? as u32,
        DeviceId::new(d["deviceId"].as_u64().ok_or("deviceId")? as u8)?,
        pre_key,
        (spk["keyId"].as_u64().unwrap() as u32).into(),
        PublicKey::deserialize(&unb64(spk["publicKey"].as_str().unwrap())?)?,
        unb64(spk["signature"].as_str().unwrap())?,
        (pq["keyId"].as_u64().unwrap() as u32).into(),
        kem::PublicKey::deserialize(&unb64(pq["publicKey"].as_str().unwrap())?)?,
        unb64(pq["signature"].as_str().unwrap())?,
        IdentityKey::decode(&unb64(keys["identityKey"].as_str().ok_or("identityKey")?)?)?,
    )?;
    process_prekey_bundle(&to.address(), &from.address(), &mut from.store.session_store, &mut from.store.identity_store,
        &bundle, SystemTime::now(), &mut rng).await?;
    from.add_peer(&to.aci.clone());
    Ok(())
}

/// Link a further device to `name`'s account, as a new client does after scanning the primary's
/// code: the primary asks the server for a linking token (`GET /v1/devices/provisioning/code`),
/// and the new device registers itself (`PUT /v1/devices/link`) with its own password,
/// registration ids, signed prekey and Kyber last-resort key, signed with the account's identity
/// keys (which a real primary sends it in the provisioning message). `one_time` one-time EC
/// prekeys are uploaded for it (0: its bundle then has `"preKey":null`).
/// The device is saved as account `<name>.<device id>` and receives with `receive <name>.<id>`.
async fn link(name: &str, one_time: u32) -> R<()> {
    let primary = Account::load(name).await?;
    let mut rng = rand::rng();
    let identity = primary.store.get_identity_key_pair().await?;
    let registration_id = rng.random_range(1..=0x3fff_u32);
    let pni_registration_id = rng.random_range(1..=0x3fff_u32);
    const ALPHABET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    let password: String = (0..PASSWORD_LEN).map(|_| ALPHABET[rng.random_range(0..ALPHABET.len())] as char).collect();
    let key_id = rng.random_range(2..0x00ff_ffff_u32);
    let aci_spk = signed_prekey(&identity, key_id, &mut rng)?;
    let pni_spk = signed_prekey(&primary.pni_identity, key_id, &mut rng)?;
    let aci_kyber = kyber_prekey(&identity, key_id)?;
    let pni_kyber = kyber_prekey(&primary.pni_identity, key_id)?;

    let mut chat = Chat::connect(Some((&primary.login(), &primary.password)))?;
    let token = chat.expect("GET", "/v1/devices/provisioning/code", &[], None, &[200])?;
    chat.close();
    let code = token["verificationCode"].as_str().ok_or("no linking token")?.to_string();
    let auth = format!("Basic {}", b64(format!("{}:{password}", primary.number).as_bytes()));
    let body = json!({
        "verificationCode": code,
        "accountAttributes": {
            "fetchesMessages": true,
            "registrationId": registration_id,
            "pniRegistrationId": pni_registration_id,
            "capabilities": {"spqr": true},
        },
        "aciSignedPreKey": ec_signed_json(&aci_spk)?,
        "pniSignedPreKey": ec_signed_json(&pni_spk)?,
        "aciPqLastResortPreKey": kem_signed_json(&aci_kyber)?,
        "pniPqLastResortPreKey": kem_signed_json(&pni_kyber)?,
    });
    let mut chat = Chat::connect(None)?;
    let linked = chat.expect("PUT", "/v1/devices/link", &[("authorization", auth)], Some(body), &[200])?;
    chat.close();
    let device_id = linked["deviceId"].as_u64().ok_or("no device id")? as u8;

    let mut store = InMemSignalProtocolStore::new(identity, registration_id)?;
    store.save_signed_pre_key(key_id.into(), &aci_spk).await?;
    store.save_kyber_pre_key(key_id.into(), &aci_kyber).await?;
    let device = Account {
        name: format!("{name}.{device_id}"), number: primary.number.clone(), aci: primary.aci.clone(), pni: primary.pni.clone(),
        password, registration_id, pni_registration_id, profile_key: primary.profile_key, pni_identity: primary.pni_identity,
        store, sender_certificate: None, peers: vec![], device_id,
    };
    let mut device = device;
    if one_time > 0 {
        let mut prekeys = vec![];
        for i in 0..one_time {
            let pid = 1000 * device_id as u32 + i;
            let pair = KeyPair::generate(&mut rng);
            device.store.save_pre_key(pid.into(), &PreKeyRecord::new(pid.into(), &pair)).await?;
            prekeys.push(json!({"keyId": pid, "publicKey": b64(&pair.public_key.serialize())}));
        }
        let mut chat = Chat::connect(Some((&device.login(), &device.password)))?;
        chat.expect("PUT", "/v2/keys?identity=aci", &[], Some(json!({"preKeys": prekeys, "pqPreKeys": []})), &[200, 204])?;
        chat.close();
    }
    device.save().await?;
    println!("{}", json!({"linked": device.name, "aci": device.aci, "device_id": device_id, "registration_id": registration_id,
        "signed_prekey_id": key_id, "one_time_prekeys": one_time}));
    Ok(())
}

// ---- Fault injection for the MPC client's recovery tests (check_signal_service_local.py). Each
// changes a test account on the LOCAL server the way a real user's client can.

/// The user registers again (new phone, reinstall): the same number and account id, a NEW
/// identity key, registration id and prekeys; linked devices are gone. The profile key is kept,
/// so the access key its contacts hold still works. The saved account is replaced.
async fn reregister(name: &str) -> R<()> {
    let old = Account::load(name).await?;
    register_full(name, &old.number, false, Some(old.profile_key)).await?;
    let new = Account::load(name).await?;
    if new.aci != old.aci {
        return Err(format!("the account id changed on registering again: {} -> {}", old.aci, new.aci).into());
    }
    println!("{}", json!({"reregistered": name, "aci": new.aci, "registration_id": new.registration_id,
        "identity_changed": new.store.get_identity_key_pair().await?.identity_key().serialize()
            != old.store.get_identity_key_pair().await?.identity_key().serialize()}));
    Ok(())
}

/// The primary removes a linked device (`DELETE /v1/devices/{id}`).
async fn unlink(name: &str, device: u8) -> R<()> {
    let primary = Account::load(name).await?;
    let mut chat = Chat::connect(Some((&primary.login(), &primary.password)))?;
    let (status, _) = chat.request("DELETE", &format!("/v1/devices/{device}"), &[], None)?;
    chat.close();
    if status != 200 && status != 204 {
        return Err(format!("DELETE /v1/devices/{device}: status {status}").into());
    }
    println!("{}", json!({"unlinked": format!("{name}.{device}"), "status": status}));
    Ok(())
}

/// The user deletes the account (`DELETE /v1/accounts/me`).
async fn delete_account(name: &str) -> R<()> {
    let me = Account::load(name).await?;
    let mut chat = Chat::connect(Some((&me.login(), &me.password)))?;
    let (status, _) = chat.request("DELETE", "/v1/accounts/me", &[], None)?;
    chat.close();
    if status != 200 && status != 204 {
        return Err(format!("DELETE /v1/accounts/me: status {status}").into());
    }
    println!("{}", json!({"deleted": name, "aci": me.aci, "status": status}));
    Ok(())
}

/// The user's profile key changes (Signal clients rotate it, for example on blocking someone):
/// the account's access key becomes the new key's, so sealed sends under the old one get 401.
async fn rotate_access(name: &str) -> R<()> {
    let mut me = Account::load(name).await?;
    let mut rng = rand::rng();
    me.profile_key = rng.random();
    let body = json!({
        "fetchesMessages": true,
        "registrationId": me.registration_id,
        "pniRegistrationId": me.pni_registration_id,
        "capabilities": {"spqr": true},
        "unidentifiedAccessKey": b64(&me.access_key()),
        "unrestrictedUnidentifiedAccess": false,
        "discoverableByPhoneNumber": false,
    });
    let mut chat = Chat::connect(Some((&me.login(), &me.password)))?;
    let (status, _) = chat.request("PUT", "/v1/accounts/attributes", &[], Some(body))?;
    chat.close();
    if status != 200 && status != 204 {
        return Err(format!("PUT /v1/accounts/attributes: status {status}").into());
    }
    me.save().await?;
    println!("{}", json!({"rotated": name, "status": status}));
    Ok(())
}

/// The raw body of `GET /v2/keys/{aci}/*` for `name`'s account (every device's bundle), fetched
/// as a sealed-sender client does: unauthenticated socket, the account's access key. Written to
/// `out` exactly as the server sent it. (Each fetch uses up one one-time prekey per device.)
async fn keys_dump(name: &str, out: &str) -> R<()> {
    let to = Account::load(name).await?;
    let mut chat = Chat::connect(None)?;
    let (status, body) = chat.request("GET", &format!("/v2/keys/{}/*", to.aci), &[("unidentified-access-key", b64(&to.access_key()))], None)?;
    let raw = chat.last_response_raw.clone();
    chat.close();
    if status != 200 {
        return Err(format!("GET /v2/keys: status {status}").into());
    }
    std::fs::write(out, &body)?;
    std::fs::write(format!("{out}.message"), &raw)?;
    println!("{}", json!({"status": status, "body_bytes": body.len(), "message_bytes": raw.len(), "out": out}));
    Ok(())
}

async fn run(args: &[String]) -> R<()> {
    let a: Vec<&str> = args.iter().map(String::as_str).collect();
    match a.as_slice() {
        ["link", name] => link(name, 0).await,
        ["link", name, count] => link(name, count.parse()?).await,
        ["keys-dump", name, out] => keys_dump(name, out).await,
        ["reregister", name] => reregister(name).await,
        ["unlink", name, device] => unlink(name, device.parse()?).await,
        ["delete", name] => delete_account(name).await,
        ["rotate-access", name] => rotate_access(name).await,
        ["register", name, number] => register(name, number).await,
        ["establish", from, to] => establish(from, to).await,
        ["send", from, to, text] => {
            let mut f = Account::load(from).await?;
            let t = Account::load(to).await?;
            let ts = sealed_send(&mut f, &t, text).await?;
            f.save().await?;
            println!("{}", json!({"sent": true, "timestamp": ts}));
            Ok(())
        }
        ["mpc-send", from, to, text] => mpc_send(from, to, text).await,
        ["signup", name, number, to, text] => signup(name, number, to, text).await,
        ["kem-decapsulate", key, ciphertext] => mpc::kem_decapsulate(key, ciphertext),
        ["export-mpc"] => mpc::export_mpc("sender", &["recipient", "recipient2"]).await,
        ["export-mpc", sender, contacts @ ..] => mpc::export_mpc(sender, contacts).await,
        ["ref-send", text] => mpc::ref_send(text, None).await,
        ["ref-send", text, dir] => mpc::ref_send(text, Some(dir)).await,
        ["probe-sockets", dir, rest @ ..] => {
            let idle = rest.first().map(|s| s.parse()).transpose()?.unwrap_or(5);
            mpc::probe_sockets(dir, idle).await
        }
        ["receive", name, rest @ ..] => {
            let secs = rest.first().map(|s| s.parse()).transpose()?.unwrap_or(10);
            let mut me = Account::load(name).await?;
            let got = receive_envelopes(&mut me, usize::MAX, Duration::from_secs(secs)).await?;
            for (from, text, ts, envelope) in got {
                println!("{}", json!({"from": from, "text": text, "timestamp": ts, "envelope": envelope}));
            }
            Ok(())
        }
        ["show", name] => {
            let me = Account::load(name).await?;
            println!("{}", json!({"name": me.name, "number": me.number, "aci": me.aci, "pni": me.pni, "device_id": 1,
                "registration_id": me.registration_id, "access_key": b64(&me.access_key()), "peers": me.peers,
                "password_len": me.password.len(), "has_sender_certificate": me.sender_certificate.is_some()}));
            Ok(())
        }
        ["provision"] => {
            // Fictional NANP numbers (555-01xx); the local stub registration service sends nothing.
            register_with("sender", "+12025550101", true).await?;
            register("recipient", "+12025550102").await?;
            register("recipient2", "+12025550103").await?;
            establish("sender", "recipient").await?;
            establish("sender", "recipient2").await?;
            let mut s = Account::load("sender").await?;
            let r = Account::load("recipient").await?;
            let ts = sealed_send(&mut s, &r, "lss provision: established send").await?;
            s.save().await?;
            let mut r = Account::load("recipient").await?;
            let got = receive(&mut r, 1, Duration::from_secs(15)).await?;
            if got.len() != 1 || got[0].1 != "lss provision: established send" || got[0].2 != ts {
                return Err("established send was not received intact".into());
            }
            let r2 = Account::load("recipient2").await?;
            println!("{}", json!({"provisioned": true, "sender": s.aci, "recipient": r.aci, "recipient2": r2.aci}));
            Ok(())
        }
        _ => Err("usage: lss-provision register NAME NUMBER | establish FROM TO | send FROM TO TEXT | mpc-send FROM TO TEXT | receive NAME [SECONDS] | link NAME [ONE_TIME] | keys-dump NAME OUT | show NAME | provision | export-mpc [SENDER CONTACT..] | ref-send TEXT | probe-sockets DIR [IDLE_SECS]".into()),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let rt = tokio::runtime::Builder::new_current_thread().build().unwrap();
    if let Err(e) = rt.block_on(run(&args)) {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}
