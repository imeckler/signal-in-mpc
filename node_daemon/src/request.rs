//! The application's signed requests: the exact bytes the database nodes verify. Pure.

use crate::sha256;
use ed25519_dalek::{Signature, VerifyingKey};
use serde_json::{Value, json};

/// The account's own row on the database nodes; no request may list it (`handoff::ACCOUNT_ID`).
pub const ACCOUNT_ID: u128 = u128::MAX - 1;
/// `handoff::MAX_NOTIFY_IDS`.
pub const MAX_IDS: usize = 100_000;
/// `handoff::MAX_CLOCK_SKEW_SECS`.
pub const MAX_CLOCK_SKEW_SECS: u64 = 30;

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::public_key;

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
}
