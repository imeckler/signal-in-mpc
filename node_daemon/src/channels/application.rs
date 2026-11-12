//! The application's channel: the listener on `listen` (localhost, or the node's WireGuard
//! address: an address only the application server reaches), what it may ask, and what it gets.
//!
//! `notify` and `delete` carry the application's signed request (checked by the scheduler exactly
//! as the database nodes check it). `wait`, `events` and `status` are unauthenticated by default:
//! what they return is public to the nodes, and only the application reaches the listener. When
//! the configuration names `application.token_file`, every request must also carry
//! `"bearer": TOKEN`, compared in constant time; any other request is refused.

use super::Listener;
use crate::constant_time_eq;
use serde_json::{Value, json};
use std::sync::Arc;

/// Everything the application can ask a daemon.
#[derive(Clone, Debug, PartialEq)]
pub enum AppRequest {
    /// `{"op":"notify","message":TEXT,"request":R}`.
    Notify { request: Value, message: Option<String> },
    /// `{"op":"delete","request":D}`.
    Delete { request: Value },
    /// `{"op":"wait","job":DIGEST,"timeout":SECONDS}`.
    Wait { job: String, timeout: u64 },
    /// `{"op":"events","after":N,"wait":SECONDS}`.
    Events { after: u64, wait: u64 },
    /// `{"op":"status"}`.
    Status,
}

impl AppRequest {
    pub fn decode(message: &Value) -> Result<AppRequest, String> {
        let number = |name: &str| message.get(name).and_then(Value::as_u64).unwrap_or(0);
        match message.get("op").and_then(Value::as_str).unwrap_or("") {
            "notify" => Ok(AppRequest::Notify {
                request: message.get("request").cloned().unwrap_or(Value::Null),
                message: message.get("message").and_then(Value::as_str).map(str::to_string),
            }),
            "delete" => Ok(AppRequest::Delete { request: message.get("request").cloned().unwrap_or(Value::Null) }),
            "wait" => match message.get("job").and_then(Value::as_str) {
                Some(job) => Ok(AppRequest::Wait { job: job.to_string(), timeout: number("timeout") }),
                None => Err("wait: job is missing".into()),
            },
            "events" => Ok(AppRequest::Events { after: number("after"), wait: number("wait") }),
            "status" => Ok(AppRequest::Status),
            _ => Err("unknown request".into()),
        }
    }

    /// The request on the wire (the application's side; `notify-app` and tests).
    pub fn encode(&self) -> Value {
        match self {
            AppRequest::Notify { request, message: Some(message) } => json!({"op": "notify", "request": request, "message": message}),
            AppRequest::Notify { request, message: None } => json!({"op": "notify", "request": request}),
            AppRequest::Delete { request } => json!({"op": "delete", "request": request}),
            AppRequest::Wait { job, timeout } => json!({"op": "wait", "job": job, "timeout": timeout}),
            AppRequest::Events { after, wait } => json!({"op": "events", "after": after, "wait": wait}),
            AppRequest::Status => json!({"op": "status"}),
        }
    }
}

/// This node's long-lived send session, as `status` reports it.
#[derive(Clone, Debug, PartialEq)]
pub struct SendStatus {
    pub pid: Option<u32>,
    pub ready: bool,
    pub serving: bool,
    pub messages: u64,
    pub jobs: u64,
    pub seconds: u64,
    pub megabytes: u64,
    pub ending: Option<String>,
}

/// The reply to `status`.
#[derive(Clone, Debug, PartialEq)]
pub struct Status {
    pub party: u8,
    pub received: usize,
    pub agreed: usize,
    pub running: usize,
    pub done: usize,
    pub events: usize,
    pub receive_session_running: bool,
    pub receive_sessions_started: u64,
    pub send_sessions_started: u64,
    pub send_session: Option<SendStatus>,
}

/// Everything a daemon answers the application.
#[derive(Clone, Debug, PartialEq)]
pub enum AppReply {
    /// `{"ok":false,"error":…}`.
    Refused(String),
    /// A notify or delete taken: `{"ok":true,"job","state"[,"known":true]}` (`known`: the same
    /// signed request was already held).
    Accepted { job: String, state: &'static str, known: bool },
    /// `wait` on a finished job: `{"ok":true,"job","state":"done","result"}`.
    Done { job: String, result: Option<Value> },
    /// `wait` that timed out first: `{"ok":true,"job","state"}`.
    Pending { job: String, state: &'static str },
    /// `{"ok":true,"events":[…],"next":N}`.
    Events { events: Vec<Value>, next: usize },
    Status(Status),
}

impl AppReply {
    pub fn encode(&self) -> Value {
        match self {
            AppReply::Refused(why) => json!({"ok": false, "error": why}),
            AppReply::Accepted { job, state, known: false } => json!({"ok": true, "job": job, "state": state}),
            AppReply::Accepted { job, state, known: true } => json!({"ok": true, "job": job, "state": state, "known": true}),
            AppReply::Done { job, result } => json!({"ok": true, "job": job, "state": "done", "result": result}),
            AppReply::Pending { job, state } => json!({"ok": true, "job": job, "state": state}),
            AppReply::Events { events, next } => json!({"ok": true, "events": events, "next": next}),
            AppReply::Status(s) => json!({"ok": true, "party": s.party, "received": s.received, "agreed": s.agreed, "running": s.running,
                "done": s.done, "events": s.events, "receive_session_running": s.receive_session_running,
                "receive_sessions_started": s.receive_sessions_started, "send_sessions_started": s.send_sessions_started,
                "send_session": s.send_session.as_ref().map(|s| json!({"pid": s.pid, "ready": s.ready, "serving": s.serving, "messages": s.messages,
                    "jobs": s.jobs, "seconds": s.seconds, "megabytes": s.megabytes, "ending": s.ending}))}),
        }
    }
}

/// The bearer check: without a configured token every request passes; with one, only a request
/// carrying the same token (`"bearer"`), compared in constant time.
pub fn authorised(bearer: Option<&[u8]>, message: &Value) -> bool {
    match bearer {
        None => true,
        Some(token) => message.get("bearer").and_then(Value::as_str).is_some_and(|given| constant_time_eq(given.as_bytes(), token)),
    }
}

/// Answer the application on `listener` (`listen`).
pub fn serve(listener: Listener, bearer: Option<Vec<u8>>, handle: impl Fn(AppRequest) -> AppReply + Send + Sync + 'static) {
    listener.serve(Arc::new(move |message: Value| {
        if !authorised(bearer.as_deref(), &message) {
            return AppReply::Refused("not authorised".into()).encode();
        }
        match AppRequest::decode(&message) {
            Ok(request) => handle(request).encode(),
            Err(why) => AppReply::Refused(why).encode(),
        }
    }));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn requests_on_the_wire() {
        let request = json!({"ids": ["1"], "nonce": "00"});
        for (decoded, wire) in [
            (AppRequest::Notify { request: request.clone(), message: Some("hi".into()) }, json!({"op": "notify", "request": request, "message": "hi"})),
            (AppRequest::Delete { request: request.clone() }, json!({"op": "delete", "request": request})),
            (AppRequest::Wait { job: "ab".into(), timeout: 9 }, json!({"op": "wait", "job": "ab", "timeout": 9})),
            (AppRequest::Events { after: 3, wait: 5 }, json!({"op": "events", "after": 3, "wait": 5})),
            (AppRequest::Status, json!({"op": "status"})),
        ] {
            assert_eq!(decoded.encode(), wire);
            assert_eq!(AppRequest::decode(&wire), Ok(decoded));
        }
        // Defaults and refusals as before the types.
        assert_eq!(AppRequest::decode(&json!({"op": "wait", "job": "ab"})), Ok(AppRequest::Wait { job: "ab".into(), timeout: 0 }));
        assert_eq!(AppRequest::decode(&json!({"op": "events"})), Ok(AppRequest::Events { after: 0, wait: 0 }));
        assert_eq!(AppRequest::decode(&json!({"op": "notify"})), Ok(AppRequest::Notify { request: Value::Null, message: None }));
        assert_eq!(AppRequest::decode(&json!({"op": "wait"})), Err("wait: job is missing".into()));
        assert_eq!(AppRequest::decode(&json!({"op": "peer-ping"})), Err("unknown request".into()));
        assert_eq!(AppRequest::decode(&json!({})), Err("unknown request".into()));
    }

    #[test]
    fn replies_on_the_wire() {
        assert_eq!(AppReply::Refused("x".into()).encode(), json!({"ok": false, "error": "x"}));
        assert_eq!(AppReply::Accepted { job: "j".into(), state: "received", known: false }.encode(), json!({"ok": true, "job": "j", "state": "received"}));
        assert_eq!(AppReply::Accepted { job: "j".into(), state: "agreed", known: true }.encode(), json!({"ok": true, "job": "j", "state": "agreed", "known": true}));
        assert_eq!(AppReply::Done { job: "j".into(), result: None }.encode(), json!({"ok": true, "job": "j", "state": "done", "result": null}));
        assert_eq!(AppReply::Pending { job: "j".into(), state: "running" }.encode(), json!({"ok": true, "job": "j", "state": "running"}));
        assert_eq!(AppReply::Events { events: vec![json!({"seq": 1})], next: 1 }.encode(), json!({"ok": true, "events": [{"seq": 1}], "next": 1}));
        let status = Status { party: 1, received: 0, agreed: 1, running: 0, done: 2, events: 3, receive_session_running: true,
            receive_sessions_started: 1, send_sessions_started: 2, send_session: None };
        assert_eq!(AppReply::Status(status.clone()).encode(), json!({"ok": true, "party": 1, "received": 0, "agreed": 1, "running": 0, "done": 2,
            "events": 3, "receive_session_running": true, "receive_sessions_started": 1, "send_sessions_started": 2, "send_session": null}));
        let serving = Status { send_session: Some(SendStatus { pid: Some(7), ready: true, serving: false, messages: 4, jobs: 2, seconds: 9,
            megabytes: 0, ending: None }), ..status };
        assert_eq!(AppReply::Status(serving).encode()["send_session"], json!({"pid": 7, "ready": true, "serving": false, "messages": 4,
            "jobs": 2, "seconds": 9, "megabytes": 0, "ending": null}));
    }

    #[test]
    fn bearer_token() {
        let status = json!({"op": "status"});
        assert!(authorised(None, &status));
        assert!(!authorised(Some(b"0123456789abcdef"), &status));
        assert!(!authorised(Some(b"0123456789abcdef"), &json!({"op": "status", "bearer": "0123456789abcdeX"})));
        assert!(!authorised(Some(b"0123456789abcdef"), &json!({"op": "status", "bearer": "0123456789abcdef0"})));
        assert!(!authorised(Some(b"0123456789abcdef"), &json!({"op": "status", "bearer": 5})));
        assert!(authorised(Some(b"0123456789abcdef"), &json!({"op": "status", "bearer": "0123456789abcdef"})));
    }

    /// Over a loopback socket, with and without a token.
    #[test]
    fn listener_end_to_end() {
        use std::time::Duration;
        for bearer in [None, Some(b"0123456789abcdef".to_vec())] {
            let listener = Listener::bind("127.0.0.1:0").unwrap();
            let address = listener.address();
            serve(listener, bearer.clone(), |request| match request {
                AppRequest::Status => AppReply::Pending { job: "status".into(), state: "x" },
                _ => AppReply::Refused("other".into()),
            });
            let ask = |message: Value| super::super::call(&address, &message, Duration::from_secs(5)).unwrap();
            let with = json!({"op": "status", "bearer": "0123456789abcdef"});
            assert_eq!(ask(with)["job"], json!("status"));
            let without = ask(json!({"op": "status"}));
            if bearer.is_some() {
                assert_eq!(without, json!({"ok": false, "error": "not authorised"}));
            } else {
                assert_eq!(without["job"], json!("status"));
            }
            assert_eq!(ask(json!({"op": "nothing", "bearer": "0123456789abcdef"})), json!({"ok": false, "error": "unknown request"}));
        }
    }
}
