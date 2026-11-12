//! The node's configuration (README, "Configuration"). Parsed here; its files are read through
//! `channels::disk::read_setup`.

use crate::channels::controller::SessionEnv;
use crate::channels::disk::read_setup;
use crate::public_key;
use serde_json::Value;
use std::path::PathBuf;

pub struct Config {
    pub party: u8,
    /// The application's listener: localhost, or the node's WireGuard address (an address only
    /// the application reaches). Never a wildcard address unless a bearer token is set.
    pub listen: String,
    /// The other daemon's listener, separate from the application's (peer messages only).
    pub peer_listen: String,
    pub peer: String,
    pub peer_key: Vec<u8>,
    /// Optional (`application.token_file`): every application request must carry it.
    pub bearer: Option<Vec<u8>>,
    pub state: PathBuf,
    /// What every controller is started with.
    pub session: SessionEnv,
    pub port_base: u64,
    pub notify_key: [u8; 32],
    pub max_age: u64,
    pub receive: bool,
    pub agree_seconds: u64,
    pub start_margin_seconds: u64,
    pub send_seconds: u64,
    pub send_seconds_per_id: u64,
    pub delete_seconds: u64,
    /// The long-lived send session (README, "The long-lived send session"); `false`: one session per notify, as before.
    pub long_lived: bool,
    /// When a long-lived session is ended (between jobs) and a new one started: after this many
    /// messages, this many seconds, or this much resident memory of its process tree (0: no limit).
    pub max_messages: u64,
    pub max_seconds: u64,
    pub max_megabytes: u64,
    /// A send session whose log has not grown for this long is stopped (its worker logs every
    /// operation, and an idle session ticks every quarter second).
    pub stall_seconds: u64,
    /// Sessions a notify may be handed to (a session that dies with it is followed by another, which resumes from the journals).
    pub attempts: u32,
}

/// Ports a node pair's sessions use above `worker.port_base`: send sessions at +0..+280, receive
/// sessions at +320..+600, each with room for 40.
pub const PORT_SPAN: u64 = 640;

fn text(value: &Value, path: &[&str]) -> Result<String, String> {
    optional(value, path).ok_or(format!("config: {} is required", path.join(".")))
}

fn optional(value: &Value, path: &[&str]) -> Option<String> {
    let mut at = value;
    for name in path {
        at = at.get(name)?;
    }
    at.as_str().map(str::to_string)
}

fn number(value: &Value, path: &[&str], default: u64) -> u64 {
    let mut at = value;
    for name in path {
        match at.get(name) {
            Some(next) => at = next,
            None => return default,
        }
    }
    at.as_u64().unwrap_or(default)
}

/// `0.0.0.0:P`, `[::]:P`, `:P`: every interface of the machine.
fn wildcard(address: &str) -> bool {
    let host = address.rsplit_once(':').map(|(host, _)| host).unwrap_or(address);
    matches!(host, "" | "0.0.0.0" | "[::]" | "::" | "*" | "[::0]")
}

impl Config {
    pub fn load(path: &str) -> Result<Config, String> {
        Config::from_files(path, &read_setup)
    }

    /// `read`: the configuration file and the files it names, by path.
    pub fn from_files(path: &str, read: &dyn Fn(&str) -> Result<String, String>) -> Result<Config, String> {
        let c: Value = serde_json::from_str(&read(path)?).map_err(|e| format!("{path}: {e}"))?;
        let party = number(&c, &["party"], 2);
        if party > 1 {
            return Err("config: party must be 0 or 1".into());
        }
        let db_network = text(&c, &["database", "network"])?;
        let network: Value = serde_json::from_str(&read(&db_network)?).map_err(|e| format!("{db_network}: {e}"))?;
        // The application's notify key: the one the database nodes are configured with, unless
        // the node's configuration pins it (then the two must be equal).
        let from_network = optional(&network, &["notify_public_key"]);
        let pinned = optional(&c, &["application", "notify_public_key"]);
        let notify_key = match (&pinned, &from_network) {
            (Some(a), Some(b)) if a.trim() != b.trim() => return Err("config: application.notify_public_key differs from the database network's".into()),
            (Some(a), _) => public_key(a)?,
            (None, Some(b)) => public_key(b)?,
            (None, None) => return Err("config: no notify public key (application.notify_public_key or the database network config)".into()),
        };
        let hosts: Vec<String> = c.get("worker").and_then(|w| w.get("hosts")).and_then(Value::as_array)
            .map(|list| list.iter().filter_map(|h| h.as_str().map(str::to_string)).collect()).unwrap_or_default();
        if hosts.len() != 2 {
            return Err("config: worker.hosts must name the two nodes".into());
        }
        let key_file = text(&c, &["peer_key_file"])?;
        let peer_key = hex::decode(read(&key_file)?.trim()).map_err(|_| format!("{key_file}: not hex"))?;
        if peer_key.len() < 16 {
            return Err(format!("{key_file}: the peer key must be at least 16 bytes"));
        }
        let bearer = match optional(&c, &["application", "token_file"]) {
            None => None,
            Some(file) => {
                let token = read(&file)?.trim().as_bytes().to_vec();
                if token.len() < 16 {
                    return Err(format!("{file}: the bearer token must be at least 16 bytes"));
                }
                Some(token)
            }
        };
        let (listen, peer_listen) = (text(&c, &["listen"])?, text(&c, &["peer_listen"])?);
        if listen == peer_listen {
            return Err("config: peer_listen must differ from listen (the application and the other daemon have separate listeners)".into());
        }
        if wildcard(&listen) && bearer.is_none() {
            return Err("config: listen must be localhost or the node's WireGuard address, not every interface (or set application.token_file)".into());
        }
        let port_base = number(&c, &["worker", "port_base"], 22400);
        if port_base + PORT_SPAN > 65536 {
            return Err(format!("config: worker.port_base must leave {PORT_SPAN} ports below 65536"));
        }
        let environment = c.get("environment").and_then(Value::as_object)
            .map(|o| o.iter().filter_map(|(k, v)| v.as_str().map(|v| (k.clone(), v.to_string()))).collect()).unwrap_or_default();
        Ok(Config {
            party: party as u8,
            listen,
            peer_listen,
            peer: text(&c, &["peer"])?,
            peer_key,
            bearer,
            state: PathBuf::from(text(&c, &["state_directory"])?),
            session: SessionEnv {
                controller: text(&c, &["controller"])?,
                worker: text(&c, &["worker", "binary"])?,
                send_directory: text(&c, &["worker", "send_directory"])?,
                receive_directory: text(&c, &["worker", "receive_directory"])?,
                party: party as u8,
                hosts,
                circuit_tool: text(&c, &["circuits", "tool"])?,
                circuit_manifest: optional(&c, &["circuits", "manifest"]),
                endpoint: text(&c, &["signal", "endpoint"])?,
                signal_port: number(&c, &["signal", "port"], 443),
                hostname: text(&c, &["signal", "hostname"])?,
                trust_root: text(&c, &["signal", "trust_root"])?,
                certificate_checker: text(&c, &["signal", "certificate_checker"])?,
                socks: optional(&c, &["proxy", "socks"]),
                circuits: c.get("proxy").and_then(|p| p.get("circuits")).and_then(Value::as_u64),
                db_client: text(&c, &["database", "client"])?,
                db_network,
                db_key: text(&c, &["database", "key"])?,
                export: optional(&c, &["test", "export"]),
                tokens: optional(&c, &["test", "tokens"]),
                kem_tool: optional(&c, &["test", "kem_tool"]),
                environment,
                peer_wait_seconds: number(&c, &["timeouts", "peer_wait_seconds"], 180),
            },
            port_base,
            notify_key,
            max_age: number(&network, &["notify_max_age_secs"], 120),
            receive: c.get("receive").and_then(Value::as_bool).unwrap_or(true),
            agree_seconds: number(&c, &["timeouts", "agree_seconds"], 30),
            start_margin_seconds: number(&c, &["timeouts", "start_margin_seconds"], 30),
            send_seconds: number(&c, &["timeouts", "send_seconds"], 600),
            send_seconds_per_id: number(&c, &["timeouts", "send_seconds_per_id"], 60),
            delete_seconds: number(&c, &["timeouts", "delete_seconds"], 120),
            long_lived: c.get("send_session").and_then(|s| s.get("long_lived")).and_then(Value::as_bool).unwrap_or(true),
            max_messages: number(&c, &["send_session", "max_messages"], 5000),
            max_seconds: number(&c, &["send_session", "max_seconds"], 6 * 3600),
            max_megabytes: number(&c, &["send_session", "max_megabytes"], 0),
            stall_seconds: number(&c, &["send_session", "stall_seconds"], 900),
            attempts: number(&c, &["send_session", "attempts"], 3).clamp(1, 10) as u32,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn files(config: Value) -> impl Fn(&str) -> Result<String, String> {
        move |path: &str| match path {
            "node.json" => Ok(config.to_string()),
            "network.json" => Ok(json!({"notify_public_key": "xtRBqabaPZLqaUJuWOWU4aZqI9dnHm+CxEbQOK4sSE8="}).to_string()),
            "peer.key" => Ok("00112233445566778899aabbccddeeff\n".into()),
            "token" => Ok("0123456789abcdef0123\n".into()),
            "short-token" => Ok("abc".into()),
            other => Err(format!("{other}: no such file")),
        }
    }

    fn base() -> Value {
        json!({"party": 1, "listen": "127.0.0.1:19700", "peer_listen": "10.0.0.2:19710", "peer": "10.0.0.1:19710", "peer_key_file": "peer.key",
            "state_directory": "state", "controller": "c", "worker": {"binary": "w", "send_directory": "s", "receive_directory": "r",
            "hosts": ["10.0.0.1", "10.0.0.2"]}, "circuits": {"tool": "t"}, "signal": {"endpoint": "e", "hostname": "h", "trust_root": "ca",
            "certificate_checker": "cc"}, "database": {"client": "d", "network": "network.json", "key": "k"}})
    }

    fn load(config: Value) -> Result<Config, String> {
        Config::from_files("node.json", &files(config))
    }

    /// (`Config` has no `Debug`: it holds the peer key and the bearer token.)
    fn refusal(config: Value) -> String {
        match load(config) {
            Ok(_) => panic!("accepted"),
            Err(why) => why,
        }
    }

    #[test]
    fn listener_and_bearer() {
        let config = load(base()).unwrap();
        assert_eq!((config.party, config.bearer.is_none(), config.port_base, config.session.party), (1, true, 22400, 1));
        let mut every = base();
        every["listen"] = json!("0.0.0.0:19700");
        assert!(refusal(every.clone()).contains("not every interface"));
        for address in ["[::]:19700", ":19700"] {
            every["listen"] = json!(address);
            assert!(load(every.clone()).is_err(), "{address}");
        }
        every["application"] = json!({"token_file": "token"});
        assert_eq!(load(every.clone()).unwrap().bearer, Some(b"0123456789abcdef0123".to_vec()));
        every["application"] = json!({"token_file": "short-token"});
        assert!(refusal(every.clone()).contains("at least 16 bytes"));
        every["application"] = json!({"token_file": "missing"});
        assert!(load(every).is_err());
        let mut same = base();
        same["peer_listen"] = same["listen"].clone();
        assert!(refusal(same).contains("peer_listen must differ"));
        let mut ports = base();
        ports["worker"]["port_base"] = json!(65000);
        assert!(refusal(ports).contains("port_base"));
    }
}
