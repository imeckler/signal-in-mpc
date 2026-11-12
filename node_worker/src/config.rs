//! Arguments and environment (`tls_worker_v3.cpp` `run`, lines 410-493, and `peer_link.h`),
//! and the session string that every agreement carries.
//!
//! Usage: `node-worker PARTY(0|1) HOSTS(ignored) PORT CIRCUIT_CACHE_SCRIPT SESSION_ID_HEX`,
//! exactly as the C++ worker. Settings that change what is computed are folded into the session
//! string, so two workers configured differently disagree on their first request.
//!
//! Refused here (S8: not forwarded): `TLS_WORKER_TEST_PRODUCER` and `TLS_WORKER_SERVICE_FIXTURE`.
use std::net::Ipv4Addr;
use std::time::Duration;

#[derive(Debug, Clone, PartialEq)]
pub struct Config {
    /// 0 (leader: listens, owns the server socket) or 1.
    pub party: u8,
    pub port: u32,
    pub cache_script: String,
    pub session_hex: String,
    pub session_id: [u8; 32],
    /// TLS_WORKER_TEST_LINK_SHIFT: the dialling party (1) dials PORT+N for every link to the
    /// other worker, where scripts/delay_relay.cpp listens. 0 for the listening party.
    pub link_shift: u32,
    pub link_shift_requested: bool,
    /// TLS_WORKER_PEER (default 127.0.0.1) and TLS_WORKER_LISTEN (default all interfaces).
    pub peer: Ipv4Addr,
    pub listen: Option<Ipv4Addr>,
    pub ladder: bool,
    pub typed_open: bool,
    pub hinted: bool,
    pub field_direct: bool,
    pub field_batch: u32,
    pub field_reserve: u32,
    pub field_lines: u32,
    pub stock_factories: u32,
    pub stock_batch: u64,
    pub stock_reserve: u64,
    /// TLS_WORKER_PEER_WAIT (default 180 s); None: no bound.
    pub peer_wait: Option<Duration>,
    /// The session id followed by every setting both workers must share.
    pub session: String,
}

fn flag(value: Option<String>, name: &str, default: bool) -> Result<bool, String> {
    match value.as_deref() {
        None => Ok(default),
        Some("0") => Ok(false),
        Some("1") => Ok(true),
        Some(_) => Err(format!("{name}: 0 or 1")),
    }
}

fn number(text: &str, name: &str) -> Result<u64, String> {
    text.trim().parse::<u64>().map_err(|_| format!("{name}: not a number"))
}

impl Config {
    pub fn leader(&self) -> bool {
        self.party == 0
    }
    /// A peer other than this machine.
    pub fn remote(&self) -> bool {
        self.peer != Ipv4Addr::LOCALHOST
    }
    /// The Boolean engine's channel.
    pub fn engine_port(&self) -> u32 {
        self.port + self.link_shift
    }
    /// The field engine's.
    pub fn field_port(&self) -> u32 {
        self.port + 10 + self.link_shift
    }
    /// The control link's (link.rs).
    pub fn link_port(&self) -> u32 {
        self.port + crate::link::PORT_OFFSET + self.link_shift
    }
    /// FieldEngine's `peer`: the other worker when remote; with the test shift, this machine
    /// (so that the field engine's links pass the relay too); otherwise none.
    pub fn field_peer(&self) -> Option<String> {
        if self.remote() {
            Some(self.peer.to_string())
        } else if self.link_shift_requested {
            Some("127.0.0.1".into())
        } else {
            None
        }
    }
    pub fn challenge_domain(&self) -> String {
        format!("tls-worker-v3:session={}", self.session_hex)
    }

    pub fn parse(args: &[String], env: impl Fn(&str) -> Option<String>) -> Result<Config, String> {
        if args.len() != 6 {
            return Err("usage: node-worker PARTY HOSTS PORT CIRCUIT_CACHE_SCRIPT SESSION_ID_HEX".into());
        }
        let party: u8 = match args[1].as_str() {
            "0" => 0,
            "1" => 1,
            _ => return Err("party: 0 or 1".into()),
        };
        let port = number(&args[3], "port")? as u32;
        let session_hex = args[5].clone();
        if session_hex.len() != 64 || !session_hex.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)) {
            return Err("session id: 64 lowercase hex digits".into());
        }
        let mut session_id = [0u8; 32];
        for (i, out) in session_id.iter_mut().enumerate() {
            *out = u8::from_str_radix(&session_hex[2 * i..2 * i + 2], 16).unwrap();
        }
        if env("TLS_WORKER_TEST_PRODUCER").is_some() {
            return Err("TLS_WORKER_TEST_PRODUCER: the TEST producer is not part of node_worker".into());
        }
        if env("TLS_WORKER_SERVICE_FIXTURE").is_some() {
            return Err("TLS_WORKER_SERVICE_FIXTURE: the service fixture is not part of node_worker".into());
        }
        let shift_text = env("TLS_WORKER_TEST_LINK_SHIFT");
        let mut link_shift = 0;
        if let Some(t) = &shift_text {
            link_shift = number(t, "TLS_WORKER_TEST_LINK_SHIFT")? as u32;
            if !(12..=1000).contains(&link_shift) {
                return Err("TLS_WORKER_TEST_LINK_SHIFT: 12 to 1000".into());
            }
            if party == 0 {
                link_shift = 0;
            }
        }
        let address = |name: &str| -> Result<Option<Ipv4Addr>, String> {
            match env(name).filter(|v| !v.is_empty()) {
                None => Ok(None),
                Some(v) => v.parse().map(Some).map_err(|_| format!("{name}: a numeric IPv4 address")),
            }
        };
        let peer = address("TLS_WORKER_PEER")?.unwrap_or(Ipv4Addr::LOCALHOST);
        let listen = address("TLS_WORKER_LISTEN")?;
        let ladder = match env("TLS_WORKER_KEY_AGREEMENT").as_deref() {
            None | Some("split") => false,
            Some("ladder") => true,
            Some(_) => return Err("TLS_WORKER_KEY_AGREEMENT: ladder or split".into()),
        };
        let mut field_batch = if ladder { 3000 } else { 16 };
        if let Some(t) = env("TLS_WORKER_FIELD_BATCH") {
            field_batch = number(&t, "TLS_WORKER_FIELD_BATCH")? as u32;
            if !(1..=100000).contains(&field_batch) {
                return Err("TLS_WORKER_FIELD_BATCH: 1 to 100000".into());
            }
        }
        let (mut stock_factories, mut stock_batch, mut stock_reserve) = (2u64, 1u64 << 19, 1u64 << 22);
        if let Some(t) = env("TLS_WORKER_TRIPLE_STOCK") {
            let parts: Vec<&str> = t.split(',').collect();
            if parts.is_empty() || parts.len() > 3 {
                return Err("TLS_WORKER_TRIPLE_STOCK: FACTORIES[,BATCH[,RESERVE]]".into());
            }
            stock_factories = number(parts[0], "TLS_WORKER_TRIPLE_STOCK")?;
            if parts.len() > 1 {
                stock_batch = number(parts[1], "TLS_WORKER_TRIPLE_STOCK")?;
            }
            if parts.len() > 2 {
                stock_reserve = number(parts[2], "TLS_WORKER_TRIPLE_STOCK")?;
            }
            if stock_factories > 8 || stock_batch < 1024 || stock_batch > 1 << 24 || stock_reserve > 1 << 28 {
                return Err("TLS_WORKER_TRIPLE_STOCK: out of range".into());
            }
        }
        let (mut field_reserve, mut field_lines) = (8 * field_batch as u64, 2u64);
        if let Some(t) = env("TLS_WORKER_FIELD_STOCK") {
            let parts: Vec<&str> = t.split(',').collect();
            if parts.is_empty() || parts.len() > 2 {
                return Err("TLS_WORKER_FIELD_STOCK: RESERVE[,LINES]".into());
            }
            field_reserve = number(parts[0], "TLS_WORKER_FIELD_STOCK")?;
            if parts.len() > 1 {
                field_lines = number(parts[1], "TLS_WORKER_FIELD_STOCK")?;
            }
            if field_reserve > 10_000_000 || !(1..=8).contains(&field_lines) {
                return Err("TLS_WORKER_FIELD_STOCK: out of range".into());
            }
        }
        let field_direct = flag(env("TLS_WORKER_FIELD_DIRECT"), "TLS_WORKER_FIELD_DIRECT", false)?;
        let mut peer_wait = Some(Duration::from_secs(180));
        if let Some(t) = env("TLS_WORKER_PEER_WAIT") {
            let seconds = number(&t, "TLS_WORKER_PEER_WAIT")?;
            if seconds > 86400 {
                return Err("TLS_WORKER_PEER_WAIT: 0 to 86400".into());
            }
            peer_wait = (seconds > 0).then(|| Duration::from_secs(seconds));
        }
        let typed_open = flag(env("TLS_WORKER_TYPED_OPEN"), "TLS_WORKER_TYPED_OPEN", true)?;
        let hinted = flag(env("TLS_WORKER_HINTED"), "TLS_WORKER_HINTED", false)?;
        // `run`, lines 488-493, in that order.
        let mut session = session_hex.clone();
        if hinted {
            session += ":hinted";
        }
        if field_direct {
            session += ":field-direct";
        }
        session += if ladder { ":ladder" } else { ":split" };
        session += if typed_open { ":typed-open" } else { ":scan-open" };
        let (b, r) = if stock_factories > 0 { (stock_batch, stock_reserve) } else { (0, 0) };
        session += &format!(":stock={stock_factories},{b},{r}:field={field_batch},{field_reserve},{field_lines}");
        let config = Config {
            party,
            port,
            cache_script: args[4].clone(),
            session_hex,
            session_id,
            link_shift,
            link_shift_requested: shift_text.is_some(),
            peer,
            listen,
            ladder,
            typed_open,
            hinted,
            field_direct,
            field_batch,
            field_reserve: field_reserve as u32,
            field_lines: field_lines as u32,
            stock_factories: stock_factories as u32,
            stock_batch,
            stock_reserve,
            peer_wait,
            session,
        };
        let highest = config.link_port().max(config.port + crate::link::PORT_OFFSET);
        if config.port <= 1024 || highest > 65535 {
            return Err("port: above 1024, with room for PORT+20 (and the test shift)".into());
        }
        Ok(config)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn args(party: &str) -> Vec<String> {
        ["node-worker", party, "hosts", "21500", "circuit_cache.py", &"0f".repeat(32)].iter().map(|s| s.to_string()).collect()
    }

    fn parse(party: &str, env: &[(&str, &str)]) -> Result<Config, String> {
        let env: HashMap<String, String> = env.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect();
        Config::parse(&args(party), |k| env.get(k).cloned())
    }

    #[test]
    fn default_session_string_matches_the_cpp_worker() {
        let c = parse("0", &[]).unwrap();
        assert_eq!(c.session, format!("{}:split:typed-open:stock=2,524288,4194304:field=16,128,2", "0f".repeat(32)));
        assert_eq!((c.engine_port(), c.field_port(), c.link_port()), (21500, 21510, 21520));
        assert_eq!(c.field_peer(), None);
        assert_eq!(c.peer_wait, Some(Duration::from_secs(180)));
    }

    #[test]
    fn settings_fold_into_the_session_string() {
        let c = parse(
            "1",
            &[
                ("TLS_WORKER_KEY_AGREEMENT", "ladder"),
                ("TLS_WORKER_HINTED", "1"),
                ("TLS_WORKER_FIELD_DIRECT", "1"),
                ("TLS_WORKER_TYPED_OPEN", "0"),
                ("TLS_WORKER_TRIPLE_STOCK", "0"),
                ("TLS_WORKER_FIELD_STOCK", "100,3"),
            ],
        )
        .unwrap();
        assert_eq!(c.session, format!("{}:hinted:field-direct:ladder:scan-open:stock=0,0,0:field=3000,100,3", "0f".repeat(32)));
    }

    #[test]
    fn test_shift_moves_only_the_dialling_party() {
        let a = parse("0", &[("TLS_WORKER_TEST_LINK_SHIFT", "100")]).unwrap();
        let b = parse("1", &[("TLS_WORKER_TEST_LINK_SHIFT", "100")]).unwrap();
        assert_eq!((a.engine_port(), a.link_port()), (21500, 21520));
        assert_eq!((b.engine_port(), b.field_port(), b.link_port()), (21600, 21610, 21620));
        assert_eq!(a.field_peer().as_deref(), Some("127.0.0.1"));
        assert!(parse("1", &[("TLS_WORKER_TEST_LINK_SHIFT", "5")]).is_err());
    }

    #[test]
    fn refusals() {
        assert!(parse("2", &[]).is_err());
        assert!(parse("0", &[("TLS_WORKER_TEST_PRODUCER", "64")]).is_err());
        assert!(parse("0", &[("TLS_WORKER_SERVICE_FIXTURE", "text")]).is_err());
        assert!(parse("0", &[("TLS_WORKER_PEER", "localhost")]).is_err());
        assert!(parse("0", &[("TLS_WORKER_FIELD_BATCH", "0")]).is_err());
        assert!(parse("0", &[("TLS_WORKER_TRIPLE_STOCK", "9")]).is_err());
        assert!(parse("0", &[("TLS_WORKER_HINTED", "yes")]).is_err());
        let mut a = args("0");
        a[5] = "0F".repeat(32);
        assert!(Config::parse(&a, |_| None).is_err());
        assert_eq!(parse("0", &[("TLS_WORKER_PEER_WAIT", "0")]).unwrap().peer_wait, None);
        assert!(parse("0", &[("TLS_WORKER_PEER", "10.0.0.2")]).unwrap().remote());
    }
}
