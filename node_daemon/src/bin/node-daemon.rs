//! The daemon of one computation node: node-daemon CONFIG.json. See ../../README.md.
//!
//! It handles public values only (the application's requests, ids, results, session names) and
//! this node's own database client key file, by path. It never sees a share, never parses
//! Signal traffic, and returns nothing the controller did not report as an agreed public value.

use node_daemon::{Kind, Request, call, hmac, open, public_key, random_bytes, read_line, result_digest, seal, sha256, unix_now, write_line, MAX_MESSAGE_BYTES};
use serde_json::{Value, json};
use std::collections::HashMap;
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::{Arc, Condvar, Mutex, MutexGuard};
use std::thread;
use std::time::{Duration, Instant};

static STOP: AtomicBool = AtomicBool::new(false);

extern "C" fn on_signal(_: libc::c_int) {
    STOP.store(true, Ordering::SeqCst);
}

fn log(text: &str) {
    eprintln!("{} node-daemon: {text}", unix_now());
}

struct Config {
    party: u8,
    listen: String,
    peer: String,
    peer_key: Vec<u8>,
    state: PathBuf,
    controller: String,
    worker: String,
    send_directory: String,
    receive_directory: String,
    hosts: Vec<String>,
    port_base: u64,
    circuit_tool: String,
    circuit_manifest: Option<String>,
    endpoint: String,
    signal_port: u64,
    hostname: String,
    trust_root: String,
    certificate_checker: String,
    socks: Option<String>,
    circuits: Option<u64>,
    db_client: String,
    db_network: String,
    db_key: String,
    notify_key: [u8; 32],
    max_age: u64,
    export: Option<String>,
    tokens: Option<String>,
    kem_tool: Option<String>,
    environment: Vec<(String, String)>,
    receive: bool,
    agree_seconds: u64,
    start_margin_seconds: u64,
    send_seconds: u64,
    send_seconds_per_id: u64,
    delete_seconds: u64,
}

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

impl Config {
    fn load(path: &str) -> Result<Config, String> {
        let read = |p: &str| fs::read_to_string(p).map_err(|e| format!("{p}: {e}"));
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
        let environment = c.get("environment").and_then(Value::as_object)
            .map(|o| o.iter().filter_map(|(k, v)| v.as_str().map(|v| (k.clone(), v.to_string()))).collect()).unwrap_or_default();
        Ok(Config {
            party: party as u8,
            listen: text(&c, &["listen"])?,
            peer: text(&c, &["peer"])?,
            peer_key,
            state: PathBuf::from(text(&c, &["state_directory"])?),
            controller: text(&c, &["controller"])?,
            worker: text(&c, &["worker", "binary"])?,
            send_directory: text(&c, &["worker", "send_directory"])?,
            receive_directory: text(&c, &["worker", "receive_directory"])?,
            hosts,
            port_base: number(&c, &["worker", "port_base"], 22400),
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
            notify_key,
            max_age: number(&network, &["notify_max_age_secs"], 120),
            export: optional(&c, &["test", "export"]),
            tokens: optional(&c, &["test", "tokens"]),
            kem_tool: optional(&c, &["test", "kem_tool"]),
            environment,
            receive: c.get("receive").and_then(Value::as_bool).unwrap_or(true),
            agree_seconds: number(&c, &["timeouts", "agree_seconds"], 30),
            start_margin_seconds: number(&c, &["timeouts", "start_margin_seconds"], 30),
            send_seconds: number(&c, &["timeouts", "send_seconds"], 600),
            send_seconds_per_id: number(&c, &["timeouts", "send_seconds_per_id"], 60),
            delete_seconds: number(&c, &["timeouts", "delete_seconds"], 120),
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Stage {
    /// Verified here; the other daemon has not confirmed it holds the same request.
    Received,
    /// Both daemons hold it; waiting for its turn.
    Agreed,
    Running,
    Done,
}

impl Stage {
    fn name(self) -> &'static str {
        match self {
            Stage::Received => "received",
            Stage::Agreed => "agreed",
            Stage::Running => "running",
            Stage::Done => "done",
        }
    }
}

struct Job {
    request: Request,
    message: Option<String>,
    stage: Stage,
    received: Instant,
    /// The leader's first attempt to start it that the peer did not accept.
    start_failed: Option<Instant>,
    result: Option<Value>,
    finished: Option<Instant>,
}

#[derive(Default)]
struct Shared {
    jobs: HashMap<String, Job>,
    /// Agreed jobs in the order they will run (kept by the leader).
    queue: Vec<String>,
    /// A send or delete session is running on this node: one at a time.
    busy: bool,
    events: Vec<Value>,
    /// Controller processes of this daemon (killed with their children on shutdown).
    children: Vec<u32>,
    receive_child: Option<u32>,
    receive_generation: u64,
    sessions: u64,
}

struct Daemon {
    config: Config,
    shared: Mutex<Shared>,
    changed: Condvar,
}

/// The process and everything below it, from the process table.
fn tree(root: u32) -> Vec<u32> {
    let out = Command::new("ps").args(["-axo", "pid=,ppid="]).output().map(|o| String::from_utf8_lossy(&o.stdout).to_string()).unwrap_or_default();
    let rows: Vec<(u32, u32)> = out.lines().filter_map(|line| {
        let mut parts = line.split_whitespace();
        Some((parts.next()?.parse().ok()?, parts.next()?.parse().ok()?))
    }).collect();
    let mut found = vec![root];
    let mut index = 0;
    while index < found.len() {
        let parent = found[index];
        let below: Vec<u32> = rows.iter().filter(|(pid, ppid)| *ppid == parent && !found.contains(pid)).map(|(pid, _)| *pid).collect();
        found.extend(below);
        index += 1;
    }
    found
}

/// Ask the tree to stop, then kill what is left. (Children stay in the daemon's process group,
/// so whoever kills the group gets them too.)
fn kill_tree(root: u32) {
    let all = tree(root);
    for pid in &all {
        unsafe { libc::kill(*pid as libc::pid_t, libc::SIGTERM); }
    }
    thread::sleep(Duration::from_millis(800));
    for pid in &all {
        unsafe { libc::kill(*pid as libc::pid_t, libc::SIGKILL); }
    }
}

struct Outcome {
    code: Option<i32>,
    timed_out: bool,
    lines: Vec<String>,
    seconds: f64,
}

impl Daemon {
    fn lock(&self) -> MutexGuard<'_, Shared> {
        self.shared.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    fn leader(&self) -> bool {
        self.config.party == 0
    }

    fn peer_call(&self, message: Value) -> Result<Value, String> {
        call(&self.config.peer, &seal(&self.config.peer_key, message), Duration::from_secs(5))
    }

    // ---- Requests of the application.

    fn submit(&self, kind: Kind, message: &Value) -> Value {
        let refuse = |why: String| json!({"ok": false, "error": why});
        let request = match Request::parse(kind, message.get("request").unwrap_or(&Value::Null)) {
            Ok(request) => request,
            Err(why) => return refuse(why),
        };
        // The application's signature and the freshness rule, exactly as the database nodes
        // will check them, before anything else happens.
        if let Err(why) = request.verify_signature(&self.config.notify_key).and_then(|_| request.check_freshness(unix_now(), self.config.max_age)) {
            return refuse(why);
        }
        let text = match kind {
            Kind::Delete => None,
            Kind::Notify => {
                let Some(text) = message.get("message").and_then(Value::as_str) else { return refuse("notify: message is missing".into()) };
                if text.is_empty() || text.len() > MAX_MESSAGE_BYTES {
                    return refuse(format!("notify: the message must be 1..{MAX_MESSAGE_BYTES} bytes"));
                }
                if sha256(text.as_bytes()) != request.message_hash {
                    return refuse("notify: the message is not the one the request was signed for".into());
                }
                Some(text.to_string())
            }
        };
        let digest = hex::encode(request.digest());
        let mut shared = self.lock();
        if let Some(job) = shared.jobs.get(&digest) {
            // The same signed request again: only a job that did not run to completion is taken
            // again (a notify then resumes from the journal and sends what was not settled).
            let status = job.result.as_ref().and_then(|r| r["status"].as_str()).unwrap_or("");
            if !(job.stage == Stage::Done && (status == "failed" || status == "rejected")) {
                return json!({"ok": true, "job": digest, "state": job.stage.name(), "known": true});
            }
        }
        log(&format!("{} {} received: {} ids", kind.name(), &digest[..16], request.ids.len()));
        shared.jobs.insert(digest.clone(), Job { request, message: text, stage: Stage::Received, received: Instant::now(), start_failed: None, result: None, finished: None });
        self.changed.notify_all();
        json!({"ok": true, "job": digest, "state": "received"})
    }

    fn wait(&self, message: &Value) -> Value {
        let Some(digest) = message.get("job").and_then(Value::as_str) else { return json!({"ok": false, "error": "wait: job is missing"}) };
        let deadline = Instant::now() + Duration::from_secs(message.get("timeout").and_then(Value::as_u64).unwrap_or(0).min(3600));
        let mut shared = self.lock();
        loop {
            match shared.jobs.get(digest) {
                None => return json!({"ok": false, "error": "unknown job"}),
                Some(job) if job.stage == Stage::Done => return json!({"ok": true, "job": digest, "state": "done", "result": job.result}),
                Some(job) => {
                    let now = Instant::now();
                    if now >= deadline {
                        return json!({"ok": true, "job": digest, "state": job.stage.name()});
                    }
                    shared = self.changed.wait_timeout(shared, (deadline - now).min(Duration::from_secs(1))).unwrap_or_else(|p| p.into_inner()).0;
                }
            }
        }
    }

    fn events(&self, message: &Value) -> Value {
        let after = message.get("after").and_then(Value::as_u64).unwrap_or(0) as usize;
        let deadline = Instant::now() + Duration::from_secs(message.get("wait").and_then(Value::as_u64).unwrap_or(0).min(3600));
        let mut shared = self.lock();
        loop {
            let now = Instant::now();
            if shared.events.len() > after || now >= deadline {
                let list: Vec<Value> = shared.events.iter().skip(after).cloned().collect();
                return json!({"ok": true, "events": list, "next": shared.events.len()});
            }
            shared = self.changed.wait_timeout(shared, (deadline - now).min(Duration::from_secs(1))).unwrap_or_else(|p| p.into_inner()).0;
        }
    }

    fn status(&self) -> Value {
        let shared = self.lock();
        let count = |stage: Stage| shared.jobs.values().filter(|j| j.stage == stage).count();
        json!({"ok": true, "party": self.config.party, "received": count(Stage::Received), "agreed": count(Stage::Agreed), "running": count(Stage::Running),
            "done": count(Stage::Done), "events": shared.events.len(), "receive_session_running": shared.receive_child.is_some(),
            "receive_sessions_started": shared.receive_generation})
    }

    // ---- Messages of the other daemon (authenticated before they get here).

    fn peer(self: &Arc<Self>, op: &str, message: &Value) -> Value {
        let digest = message.get("job").and_then(Value::as_str).unwrap_or("").to_string();
        match op {
            "peer-ping" => json!({"ok": true}),
            // "Do you hold this request too?" Yes only for a request this daemon verified itself.
            "peer-agree" => {
                let mut shared = self.lock();
                match shared.jobs.get_mut(&digest) {
                    Some(job) if job.stage == Stage::Received || job.stage == Stage::Agreed => {
                        job.stage = Stage::Agreed;
                        json!({"ok": true})
                    }
                    _ => json!({"ok": false}),
                }
            }
            "peer-start" => {
                if self.leader() {
                    return json!({"ok": false, "error": "only party 0 starts sessions"});
                }
                let (Some(session), Some(port)) = (message.get("session").and_then(Value::as_str), message.get("port").and_then(Value::as_u64)) else {
                    return json!({"ok": false, "error": "peer-start: session and port"});
                };
                let mut shared = self.lock();
                if shared.busy {
                    return json!({"ok": false, "busy": true});
                }
                let fresh = match shared.jobs.get(&digest) {
                    Some(job) if job.stage == Stage::Received || job.stage == Stage::Agreed => job.request.check_freshness(unix_now(), self.config.max_age).is_ok(),
                    _ => return json!({"ok": false, "error": "not a request this node holds"}),
                };
                if !fresh {
                    return json!({"ok": false, "error": "expired"});
                }
                shared.jobs.get_mut(&digest).unwrap().stage = Stage::Running;
                shared.busy = true;
                drop(shared);
                self.start_job(digest, session.to_string(), port);
                json!({"ok": true})
            }
            "peer-receive" => {
                if self.leader() || !self.config.receive {
                    return json!({"ok": false, "error": "no receive session here"});
                }
                let (Some(session), Some(port)) = (message.get("session").and_then(Value::as_str), message.get("port").and_then(Value::as_u64)) else {
                    return json!({"ok": false, "error": "peer-receive: session and port"});
                };
                let old = self.lock().receive_child.take();
                if let Some(pid) = old {
                    kill_tree(pid);
                }
                let (daemon, session) = (self.clone(), session.to_string());
                thread::spawn(move || daemon.receive_session(&session, port));
                json!({"ok": true})
            }
            _ => json!({"ok": false, "error": "unknown peer message"}),
        }
    }

    // ---- Sessions.

    fn finish(&self, digest: &str, status: &str, results: Value, detail: &str, evidence: Option<Value>, seconds: f64) {
        let mut shared = self.lock();
        let Some(job) = shared.jobs.get_mut(digest) else { return };
        let kind = job.request.kind;
        // `common` is what both nodes must report alike; its digest is what the application compares.
        let common = match kind {
            Kind::Notify => json!({"job": digest, "kind": "notify", "status": status, "results": results}),
            Kind::Delete => json!({"job": digest, "kind": "delete", "status": status,
                "ids": job.request.ids.iter().map(|id| id.to_string()).collect::<Vec<_>>()}),
        };
        let mut result = common.clone();
        result["result_digest"] = json!(result_digest(&common));
        result["node"] = json!({"party": self.config.party, "detail": detail, "seconds": (seconds * 10.0).round() / 10.0});
        if let Some(evidence) = evidence {
            result["node"]["evidence"] = evidence;
        }
        job.result = Some(result);
        job.stage = Stage::Done;
        job.finished = Some(Instant::now());
        shared.queue.retain(|d| d != digest);
        log(&format!("{} {} done: {status}{}", kind.name(), &digest[..16.min(digest.len())], if detail.is_empty() { String::new() } else { format!(" ({detail})") }));
        self.changed.notify_all();
    }

    fn start_job(self: &Arc<Self>, digest: String, session: String, port: u64) {
        let daemon = self.clone();
        thread::spawn(move || {
            daemon.run_job(&digest, &session, port);
            daemon.lock().busy = false;
            daemon.changed.notify_all();
        });
    }

    fn work(&self, name: &str) -> Result<PathBuf, String> {
        let path = self.config.state.join("work").join(name);
        fs::create_dir_all(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        Ok(path)
    }

    fn database_environment(&self, command: &mut Command, work: &Path) {
        for (name, value) in &self.config.environment {
            command.env(name, value);
        }
        command.env("SIGNAL_DB_CLIENT", &self.config.db_client).env("SIGNAL_DB_NETWORK", &self.config.db_network)
            .env("SIGNAL_DB_KEY", &self.config.db_key).env("SIGNAL_DB_WORK", work);
        if let Some(tokens) = &self.config.tokens {
            command.env("SIGNAL_DB_TOKENS", tokens);
        }
    }

    /// The controller of a two-party session (its argument list is its interface).
    fn session_command(&self, directory: &str, session: &str, port: u64, work: &Path) -> Result<Command, String> {
        let hosts = work.join("hosts");
        fs::write(&hosts, self.config.hosts.iter().map(|h| format!("{h}\n")).collect::<String>()).map_err(|e| format!("{}: {e}", hosts.display()))?;
        let mut command = Command::new(&self.config.controller);
        command.args([&self.config.worker, directory, &self.config.party.to_string(), &hosts.display().to_string(), &port.to_string(),
            &self.config.circuit_tool, session, &self.config.endpoint, &self.config.signal_port.to_string(), &self.config.hostname,
            &self.config.certificate_checker, &self.config.trust_root, "0"]);
        self.database_environment(&mut command, work);
        for name in ["SIGNAL_LOCAL_CREDENTIALS", "SIGNAL_LOCAL_RECEIVE", "SIGNAL_LOCAL_EXPECT", "SIGNAL_LOCAL_EXTRA_CONTACTS", "SIGNAL_LOCAL_NEW_CONTACT",
            "SIGNAL_LOCAL_STORE", "SIGNAL_LOCAL_BROADCASTS", "SIGNAL_LOCAL_PAUSE_AFTER", "SIGNAL_LOCAL_PAUSE_REFRESH", "SIGNAL_LOCAL_TIMESTAMP",
            "SIGNAL_DB_REQUEST", "SIGNAL_NOTIFY_ID", "SIGNAL_NOTIFY_JOURNAL", "SIGNAL_NOTIFY_MESSAGE_FILE", "SIGNAL_LOCAL_EVENTS", "SIGNAL_RECOVERY"] {
            command.env_remove(name);   // a session's kind is decided here, not by the daemon's own environment
        }
        if let Some(export) = &self.config.export {
            command.env("SIGNAL_LOCAL_EXPORT", export);
        }
        if let Some(tool) = &self.config.kem_tool {
            command.env("SIGNAL_LOCAL_KEM", tool);
        }
        if let Some(manifest) = &self.config.circuit_manifest {
            command.env("CIRCUIT_MANIFEST", manifest);
        }
        if let Some(socks) = &self.config.socks {
            command.env("SIGNAL_TOR_SOCKS", socks).env("SIGNAL_TOR_CIRCUITS", self.config.circuits.unwrap_or(1).to_string());
        }
        Ok(command)
    }

    /// Run a controller to its end or to `limit`. Its standard output is read line by line
    /// (`on_line`); its standard error goes to the node's log file `log_name`.
    fn supervise(&self, mut command: Command, log_name: &str, limit: Duration, receive: bool, mut on_line: impl FnMut(&str)) -> Result<Outcome, String> {
        let logs = self.config.state.join("logs");
        fs::create_dir_all(&logs).map_err(|e| format!("{}: {e}", logs.display()))?;
        let file = fs::File::create(logs.join(log_name)).map_err(|e| format!("{log_name}: {e}"))?;
        let started = Instant::now();
        let mut child = command.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(file).spawn().map_err(|e| format!("controller: {e}"))?;
        let pid = child.id();
        {
            let mut shared = self.lock();
            shared.children.push(pid);
            if receive {
                shared.receive_child = Some(pid);
            }
        }
        let (sender, lines) = mpsc::channel::<String>();
        let output = child.stdout.take();
        thread::spawn(move || {
            if let Some(output) = output {
                for line in BufReader::new(output).lines() {
                    match line {
                        Ok(line) if line.len() <= 8 << 20 => { if sender.send(line).is_err() { break } }
                        _ => break,
                    }
                }
            }
        });
        let mut collected = Vec::new();
        let mut timed_out = false;
        let mut exited: Option<(Option<i32>, Instant)> = None;
        loop {
            match lines.recv_timeout(Duration::from_millis(100)) {
                Ok(line) => {
                    on_line(&line);
                    if collected.len() < 4096 {
                        collected.push(line);
                    }
                    continue;
                }
                Err(mpsc::RecvTimeoutError::Disconnected) if exited.is_some() => break,
                Err(_) => {}
            }
            match exited {
                // After the exit: what is still in the pipe, for at most two seconds.
                Some((_, at)) => if at.elapsed() > Duration::from_secs(2) { break },
                None => {
                    if let Ok(Some(status)) = child.try_wait() {
                        exited = Some((status.code(), Instant::now()));
                    } else if started.elapsed() > limit || STOP.load(Ordering::SeqCst) {
                        timed_out = !STOP.load(Ordering::SeqCst);
                        kill_tree(pid);
                        let status = child.wait().ok();
                        exited = Some((status.and_then(|s| s.code()), Instant::now()));
                    }
                }
            }
        }
        let mut shared = self.lock();
        shared.children.retain(|p| *p != pid);
        if shared.receive_child == Some(pid) {
            shared.receive_child = None;
        }
        Ok(Outcome { code: exited.and_then(|e| e.0), timed_out, lines: collected, seconds: started.elapsed().as_secs_f64() })
    }

    fn run_job(&self, digest: &str, session: &str, port: u64) {
        let (request, message) = {
            let shared = self.lock();
            let Some(job) = shared.jobs.get(digest) else { return };
            (job.request.clone(), job.message.clone())
        };
        let outcome = match request.kind {
            Kind::Notify => self.run_notify(digest, &request, message.as_deref().unwrap_or(""), session, port),
            Kind::Delete => self.run_delete(digest, &request),
        };
        if let Err(why) = outcome {
            // A local failure before or around the session (a file, a spawn): logged here, and
            // reported to the application only as "failed".
            log(&format!("{} {}: {why}", request.kind.name(), &digest[..16]));
            self.finish(digest, "failed", json!([]), "the session could not be run on this node", None, 0.0);
        }
    }

    fn run_notify(&self, digest: &str, request: &Request, message: &str, session: &str, port: u64) -> Result<(), String> {
        let work = self.work("send")?;
        let write = |name: &str, bytes: &[u8]| -> Result<PathBuf, String> {
            let path = work.join(name);
            fs::write(&path, bytes).map_err(|e| format!("{}: {e}", path.display()))?;
            Ok(path)
        };
        let request_file = write("request.json", request.file_json().to_string().as_bytes())?;
        let message_file = write("message.txt", message.as_bytes())?;
        // The journal of what this notify settled, owned by the daemon: one file per notify,
        // named by the request's digest, removed when the notify completes.
        let journals = self.config.state.join("journal");
        fs::create_dir_all(&journals).map_err(|e| format!("{}: {e}", journals.display()))?;
        let journal = journals.join(format!("{digest}.jsonl"));
        let mut command = self.session_command(&self.config.send_directory, session, port, &work)?;
        command.env("SIGNAL_DB_REQUEST", &request_file).env("SIGNAL_NOTIFY_MESSAGE_FILE", &message_file)
            .env("SIGNAL_NOTIFY_ID", digest).env("SIGNAL_NOTIFY_JOURNAL", &journal);
        let limit = Duration::from_secs(self.config.send_seconds + self.config.send_seconds_per_id * request.ids.len() as u64);
        log(&format!("notify {} session {} starts on port {port}", &digest[..16], &session[..16.min(session.len())]));
        let outcome = self.supervise(command, &format!("send-{}.log", &digest[..16]), limit, false, |_| {})?;
        let report = outcome.lines.iter().rev().filter_map(|line| serde_json::from_str::<Value>(line).ok()).find(|v| v.get("passed").is_some());
        let passed = outcome.code == Some(0) && report.as_ref().is_some_and(|r| r["passed"] == json!(true));
        let Some(report) = report.filter(|_| passed) else {
            let detail = if outcome.timed_out { "the session was stopped at its time limit".to_string() } else { format!("the session ended with status {:?}", outcome.code) };
            self.finish(digest, "failed", json!([]), &detail, None, outcome.seconds);
            return Ok(());
        };
        // Per id, from what the two controllers agreed on (they compare a digest of these before
        // reporting them): the send's result, or that the database nodes do not have the id.
        let listed = |name: &str| -> Vec<String> {
            report.get(name).and_then(Value::as_array).map(|l| l.iter().filter_map(|v| v.as_str().map(str::to_string)).collect()).unwrap_or_default()
        };
        let (unknown, waiting) = (listed("unknown"), listed("not_yet_readable"));
        let rows = report.get("results").and_then(Value::as_array).cloned().unwrap_or_default();
        let results: Vec<Value> = request.ids.iter().map(|id| {
            let id = id.to_string();
            let row = rows.iter().find(|r| r["id"].as_str() == Some(&id) && r["message"].as_u64() == Some(0));
            let (result, reason) = match row {
                Some(row) => (row["result"].as_str().unwrap_or("fault").to_string(), row["reason"].as_str().unwrap_or("").to_string()),
                None if unknown.contains(&id) => ("unknown contact".to_string(), String::new()),
                None if waiting.contains(&id) => ("retry later".to_string(), "not readable until the database nodes' next epoch".to_string()),
                None => ("fault".to_string(), "the session reported no result for this id".to_string()),
            };
            json!({"id": id, "result": result, "reason": reason})
        }).collect();
        let _ = fs::remove_file(&journal);
        self.finish(digest, "completed", json!(results), "", None, outcome.seconds);
        Ok(())
    }

    fn run_delete(&self, digest: &str, request: &Request) -> Result<(), String> {
        let work = self.work("delete")?;
        let request_file = work.join("request.json");
        fs::write(&request_file, request.file_json().to_string()).map_err(|e| format!("{}: {e}", request_file.display()))?;
        let evidence_file = work.join("delete.json");
        let _ = fs::remove_file(&evidence_file);
        let mut command = Command::new(&self.config.controller);
        command.args(["db-delete", &self.config.party.to_string(), &request_file.display().to_string()]);
        self.database_environment(&mut command, &work);
        let outcome = self.supervise(command, &format!("delete-{}.log", &digest[..16]), Duration::from_secs(self.config.delete_seconds), false, |_| {})?;
        // The database client's report: which nodes committed, with each node's signature over
        // the request's digest. Public, and checkable by anyone with the network config.
        let evidence = fs::read_to_string(&evidence_file).ok().and_then(|text| serde_json::from_str::<Value>(&text).ok());
        let deleted = outcome.code == Some(0) && outcome.lines.iter().any(|line| line.contains("\"deleted\":true"))
            && evidence.as_ref().is_some_and(|e| e["acknowledged"] == json!(true) && e["request_digest"].as_str() == Some(digest));
        if deleted {
            self.finish(digest, "deleted", json!([]), "", evidence, outcome.seconds);
        } else {
            let detail = if outcome.timed_out { "stopped at the time limit".to_string() } else { "the database nodes did not confirm the delete to this node".to_string() };
            self.finish(digest, "failed", json!([]), &detail, evidence, outcome.seconds);
        }
        Ok(())
    }

    /// One receive session of this node, to its end. Each new user it stores is an event.
    fn receive_session(&self, session: &str, port: u64) {
        let run = || -> Result<Outcome, String> {
            let work = self.work("receive")?;
            let mut command = self.session_command(&self.config.receive_directory, session, port, &work)?;
            // No credentials here: the account comes from the database nodes. The session ends
            // only when it fails or its step budget runs out; it is then started again.
            command.env("SIGNAL_LOCAL_RECEIVE", "1").env("SIGNAL_LOCAL_EXPECT", "1000000000").env("SIGNAL_LOCAL_EVENTS", "1");
            let generation = {
                let mut shared = self.lock();
                shared.receive_generation += 1;
                shared.receive_generation
            };
            log(&format!("receive session {} starts on port {port}", &session[..16.min(session.len())]));
            self.supervise(command, &format!("receive-{generation}.log"), Duration::from_secs(u64::MAX / 4), true, |line| {
                let Ok(event) = serde_json::from_str::<Value>(line) else { return };
                if event["event"] != json!("signup") {
                    return;
                }
                let Some(id) = event["id"].as_str().filter(|id| id.parse::<u128>().is_ok()) else { return };
                let mut shared = self.lock();
                let entry = json!({"seq": shared.events.len() + 1, "event": "signup", "id": id, "at": unix_now()});
                if let Ok(mut file) = fs::OpenOptions::new().create(true).append(true).open(self.config.state.join("events.jsonl")) {
                    let _ = writeln!(file, "{entry}");
                }
                shared.events.push(entry);
                log(&format!("signup: id {id}"));
                self.changed.notify_all();
            })
        };
        match run() {
            Ok(outcome) => log(&format!("receive session ended after {:.0} s with status {:?}", outcome.seconds, outcome.code)),
            Err(why) => log(&format!("receive session: {why}")),
        }
    }

    fn session_name(&self) -> Result<(String, u64), String> {
        let mut shared = self.lock();
        shared.sessions += 1;
        Ok((hex::encode(random_bytes(32)?), shared.sessions))
    }

    // ---- The clock of both daemons: requests that were not confirmed or not started in time.

    fn expire(&self) {
        let now = unix_now();
        let late: Vec<(String, &'static str, &'static str)> = {
            let shared = self.lock();
            // The follower waits a little longer than the leader asks, so that the two give the same answer.
            let patience = Duration::from_secs(self.config.agree_seconds + if self.leader() { 0 } else { 5 });
            let margin = if self.leader() { self.config.start_margin_seconds.min(self.config.max_age / 2) } else { 0 };
            shared.jobs.iter().filter_map(|(digest, job)| {
                if job.stage == Stage::Received && job.received.elapsed() > patience {
                    Some((digest.clone(), "rejected", "the other node did not confirm that it received this request"))
                } else if (job.stage == Stage::Received || job.stage == Stage::Agreed) && now + margin > job.request.issued_at + self.config.max_age {
                    Some((digest.clone(), "expired", "the request's lifetime ended before its turn came"))
                } else {
                    None
                }
            }).collect()
        };
        for (digest, status, detail) in late {
            self.finish(&digest, status, json!([]), detail, None, 0.0);
        }
        // Finished jobs are kept for an hour (the application reads their results), at most 4096 of them.
        let mut shared = self.lock();
        let many = shared.jobs.len() > 4096;
        shared.jobs.retain(|_, job| job.finished.is_none_or(|at| at.elapsed() < Duration::from_secs(if many { 60 } else { 3600 })));
    }

    /// Party 0: confirm each new request with the other daemon, then run agreed requests one at
    /// a time, in the order they were confirmed.
    fn schedule(self: &Arc<Self>) {
        let new: Vec<String> = self.lock().jobs.iter().filter(|(_, job)| job.stage == Stage::Received).map(|(digest, _)| digest.clone()).collect();
        for digest in new {
            if self.peer_call(json!({"op": "peer-agree", "job": digest})).is_ok_and(|reply| reply["ok"] == json!(true)) {
                let mut shared = self.lock();
                if let Some(job) = shared.jobs.get_mut(&digest).filter(|job| job.stage == Stage::Received) {
                    job.stage = Stage::Agreed;
                    shared.queue.push(digest.clone());
                    log(&format!("request {} confirmed by the other node", &digest[..16]));
                }
            }
        }
        let next = {
            let shared = self.lock();
            if shared.busy { None } else { shared.queue.first().cloned() }
        };
        let Some(digest) = next else { return };
        let Ok((session, count)) = self.session_name() else { return };
        let port = self.config.port_base + 40 * (count % 8);
        let reply = self.peer_call(json!({"op": "peer-start", "job": digest, "session": session, "port": port}));
        if reply.as_ref().is_ok_and(|r| r["ok"] == json!(true)) {
            let mut shared = self.lock();
            shared.queue.retain(|d| *d != digest);
            shared.busy = true;
            if let Some(job) = shared.jobs.get_mut(&digest) {
                job.stage = Stage::Running;
            }
            drop(shared);
            self.start_job(digest, session, port);
        } else if !reply.as_ref().is_ok_and(|r| r["busy"] == json!(true)) {
            // The other node is unreachable or refuses: tried again until the confirmation time is used up.
            let mut shared = self.lock();
            let first = shared.jobs.get_mut(&digest).map(|job| *job.start_failed.get_or_insert_with(Instant::now));
            drop(shared);
            if first.is_some_and(|at| at.elapsed() > Duration::from_secs(self.config.agree_seconds)) {
                self.finish(&digest, "failed", json!([]), "the other node did not start the session", None, 0.0);
            }
        }
    }

    /// Party 0: keep one receive session running; when it ends, start the next (both nodes).
    fn keep_receiving(self: &Arc<Self>) {
        let mut pause = 2u64;
        while !STOP.load(Ordering::SeqCst) {
            let Ok((session, count)) = self.session_name() else { return };
            let port = self.config.port_base + 320 + 40 * (count % 8);
            let started = Instant::now();
            match self.peer_call(json!({"op": "peer-receive", "session": session, "port": port})) {
                Ok(reply) if reply["ok"] == json!(true) => self.receive_session(&session, port),
                _ => {}
            }
            // A session that ended at once is not restarted in a tight loop.
            pause = if started.elapsed() > Duration::from_secs(120) { 2 } else { (pause * 2).min(60) };
            for _ in 0..pause * 5 {
                if STOP.load(Ordering::SeqCst) {
                    return;
                }
                thread::sleep(Duration::from_millis(200));
            }
        }
    }

    fn handle(self: &Arc<Self>, message: &Value) -> Value {
        let op = message.get("op").and_then(Value::as_str).unwrap_or("");
        if op.starts_with("peer-") {
            return match open(&self.config.peer_key, message) {
                Ok(()) => self.peer(op, message),
                Err(why) => json!({"ok": false, "error": why}),
            };
        }
        match op {
            "notify" => self.submit(Kind::Notify, message),
            "delete" => self.submit(Kind::Delete, message),
            "wait" => self.wait(message),
            "events" => self.events(message),
            "status" => self.status(),
            _ => json!({"ok": false, "error": "unknown request"}),
        }
    }
}

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    if arguments.len() != 2 {
        eprintln!("usage: node-daemon CONFIG.json");
        std::process::exit(2);
    }
    let config = match Config::load(&arguments[1]) {
        Ok(config) => config,
        Err(why) => {
            eprintln!("node-daemon: {why}");
            std::process::exit(2);
        }
    };
    unsafe {
        libc::signal(libc::SIGTERM, on_signal as extern "C" fn(libc::c_int) as libc::sighandler_t);
        libc::signal(libc::SIGINT, on_signal as extern "C" fn(libc::c_int) as libc::sighandler_t);
    }
    if let Err(e) = fs::create_dir_all(&config.state) {
        eprintln!("node-daemon: {}: {e}", config.state.display());
        std::process::exit(2);
    }
    // Signups reported before a restart are still reported after it.
    let events: Vec<Value> = fs::read_to_string(config.state.join("events.jsonl")).unwrap_or_default().lines()
        .filter_map(|line| serde_json::from_str(line).ok()).collect();
    // Journals of notifies that can no longer be resumed (their request has long expired).
    if let Ok(entries) = fs::read_dir(config.state.join("journal")) {
        for entry in entries.flatten() {
            let old = entry.metadata().and_then(|m| m.modified()).ok().and_then(|t| t.elapsed().ok()).is_some_and(|age| age > Duration::from_secs(86400));
            if old {
                let _ = fs::remove_file(entry.path());
            }
        }
    }
    let listener = match TcpListener::bind(&config.listen) {
        Ok(listener) => listener,
        Err(e) => {
            eprintln!("node-daemon: {}: {e}", config.listen);
            std::process::exit(2);
        }
    };
    // A fixed check of the link's MAC, so that a wrong build is noticed at start.
    assert_eq!(hex::encode(hmac(b"Jefe", b"what do ya want for nothing?")), "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843");
    let daemon = Arc::new(Daemon { config, shared: Mutex::new(Shared { events, ..Shared::default() }), changed: Condvar::new() });
    log(&format!("party {} listening on {}", daemon.config.party, daemon.config.listen));
    println!("listening {}", daemon.config.listen);
    let _ = std::io::stdout().flush();
    {
        let daemon = daemon.clone();
        thread::spawn(move || {
            for stream in listener.incoming().flatten() {
                let daemon = daemon.clone();
                thread::spawn(move || {
                    let mut stream = stream;
                    let _ = stream.set_read_timeout(Some(Duration::from_secs(30)));
                    let reply = match read_line(&mut stream) {
                        Ok(message) => daemon.handle(&message),
                        Err(why) => json!({"ok": false, "error": why}),
                    };
                    let _ = write_line(&mut stream, &reply);
                });
            }
        });
    }
    if daemon.leader() && daemon.config.receive {
        let daemon = daemon.clone();
        thread::spawn(move || daemon.keep_receiving());
    }
    while !STOP.load(Ordering::SeqCst) {
        daemon.expire();
        if daemon.leader() {
            daemon.schedule();
        }
        thread::sleep(Duration::from_millis(200));
    }
    log("stopping");
    let children = daemon.lock().children.clone();
    for pid in children {
        kill_tree(pid);
    }
}
