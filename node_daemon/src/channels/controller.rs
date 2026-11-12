//! The controller processes a daemon starts, and what passes between them.
//!
//! Out: the controller's argument list and environment, from `SessionEnv` (the node's settings)
//! and `Launch` (which session). Nothing else is inherited that decides a session's kind: the
//! variables in `SESSION_KIND_VARIABLES` are removed from the daemon's own environment first.
//! In: its standard output, line by line, as `ControllerLine`; its standard error goes to a log
//! file under `STATE/logs/`. Also here: the process table (`ps`) to find a controller's process
//! tree, and `kill` of that tree.

use super::disk::{Disk, LogFile};
use super::host::{Moment, log, stopping};
use serde_json::{Value, json};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

/// The variables that decide what kind of session a controller runs. They are set below from
/// `Launch` only, never inherited from the daemon's environment.
pub const SESSION_KIND_VARIABLES: [&str; 17] = ["SIGNAL_LOCAL_CREDENTIALS", "SIGNAL_LOCAL_RECEIVE", "SIGNAL_LOCAL_EXPECT", "SIGNAL_LOCAL_EXTRA_CONTACTS",
    "SIGNAL_LOCAL_NEW_CONTACT", "SIGNAL_LOCAL_STORE", "SIGNAL_LOCAL_BROADCASTS", "SIGNAL_LOCAL_PAUSE_AFTER", "SIGNAL_LOCAL_PAUSE_REFRESH",
    "SIGNAL_LOCAL_TIMESTAMP", "SIGNAL_DB_REQUEST", "SIGNAL_NOTIFY_ID", "SIGNAL_NOTIFY_JOURNAL", "SIGNAL_NOTIFY_MESSAGE_FILE", "SIGNAL_LOCAL_EVENTS",
    "SIGNAL_RECOVERY", "SIGNAL_SERVE_DIR"];

/// The node's settings that every controller it starts is given (from the configuration).
#[derive(Clone, Debug)]
pub struct SessionEnv {
    pub controller: String,
    pub worker: String,
    pub send_directory: String,
    pub receive_directory: String,
    pub party: u8,
    pub hosts: Vec<String>,
    pub circuit_tool: String,
    pub circuit_manifest: Option<String>,
    pub endpoint: String,
    pub signal_port: u64,
    pub hostname: String,
    pub trust_root: String,
    pub certificate_checker: String,
    pub socks: Option<String>,
    pub circuits: Option<u64>,
    pub db_client: String,
    pub db_network: String,
    pub db_key: String,
    /// TEST scaffolding (README, "What is still scaffolding").
    pub export: Option<String>,
    pub tokens: Option<String>,
    pub kem_tool: Option<String>,
    /// Passed to every controller as is (`environment` in the configuration).
    pub environment: Vec<(String, String)>,
    /// TLS_WORKER_PEER_WAIT, unless `environment` sets it.
    pub peer_wait_seconds: u64,
}

/// Which controller to start.
#[derive(Clone, Debug)]
pub enum Launch {
    /// A one-notify send session (`send_session.long_lived: false`).
    Notify { session: String, port: u64, request_file: PathBuf, message_file: PathBuf, digest: String, journal: PathBuf },
    /// The receive session (runs until it fails or its step budget is used up).
    Receive { session: String, port: u64 },
    /// The long-lived send session, taking jobs from `serve` (`SIGNAL_SERVE_DIR`).
    Serve { session: String, port: u64, serve: PathBuf },
    /// `db-delete`: one delete request through the database client (no two-party session).
    Delete { request_file: PathBuf },
}

impl SessionEnv {
    fn database_environment(&self, command: &mut Command, work: &Path) {
        for (name, value) in &self.environment {
            command.env(name, value);
        }
        command.env("SIGNAL_DB_CLIENT", &self.db_client).env("SIGNAL_DB_NETWORK", &self.db_network)
            .env("SIGNAL_DB_KEY", &self.db_key).env("SIGNAL_DB_WORK", work);
        if let Some(tokens) = &self.tokens {
            command.env("SIGNAL_DB_TOKENS", tokens);
        }
    }

    /// The controller of a two-party session (its argument list is its interface).
    fn session_command(&self, disk: &Disk, directory: &str, session: &str, port: u64, work: &Path) -> Result<Command, String> {
        let hosts = disk.write_hosts(work, &self.hosts)?;
        let mut command = Command::new(&self.controller);
        command.args([&self.worker, directory, &self.party.to_string(), &hosts.display().to_string(), &port.to_string(),
            &self.circuit_tool, session, &self.endpoint, &self.signal_port.to_string(), &self.hostname,
            &self.certificate_checker, &self.trust_root, "0"]);
        self.database_environment(&mut command, work);
        for name in SESSION_KIND_VARIABLES {
            command.env_remove(name);   // a session's kind is decided here, not by the daemon's own environment
        }
        // The workers' bounded wait for each other at every request (tls_worker_v3.cpp, `await_peer`).
        if !self.environment.iter().any(|(name, _)| name == "TLS_WORKER_PEER_WAIT") {
            command.env("TLS_WORKER_PEER_WAIT", self.peer_wait_seconds.to_string());
        }
        if let Some(export) = &self.export {
            command.env("SIGNAL_LOCAL_EXPORT", export);
        }
        if let Some(tool) = &self.kem_tool {
            command.env("SIGNAL_LOCAL_KEM", tool);
        }
        if let Some(manifest) = &self.circuit_manifest {
            command.env("CIRCUIT_MANIFEST", manifest);
        }
        if let Some(socks) = &self.socks {
            command.env("SIGNAL_TOR_SOCKS", socks).env("SIGNAL_TOR_CIRCUITS", self.circuits.unwrap_or(1).to_string());
        }
        Ok(command)
    }

    fn command(&self, disk: &Disk, launch: &Launch, work: &Path) -> Result<Command, String> {
        Ok(match launch {
            Launch::Notify { session, port, request_file, message_file, digest, journal } => {
                let mut command = self.session_command(disk, &self.send_directory, session, *port, work)?;
                command.env("SIGNAL_DB_REQUEST", request_file).env("SIGNAL_NOTIFY_MESSAGE_FILE", message_file)
                    .env("SIGNAL_NOTIFY_ID", digest).env("SIGNAL_NOTIFY_JOURNAL", journal);
                command
            }
            Launch::Receive { session, port } => {
                let mut command = self.session_command(disk, &self.receive_directory, session, *port, work)?;
                // No credentials here: the account comes from the database nodes. The session ends
                // only when it fails or its step budget runs out; it is then started again.
                command.env("SIGNAL_LOCAL_RECEIVE", "1").env("SIGNAL_LOCAL_EXPECT", "1000000000").env("SIGNAL_LOCAL_EVENTS", "1");
                command
            }
            Launch::Serve { session, port, serve } => {
                let mut command = self.session_command(disk, &self.send_directory, session, *port, work)?;
                command.env("SIGNAL_SERVE_DIR", serve);
                command
            }
            Launch::Delete { request_file } => {
                let mut command = Command::new(&self.controller);
                command.args(["db-delete", &self.party.to_string(), &request_file.display().to_string()]);
                self.database_environment(&mut command, work);
                command
            }
        })
    }

    /// Start the controller for `launch` (working files in `work`, standard error to `log`) and
    /// supervise it to its end or to `limit`. Each line of its standard output goes to `on_line`;
    /// `on_start` gets its process id once it runs. `stall`: a controller whose log (its worker
    /// logs every operation) has not grown for this long is stopped like one at its time limit.
    /// A stop signal to the daemon stops it too.
    #[allow(clippy::too_many_arguments)]
    pub fn run(&self, disk: &Disk, launch: &Launch, work: &Path, log_file: LogFile, limit: Duration, stall: Option<Duration>,
        on_start: impl FnOnce(u32), mut on_line: impl FnMut(&str)) -> Result<Outcome, String> {
        let mut command = self.command(disk, launch, work)?;
        let LogFile { name: log_name, path: log_path, file } = log_file;
        let size_of = |path: &Path| std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);
        let started = Moment::now();
        let mut child = command.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(file).spawn().map_err(|e| format!("controller: {e}"))?;
        let pid = child.id();
        on_start(pid);
        let (mut grown, mut size) = (Moment::now(), 0u64);
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
        let mut exited: Option<(Option<i32>, Moment)> = None;
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
                    let stalled = stall.is_some_and(|stall| {
                        let now = size_of(&log_path);
                        if now != size {
                            (grown, size) = (Moment::now(), now);
                        }
                        grown.elapsed() > stall
                    });
                    if stalled {
                        log(&format!("{log_name}: no progress for {} s; stopping it", stall.map(|s| s.as_secs()).unwrap_or(0)));
                    }
                    if let Ok(Some(status)) = child.try_wait() {
                        exited = Some((status.code(), Moment::now()));
                    } else if started.elapsed() > limit || stalled || stopping() {
                        timed_out = !stopping();
                        kill_tree(pid);
                        let status = child.wait().ok();
                        exited = Some((status.and_then(|s| s.code()), Moment::now()));
                    }
                }
            }
        }
        Ok(Outcome { pid, code: exited.and_then(|e| e.0), timed_out, lines: collected, seconds: started.elapsed().as_secs_f64() })
    }
}

/// How a controller ended.
pub struct Outcome {
    pub pid: u32,
    pub code: Option<i32>,
    /// Stopped at its time limit or for want of progress (not by a stop signal).
    pub timed_out: bool,
    /// Its standard output (the first 4096 lines).
    pub lines: Vec<String>,
    pub seconds: f64,
}

/// A line of a controller's standard output.
#[derive(Clone, Debug, PartialEq)]
pub enum ControllerLine {
    /// `{"event":"ready","connections":N}`: the long-lived send session's connections are open.
    Ready { connections: Value },
    /// `{"event":"signup","id":"…"}` (receive session): a new contact is stored. Only for an id
    /// that is a u128 in decimal.
    Signup { id: String },
    /// `{"job":DIGEST,"status","results","unknown","not_yet_readable",…}`: one job of the
    /// long-lived send session, with its agreed per-id results.
    JobResult { job: String, report: Value },
    /// `{"passed":…,…}`: a session's final report.
    FinalReport(Value),
    /// Anything else (not JSON, or another shape).
    Other,
}

impl ControllerLine {
    pub fn parse(line: &str) -> ControllerLine {
        let Ok(value) = serde_json::from_str::<Value>(line) else { return ControllerLine::Other };
        if value["event"] == json!("ready") {
            return ControllerLine::Ready { connections: value["connections"].clone() };
        }
        if value["event"] == json!("signup") {
            return match value["id"].as_str().filter(|id| id.parse::<u128>().is_ok()) {
                Some(id) => ControllerLine::Signup { id: id.to_string() },
                None => ControllerLine::Other,
            };
        }
        if let Some(job) = value["job"].as_str() {
            return ControllerLine::JobResult { job: job.to_string(), report: value };
        }
        if value.get("passed").is_some() {
            return ControllerLine::FinalReport(value);
        }
        ControllerLine::Other
    }
}

// ---- Process trees.

/// The process table: (pid, parent pid, resident kilobytes).
fn process_table() -> Vec<(u32, u32, u64)> {
    let out = Command::new("ps").args(["-axo", "pid=,ppid=,rss="]).output().map(|o| String::from_utf8_lossy(&o.stdout).to_string()).unwrap_or_default();
    out.lines().filter_map(|line| {
        let mut parts = line.split_whitespace();
        Some((parts.next()?.parse().ok()?, parts.next()?.parse().ok()?, parts.next()?.parse().ok()?))
    }).collect()
}

/// The process and everything below it.
fn below(rows: &[(u32, u32, u64)], root: u32) -> Vec<u32> {
    let mut found = vec![root];
    let mut index = 0;
    while index < found.len() {
        let parent = found[index];
        let children: Vec<u32> = rows.iter().filter(|(pid, ppid, _)| *ppid == parent && !found.contains(pid)).map(|(pid, _, _)| *pid).collect();
        found.extend(children);
        index += 1;
    }
    found
}

/// Resident memory of a process and everything below it, in megabytes.
pub fn tree_megabytes(root: u32) -> u64 {
    let rows = process_table();
    let found = below(&rows, root);
    rows.iter().filter(|(pid, _, _)| found.contains(pid)).map(|(_, _, kb)| kb).sum::<u64>() / 1024
}

/// Ask the tree to stop, then kill what is left. (Children stay in the daemon's process group,
/// so whoever kills the group gets them too.)
pub fn kill_tree(root: u32) {
    let all = below(&process_table(), root);
    for pid in &all {
        unsafe { libc::kill(*pid as libc::pid_t, libc::SIGTERM); }
    }
    thread::sleep(Duration::from_millis(800));
    for pid in &all {
        unsafe { libc::kill(*pid as libc::pid_t, libc::SIGKILL); }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn controller_lines() {
        assert_eq!(ControllerLine::parse(r#"{"event":"ready","connections":3}"#), ControllerLine::Ready { connections: json!(3) });
        assert_eq!(ControllerLine::parse(r#"{"event":"signup","id":"340282366920938463463374607431768211454"}"#),
            ControllerLine::Signup { id: "340282366920938463463374607431768211454".into() });
        assert_eq!(ControllerLine::parse(r#"{"event":"signup","id":"-1"}"#), ControllerLine::Other);
        assert_eq!(ControllerLine::parse(r#"{"event":"signup","id":7}"#), ControllerLine::Other);
        let job = r#"{"job":"ab","status":"completed","results":[]}"#;
        assert_eq!(ControllerLine::parse(job), ControllerLine::JobResult { job: "ab".into(), report: serde_json::from_str(job).unwrap() });
        assert_eq!(ControllerLine::parse(r#"{"passed":false}"#), ControllerLine::FinalReport(json!({"passed": false})));
        assert_eq!(ControllerLine::parse("not json"), ControllerLine::Other);
        assert_eq!(ControllerLine::parse(r#"{"event":"other"}"#), ControllerLine::Other);
    }

    #[test]
    fn process_tree_below() {
        let rows = [(1, 0, 10), (2, 1, 10), (3, 2, 10), (4, 1, 10), (5, 9, 10)];
        let mut found = below(&rows, 1);
        found.sort();
        assert_eq!(found, vec![1, 2, 3, 4]);
    }
}
