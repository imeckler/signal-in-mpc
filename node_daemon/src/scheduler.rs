//! The daemon's state machine: requests of the application, their agreement with the other
//! daemon, the queue, and the sessions that run them. Every input and output goes through
//! `channels` (see `channels/mod.rs` for the list).

use crate::channels::application::{AppReply, AppRequest, SendStatus, Status};
use crate::channels::controller::{ControllerLine, Launch, Outcome, kill_tree, tree_megabytes};
use crate::channels::disk::Disk;
use crate::channels::host::{Moment, log, random_bytes, sleep, stopping, unix_now};
use crate::channels::peer::{Link, PeerMessage, PeerReply};
use crate::config::Config;
use crate::{Kind, MAX_MESSAGE_BYTES, Request, result_digest, sha256};
use serde_json::{Value, json};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Condvar, Mutex, MutexGuard};
use std::thread;
use std::time::Duration;

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
    received: Moment,
    /// The leader's first attempt to start it that the peer did not accept.
    start_failed: Option<Moment>,
    result: Option<Value>,
    finished: Option<Moment>,
    /// Long-lived sessions it was handed to.
    attempts: u32,
}

/// This node's long-lived send session (both nodes run one under the same name).
struct SendSession {
    name: String,
    /// The directory the controller takes jobs from (`SIGNAL_SERVE_DIR`).
    serve: PathBuf,
    pid: Option<u32>,
    /// Its connections are open (the controller's `ready` line).
    ready: bool,
    /// The notify it is serving.
    job: Option<String>,
    started: Moment,
    messages: u64,
    jobs: u64,
    /// Why this node asked it to end (DIR/stop), once asked.
    stop_asked: Option<String>,
    rss_checked: Option<Moment>,
    rss_megabytes: u64,
    rss_logged: Option<(Moment, u64)>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    /// A one-request controller (a notify in the per-request mode, a delete).
    Job,
    Receive,
    Send,
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
    send: Option<SendSession>,
    send_generation: u64,
}

/// At most the first 16 bytes (of a digest or session name, for the log).
fn short(text: &str) -> &str {
    let mut end = text.len().min(16);
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    &text[..end]
}

/// Per requested id, from what the two controllers agreed on (they compare a digest of these
/// before reporting them): the send's result, or that the database nodes do not have the id.
fn notify_results(request: &Request, report: &Value) -> Vec<Value> {
    let listed = |name: &str| -> Vec<String> {
        report.get(name).and_then(Value::as_array).map(|l| l.iter().filter_map(|v| v.as_str().map(str::to_string)).collect()).unwrap_or_default()
    };
    let (unknown, waiting) = (listed("unknown"), listed("not_yet_readable"));
    let rows = report.get("results").and_then(Value::as_array).cloned().unwrap_or_default();
    request.ids.iter().map(|id| {
        let id = id.to_string();
        let row = rows.iter().find(|r| r["id"].as_str() == Some(&id) && r["message"].as_u64() == Some(0));
        let (result, reason) = match row {
            Some(row) => (row["result"].as_str().unwrap_or("fault").to_string(), row["reason"].as_str().unwrap_or("").to_string()),
            None if unknown.contains(&id) => ("unknown contact".to_string(), String::new()),
            None if waiting.contains(&id) => ("retry later".to_string(), "not readable until the database nodes' next epoch".to_string()),
            None => ("fault".to_string(), "the session reported no result for this id".to_string()),
        };
        json!({"id": id, "result": result, "reason": reason})
    }).collect()
}

pub struct Daemon {
    pub config: Config,
    disk: Disk,
    /// To the other daemon.
    link: Link,
    shared: Mutex<Shared>,
    changed: Condvar,
}

impl Daemon {
    /// `events`: the signup events reported before a restart.
    pub fn new(config: Config, disk: Disk, events: Vec<Value>) -> Arc<Daemon> {
        let link = Link { address: config.peer.clone(), key: config.peer_key.clone(), party: config.party };
        Arc::new(Daemon { config, disk, link, shared: Mutex::new(Shared { events, ..Shared::default() }), changed: Condvar::new() })
    }

    fn lock(&self) -> MutexGuard<'_, Shared> {
        self.shared.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    pub fn leader(&self) -> bool {
        self.config.party == 0
    }

    // ---- Requests of the application.

    pub fn application(&self, request: AppRequest) -> AppReply {
        match request {
            AppRequest::Notify { request, message } => self.submit(Kind::Notify, &request, message.as_deref()),
            AppRequest::Delete { request } => self.submit(Kind::Delete, &request, None),
            AppRequest::Wait { job, timeout } => self.wait(&job, timeout),
            AppRequest::Events { after, wait } => self.events(after, wait),
            AppRequest::Status => self.status(),
        }
    }

    fn submit(&self, kind: Kind, request: &Value, text: Option<&str>) -> AppReply {
        let request = match Request::parse(kind, request) {
            Ok(request) => request,
            Err(why) => return AppReply::Refused(why),
        };
        // The application's signature and the freshness rule, exactly as the database nodes
        // will check them, before anything else happens.
        if let Err(why) = request.verify_signature(&self.config.notify_key).and_then(|_| request.check_freshness(unix_now(), self.config.max_age)) {
            return AppReply::Refused(why);
        }
        let text = match kind {
            Kind::Delete => None,
            Kind::Notify => {
                let Some(text) = text else { return AppReply::Refused("notify: message is missing".into()) };
                if text.is_empty() || text.len() > MAX_MESSAGE_BYTES {
                    return AppReply::Refused(format!("notify: the message must be 1..{MAX_MESSAGE_BYTES} bytes"));
                }
                if sha256(text.as_bytes()) != request.message_hash {
                    return AppReply::Refused("notify: the message is not the one the request was signed for".into());
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
                return AppReply::Accepted { job: digest, state: job.stage.name(), known: true };
            }
        }
        log(&format!("{} {} received: {} ids", kind.name(), short(&digest), request.ids.len()));
        shared.jobs.insert(digest.clone(), Job { request, message: text, stage: Stage::Received, received: Moment::now(), start_failed: None, result: None,
            finished: None, attempts: 0 });
        self.changed.notify_all();
        AppReply::Accepted { job: digest, state: "received", known: false }
    }

    fn wait(&self, digest: &str, timeout: u64) -> AppReply {
        let deadline = Moment::now().after(Duration::from_secs(timeout.min(3600)));
        let mut shared = self.lock();
        loop {
            match shared.jobs.get(digest) {
                None => return AppReply::Refused("unknown job".into()),
                Some(job) if job.stage == Stage::Done => return AppReply::Done { job: digest.to_string(), result: job.result.clone() },
                Some(job) => {
                    let Some(left) = deadline.remaining() else { return AppReply::Pending { job: digest.to_string(), state: job.stage.name() } };
                    shared = self.changed.wait_timeout(shared, left.min(Duration::from_secs(1))).unwrap_or_else(|p| p.into_inner()).0;
                }
            }
        }
    }

    fn events(&self, after: u64, wait: u64) -> AppReply {
        let after = after as usize;
        let deadline = Moment::now().after(Duration::from_secs(wait.min(3600)));
        let mut shared = self.lock();
        loop {
            match deadline.remaining() {
                Some(left) if shared.events.len() <= after => {
                    shared = self.changed.wait_timeout(shared, left.min(Duration::from_secs(1))).unwrap_or_else(|p| p.into_inner()).0;
                }
                _ => return AppReply::Events { events: shared.events.iter().skip(after).cloned().collect(), next: shared.events.len() },
            }
        }
    }

    fn status(&self) -> AppReply {
        let shared = self.lock();
        let count = |stage: Stage| shared.jobs.values().filter(|j| j.stage == stage).count();
        AppReply::Status(Status {
            party: self.config.party,
            received: count(Stage::Received),
            agreed: count(Stage::Agreed),
            running: count(Stage::Running),
            done: count(Stage::Done),
            events: shared.events.len(),
            receive_session_running: shared.receive_child.is_some(),
            receive_sessions_started: shared.receive_generation,
            send_sessions_started: shared.send_generation,
            send_session: shared.send.as_ref().map(|s| SendStatus { pid: s.pid, ready: s.ready, serving: s.job.is_some(), messages: s.messages,
                jobs: s.jobs, seconds: s.started.elapsed().as_secs(), megabytes: s.rss_megabytes, ending: s.stop_asked.clone() }),
        })
    }

    // ---- Messages of the other daemon (authenticated and decoded before they get here).

    pub fn peer(self: &Arc<Self>, message: PeerMessage) -> PeerReply {
        match message {
            PeerMessage::Ping => PeerReply::yes(),
            // "Do you hold this request too?" Yes only for a request this daemon verified itself.
            PeerMessage::Agree { job: digest } => {
                let mut shared = self.lock();
                match shared.jobs.get_mut(&digest) {
                    Some(job) if job.stage == Stage::Received || job.stage == Stage::Agreed => {
                        job.stage = Stage::Agreed;
                        PeerReply::yes()
                    }
                    _ => PeerReply::no(),
                }
            }
            PeerMessage::Start { job: digest, session, port } => {
                if self.leader() {
                    return PeerReply::refused("only party 0 starts sessions");
                }
                let notify = self.lock().jobs.get(&digest).is_some_and(|job| job.request.kind == Kind::Notify);
                if self.config.long_lived && notify {
                    // Hand the notify to this node's long-lived session, which must be the one
                    // party 0 names and be idle.
                    {
                        let shared = self.lock();
                        if shared.busy || !shared.send.as_ref().is_some_and(|s| s.name == session && s.job.is_none() && s.stop_asked.is_none()) {
                            return PeerReply::busy(Some("not this node's idle send session"));
                        }
                        let fresh = match shared.jobs.get(&digest) {
                            Some(job) if job.stage == Stage::Received || job.stage == Stage::Agreed => job.request.check_freshness(unix_now(), self.config.max_age).is_ok(),
                            _ => return PeerReply::refused("not a request this node holds"),
                        };
                        if !fresh {
                            return PeerReply::refused("expired");
                        }
                    }
                    return match self.hand_over(&digest) {
                        Ok(()) => PeerReply::yes(),
                        Err(why) => {
                            log(&format!("notify {}: {why}", short(&digest)));
                            PeerReply::refused("this node could not hand the request to its session")
                        }
                    };
                }
                let Some(port) = port else { return PeerReply::refused("peer-start: session and port") };
                let mut shared = self.lock();
                if shared.busy {
                    return PeerReply::busy(None);
                }
                let fresh = match shared.jobs.get(&digest) {
                    Some(job) if job.stage == Stage::Received || job.stage == Stage::Agreed => job.request.check_freshness(unix_now(), self.config.max_age).is_ok(),
                    _ => return PeerReply::refused("not a request this node holds"),
                };
                if !fresh {
                    return PeerReply::refused("expired");
                }
                if let Some(job) = shared.jobs.get_mut(&digest) {
                    job.stage = Stage::Running;
                }
                shared.busy = true;
                drop(shared);
                self.start_job(digest, session, port as u64);
                PeerReply::yes()
            }
            PeerMessage::Receive { session, port } => {
                if self.leader() || !self.config.receive {
                    return PeerReply::refused("no receive session here");
                }
                let old = self.lock().receive_child.take();
                if let Some(pid) = old {
                    kill_tree(pid);
                }
                let daemon = self.clone();
                thread::spawn(move || daemon.receive_session(&session, port as u64));
                PeerReply::yes()
            }
            // Party 0 starts a (new) long-lived send session; this node's previous one goes.
            PeerMessage::Serve { session, port } => {
                if self.leader() || !self.config.long_lived {
                    return PeerReply::refused("no long-lived send session here");
                }
                let old = self.lock().send.as_ref().and_then(|s| s.pid);
                if let Some(pid) = old {
                    kill_tree(pid);
                }
                let daemon = self.clone();
                thread::spawn(move || daemon.serve_session(&session, port as u64));
                PeerReply::yes()
            }
            // The other node's send session ended (failed, stopped, or was killed): this node's
            // session of the same name cannot go on, and is ended now instead of at the workers'
            // bounded wait (TLS_WORKER_PEER_WAIT).
            PeerMessage::Ended { session } => {
                let pid = self.lock().send.as_ref().filter(|s| s.name == session).and_then(|s| s.pid);
                if let Some(pid) = pid {
                    log(&format!("send session {}: the other node's ended; ending this one", short(&session)));
                    kill_tree(pid);
                }
                PeerReply::yes()
            }
            // Party 0 gave a notify up (no attempts left): the same status here.
            PeerMessage::Finish { job: digest } => {
                let waiting = self.lock().jobs.get(&digest).is_some_and(|job| job.stage == Stage::Received || job.stage == Stage::Agreed);
                if waiting {
                    self.finish(&digest, "failed", json!([]), "the sessions it was handed to ended before it completed", None, 0.0);
                }
                PeerReply::yes()
            }
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
        job.finished = Some(Moment::now());
        shared.queue.retain(|d| d != digest);
        log(&format!("{} {} done: {status}{}", kind.name(), short(digest), if detail.is_empty() { String::new() } else { format!(" ({detail})") }));
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

    /// Run a controller to its end or to `limit` (`channels::controller`), keeping track of it
    /// as this daemon's child (and as the receive or send session's, for `role`).
    #[allow(clippy::too_many_arguments)]
    fn supervise(&self, launch: Launch, work: &Path, log_name: &str, limit: Duration, role: Role, stall: Option<Duration>,
        on_line: impl FnMut(&str)) -> Result<Outcome, String> {
        let log_file = self.disk.create_log(log_name)?;
        let outcome = self.config.session.run(&self.disk, &launch, work, log_file, limit, stall, |pid| {
            let mut shared = self.lock();
            shared.children.push(pid);
            match role {
                Role::Receive => shared.receive_child = Some(pid),
                Role::Send => if let Some(session) = shared.send.as_mut() { session.pid = Some(pid) },
                Role::Job => {}
            }
        }, on_line)?;
        let mut shared = self.lock();
        shared.children.retain(|p| *p != outcome.pid);
        if shared.receive_child == Some(outcome.pid) {
            shared.receive_child = None;
        }
        Ok(outcome)
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
            log(&format!("{} {}: {why}", request.kind.name(), short(digest)));
            self.finish(digest, "failed", json!([]), "the session could not be run on this node", None, 0.0);
        }
    }

    fn run_notify(&self, digest: &str, request: &Request, message: &str, session: &str, port: u64) -> Result<(), String> {
        let work = self.disk.work("send")?;
        let (request_file, message_file) = self.disk.write_notify(&work, request, message)?;
        // The journal of what this notify settled, owned by the daemon: one file per notify,
        // named by the request's digest, removed when the notify completes.
        let journal = self.disk.journal(digest)?;
        let launch = Launch::Notify { session: session.to_string(), port, request_file, message_file, digest: digest.to_string(), journal };
        let limit = Duration::from_secs(self.config.send_seconds + self.config.send_seconds_per_id * request.ids.len() as u64);
        log(&format!("notify {} session {} starts on port {port}", short(digest), short(session)));
        let outcome = self.supervise(launch, &work, &format!("send-{}.log", short(digest)), limit, Role::Job, None, |_| {})?;
        let report = outcome.lines.iter().rev().find_map(|line| match ControllerLine::parse(line) {
            ControllerLine::FinalReport(report) => Some(report),
            _ => None,
        });
        let passed = outcome.code == Some(0) && report.as_ref().is_some_and(|r| r["passed"] == json!(true));
        let Some(report) = report.filter(|_| passed) else {
            let detail = if outcome.timed_out { "the session was stopped at its time limit".to_string() } else { format!("the session ended with status {:?}", outcome.code) };
            self.finish(digest, "failed", json!([]), &detail, None, outcome.seconds);
            return Ok(());
        };
        let results = notify_results(request, &report);
        self.disk.remove_journal(digest);
        self.finish(digest, "completed", json!(results), "", None, outcome.seconds);
        Ok(())
    }

    fn run_delete(&self, digest: &str, request: &Request) -> Result<(), String> {
        let work = self.disk.work("delete")?;
        let (request_file, evidence_file) = self.disk.write_delete(&work, request)?;
        let outcome = self.supervise(Launch::Delete { request_file }, &work, &format!("delete-{}.log", short(digest)),
            Duration::from_secs(self.config.delete_seconds), Role::Job, None, |_| {})?;
        // The database client's report: which nodes committed, with each node's signature over
        // the request's digest. Public, and checkable by anyone with the network config.
        let evidence = self.disk.read_delete_evidence(&evidence_file);
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
            let work = self.disk.work("receive")?;
            let generation = {
                let mut shared = self.lock();
                shared.receive_generation += 1;
                shared.receive_generation
            };
            log(&format!("receive session {} starts on port {port}", short(session)));
            let launch = Launch::Receive { session: session.to_string(), port };
            self.supervise(launch, &work, &format!("receive-{generation}.log"), Duration::from_secs(u64::MAX / 4), Role::Receive, None, |line| {
                let ControllerLine::Signup { id } = ControllerLine::parse(line) else { return };
                let mut shared = self.lock();
                let entry = json!({"seq": shared.events.len() + 1, "event": "signup", "id": id, "at": unix_now()});
                self.disk.append_event(&entry);
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

    // ---- The long-lived send session (README, "The long-lived send session").

    /// A notify handed to a session that ended before reporting it: back in the queue (party 0
    /// sends it to the next session, which resumes from the journals) unless no attempts are left.
    fn requeue(&self, shared: &mut Shared, digest: &str) {
        let Some(job) = shared.jobs.get_mut(digest) else { return };
        if job.stage != Stage::Running {
            return;
        }
        job.stage = Stage::Agreed;
        if self.leader() && !shared.queue.iter().any(|d| d == digest) {
            shared.queue.insert(0, digest.to_string());
        }
        log(&format!("notify {}: its session ended before it completed (attempt {})", short(digest), job.attempts));
    }

    /// This node's long-lived send session, to its end. Both nodes run it under the name party 0
    /// chose. `true`: it ended because a daemon asked it to (a planned restart).
    fn serve_session(&self, session: &str, port: u64) -> bool {
        let generation = {
            let mut shared = self.lock();
            shared.send_generation += 1;
            shared.send_generation
        };
        let run = || -> Result<Outcome, String> {
            let work = self.disk.work("send")?;
            let serve = self.disk.reset_serve(&work)?;
            {
                let mut shared = self.lock();
                let previous = shared.send.replace(SendSession { name: session.to_string(), serve: serve.clone(), pid: None, ready: false, job: None,
                    started: Moment::now(), messages: 0, jobs: 0, stop_asked: None, rss_checked: None, rss_megabytes: 0, rss_logged: None });
                if let Some(digest) = previous.and_then(|s| s.job) {
                    self.requeue(&mut shared, &digest);
                }
            }
            log(&format!("send session {} starts on port {port} (long-lived)", short(session)));
            let stall = Duration::from_secs(self.config.stall_seconds.max(60));
            let launch = Launch::Serve { session: session.to_string(), port, serve };
            self.supervise(launch, &work, &format!("send-session-{generation}.log"), Duration::from_secs(u64::MAX / 4), Role::Send, Some(stall),
                |line| self.send_line(session, line))
        };
        let outcome = run();
        let mut planned = false;
        {
            let mut shared = self.lock();
            if shared.send.as_ref().is_some_and(|s| s.name == session) {
                let ended = shared.send.take();
                planned = ended.as_ref().is_some_and(|s| s.stop_asked.is_some() || self.disk.stop_asked(&s.serve));
                if let Some(digest) = ended.as_ref().and_then(|s| s.job.clone()) {
                    self.requeue(&mut shared, &digest);
                }
                if let Some(ended) = ended {
                    log(&format!("send session {} ended: {} jobs, {} messages in {} s{}", short(session), ended.jobs, ended.messages,
                        ended.started.elapsed().as_secs(), ended.stop_asked.map(|why| format!(" (asked to end: {why})")).unwrap_or_default()));
                }
            }
            self.changed.notify_all();
        }
        match outcome {
            Ok(outcome) => log(&format!("send session {} exited with status {:?}{}", short(session), outcome.code,
                if outcome.timed_out { " (stopped: no progress)" } else { "" })),
            Err(why) => log(&format!("send session: {why}")),
        }
        // The other node's session of this name is waiting for this one's worker: end it now.
        // (After a planned end both controllers end by themselves.)
        if !planned {
            let _ = self.link.call(&PeerMessage::Ended { session: session.to_string() });
        }
        planned
    }

    /// A line of the send session's standard output: `ready`, or one job's agreed results.
    fn send_line(&self, session: &str, line: &str) {
        let (digest, report) = match ControllerLine::parse(line) {
            ControllerLine::Ready { connections } => {
                let mut shared = self.lock();
                if let Some(s) = shared.send.as_mut().filter(|s| s.name == session) {
                    s.ready = true;
                    log(&format!("send session {} ready ({connections} connections)", short(session)));
                }
                self.changed.notify_all();
                return;
            }
            ControllerLine::JobResult { job, report } => (job, report),
            _ => return,
        };
        let (request, serve) = {
            let shared = self.lock();
            (shared.jobs.get(&digest).map(|j| j.request.clone()), shared.send.as_ref().filter(|s| s.name == session).map(|s| s.serve.clone()))
        };
        let Some(request) = request else { return };
        let results = notify_results(&request, &report);
        self.disk.remove_journal(&digest);
        if let Some(serve) = serve {
            self.disk.remove_handed(&serve);
        }
        {
            let mut shared = self.lock();
            if let Some(s) = shared.send.as_mut().filter(|s| s.name == session) {
                if s.job.as_deref() == Some(digest.as_str()) {
                    s.job = None;
                }
                s.messages += report["messages"].as_u64().unwrap_or(0);
                s.jobs += 1;
            }
        }
        let seconds = report["milliseconds"].as_f64().unwrap_or(0.0) / 1000.0;
        self.finish(&digest, "completed", json!(results), "", None, seconds);
    }

    /// Give the session a notify: its request and text as files, then DIR/job.json (written whole).
    fn hand_over(&self, digest: &str) -> Result<(), String> {
        let (request, message, serve) = {
            let shared = self.lock();
            let job = shared.jobs.get(digest).ok_or("unknown request")?;
            let serve = shared.send.as_ref().ok_or("no send session")?.serve.clone();
            (job.request.clone(), job.message.clone().unwrap_or_default(), serve)
        };
        // The journal of what this notify settled, owned by the daemon: one file per notify,
        // named by the request's digest, removed when the notify completes.
        let journal = self.disk.journal(digest)?;
        self.disk.hand_over(&serve, digest, &request, &message, &journal)?;
        let mut shared = self.lock();
        if let Some(job) = shared.jobs.get_mut(digest) {
            job.stage = Stage::Running;
            job.attempts += 1;
        }
        if let Some(s) = shared.send.as_mut() {
            s.job = Some(digest.to_string());
        }
        shared.queue.retain(|d| d != digest);
        self.changed.notify_all();
        Ok(())
    }

    /// Wait `pause` seconds in steps of 200 ms; `false` when the daemon is asked to stop.
    fn pause(seconds: u64) -> bool {
        for _ in 0..seconds * 5 {
            if stopping() {
                return false;
            }
            sleep(Duration::from_millis(200));
        }
        true
    }

    /// Party 0: keep one long-lived send session running on both nodes; when it ends, start the next.
    fn keep_sending(self: &Arc<Self>) {
        let mut pause = 2u64;
        while !stopping() {
            let Ok((session, count)) = self.session_name() else { return };
            let port = self.config.port_base + 40 * (count % 8);
            let started = Moment::now();
            let planned = match self.link.call(&PeerMessage::Serve { session: session.clone(), port: port as u16 }) {
                Ok(reply) if reply.ok => self.serve_session(&session, port),
                _ => false,
            };
            // A session that ended at once is not restarted in a tight loop; a planned end is
            // followed at once (the other node's session ends at the same tick).
            pause = if planned { 1 } else if started.elapsed() > Duration::from_secs(120) { 2 } else { (pause * 2).min(60) };
            if !Self::pause(pause) {
                return;
            }
        }
    }

    /// Both nodes: ask the send session to end, between jobs, when it reached a limit (messages,
    /// age, memory). Either node asking is enough: the two controllers end together.
    fn maintain_send(&self) {
        let mut shared = self.lock();
        let Some(s) = shared.send.as_mut() else { return };
        if !s.ready || s.stop_asked.is_some() {
            return;
        }
        if let Some(pid) = s.pid.filter(|_| s.rss_checked.is_none_or(|at| at.elapsed() > Duration::from_secs(10))) {
            s.rss_checked = Some(Moment::now());
            s.rss_megabytes = tree_megabytes(pid);
            // Logged when it sent something since, and every five minutes while idle.
            if s.rss_logged.is_none_or(|(at, messages)| messages != s.messages || at.elapsed() > Duration::from_secs(300)) {
                s.rss_logged = Some((Moment::now(), s.messages));
                log(&format!("send session memory: {} MB after {} messages, {} jobs, {} s", s.rss_megabytes, s.messages, s.jobs, s.started.elapsed().as_secs()));
            }
        }
        if s.job.is_some() {
            return;
        }
        let c = &self.config;
        let why = if c.max_messages > 0 && s.messages >= c.max_messages {
            format!("{} messages", s.messages)
        } else if c.max_seconds > 0 && s.started.elapsed() >= Duration::from_secs(c.max_seconds) {
            format!("{} s old", s.started.elapsed().as_secs())
        } else if c.max_megabytes > 0 && s.rss_megabytes >= c.max_megabytes {
            format!("{} MB resident", s.rss_megabytes)
        } else {
            return;
        };
        if self.disk.ask_to_stop(&s.serve, &why) {
            log(&format!("send session: asked to end ({why})"));
            s.stop_asked = Some(why);
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
                    if job.attempts > 0 {
                        // Handed to a session that ended before it completed; no further one in time.
                        Some((digest.clone(), "failed", "its session ended before it completed, and the request's lifetime is over"))
                    } else {
                        Some((digest.clone(), "expired", "the request's lifetime ended before its turn came"))
                    }
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
            if self.link.call(&PeerMessage::Agree { job: digest.clone() }).is_ok_and(|reply| reply.ok) {
                let mut shared = self.lock();
                if let Some(job) = shared.jobs.get_mut(&digest).filter(|job| job.stage == Stage::Received) {
                    job.stage = Stage::Agreed;
                    shared.queue.push(digest.clone());
                    log(&format!("request {} confirmed by the other node", short(&digest)));
                }
            }
        }
        let next = {
            let shared = self.lock();
            if shared.busy || shared.send.as_ref().is_some_and(|s| s.job.is_some()) { None } else { shared.queue.first().cloned() }
        };
        let Some(digest) = next else { return };
        let (notify, attempts, fresh) = self.lock().jobs.get(&digest).map(|job| (job.request.kind == Kind::Notify, job.attempts,
            job.request.issued_at + self.config.max_age >= unix_now() + 5)).unwrap_or((false, 0, false));
        if self.config.long_lived && notify {
            // To the long-lived session, once it is ready (both nodes'), one notify at a time.
            if attempts >= self.config.attempts {
                self.finish(&digest, "failed", json!([]), "the sessions it was handed to ended before it completed", None, 0.0);
                let _ = self.link.call(&PeerMessage::Finish { job: digest.clone() });
                return;
            }
            let session = self.lock().send.as_ref().filter(|s| s.ready && s.job.is_none() && s.stop_asked.is_none()).map(|s| s.name.clone());
            let Some(session) = session else { return };
            if !fresh {
                return;   // `expire` reports it
            }
            if self.link.call(&PeerMessage::Start { job: digest.clone(), session, port: None }).is_ok_and(|r| r.ok) {
                if let Err(why) = self.hand_over(&digest) {
                    // The other node's session holds it and this one cannot: both sessions end
                    // (`peer-ended`), and the next one is handed it again.
                    log(&format!("notify {}: {why}", short(&digest)));
                    let pid = self.lock().send.as_ref().and_then(|s| s.pid);
                    if let Some(pid) = pid {
                        kill_tree(pid);
                    }
                }
            }
            return;
        }
        let Ok((session, count)) = self.session_name() else { return };
        let port = self.config.port_base + 40 * (count % 8);
        let reply = self.link.call(&PeerMessage::Start { job: digest.clone(), session: session.clone(), port: Some(port as u16) });
        if reply.as_ref().is_ok_and(|r| r.ok) {
            let mut shared = self.lock();
            shared.queue.retain(|d| *d != digest);
            shared.busy = true;
            if let Some(job) = shared.jobs.get_mut(&digest) {
                job.stage = Stage::Running;
            }
            drop(shared);
            self.start_job(digest, session, port);
        } else if !reply.as_ref().is_ok_and(|r| r.busy) {
            // The other node is unreachable or refuses: tried again until the confirmation time is used up.
            let mut shared = self.lock();
            let first = shared.jobs.get_mut(&digest).map(|job| *job.start_failed.get_or_insert_with(Moment::now));
            drop(shared);
            if first.is_some_and(|at| at.elapsed() > Duration::from_secs(self.config.agree_seconds)) {
                self.finish(&digest, "failed", json!([]), "the other node did not start the session", None, 0.0);
            }
        }
    }

    /// Party 0: keep one receive session running; when it ends, start the next (both nodes).
    fn keep_receiving(self: &Arc<Self>) {
        let mut pause = 2u64;
        while !stopping() {
            let Ok((session, count)) = self.session_name() else { return };
            let port = self.config.port_base + 320 + 40 * (count % 8);
            let started = Moment::now();
            if let Ok(reply) = self.link.call(&PeerMessage::Receive { session: session.clone(), port: port as u16 }) {
                if reply.ok {
                    self.receive_session(&session, port);
                }
            }
            // A session that ended at once is not restarted in a tight loop.
            pause = if started.elapsed() > Duration::from_secs(120) { 2 } else { (pause * 2).min(60) };
            if !Self::pause(pause) {
                return;
            }
        }
    }

    /// The daemon's own work until a stop signal: party 0 keeps the receive and send sessions
    /// running and schedules; both expire late requests and watch their send session. Then every
    /// controller it started is stopped.
    pub fn run(self: &Arc<Self>) {
        if self.leader() && self.config.receive {
            let daemon = self.clone();
            thread::spawn(move || daemon.keep_receiving());
        }
        if self.leader() && self.config.long_lived {
            let daemon = self.clone();
            thread::spawn(move || daemon.keep_sending());
        }
        while !stopping() {
            self.expire();
            self.maintain_send();
            if self.leader() {
                self.schedule();
            }
            sleep(Duration::from_millis(200));
        }
        log("stopping");
        let children = self.lock().children.clone();
        for pid in children {
            kill_tree(pid);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn results_per_id() {
        let request = Request { kind: Kind::Notify, ids: vec![1, 2, 3, 4], message_hash: [0; 32], nonce: [0; 16], issued_at: 0, signature: [0; 64] };
        let report = json!({"results": [{"message": 0, "id": "1", "result": "delivered", "reason": ""}, {"message": 1, "id": "4", "result": "delivered"}],
            "unknown": ["2"], "not_yet_readable": ["3"]});
        let results = notify_results(&request, &report);
        assert_eq!(results[0], json!({"id": "1", "result": "delivered", "reason": ""}));
        assert_eq!(results[1]["result"], json!("unknown contact"));
        assert_eq!(results[2]["result"], json!("retry later"));
        assert_eq!(results[3]["result"], json!("fault"));
        assert_eq!(short("abcdefghijklmnopqrstuvwxyz"), "abcdefghijklmnop");
        assert_eq!(short("ab"), "ab");
        assert_eq!(short("ééééééééé"), "éééééééé");
    }
}
