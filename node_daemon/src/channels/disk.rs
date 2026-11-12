//! The files a daemon reads and writes.
//!
//! At start: the configuration and the files it names (the database network config, the peer key,
//! the bearer token), read once.
//!
//! Under the state directory (`state_directory`), and nowhere else:
//! - `work/{send,receive,delete}/`: a session's working directory (the hosts file, the request
//!   and message files it is given, the database client's scratch files);
//! - `work/send/serve/`: the long-lived send session's job directory (`jobs/`, `job.json`, `stop`);
//! - `journal/DIGEST.jsonl`: a notify's journal (written by the controller, removed here);
//! - `events.jsonl`: the signup events, appended, read back at start;
//! - `logs/NAME.log`: each controller's standard error.

use crate::Request;
use serde_json::{Value, json};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Duration;

fn error(path: &Path, e: std::io::Error) -> String {
    format!("{}: {e}", path.display())
}

fn write(path: &Path, bytes: &[u8]) -> Result<(), String> {
    fs::write(path, bytes).map_err(|e| error(path, e))
}

/// A configuration file, read at start: `node-daemon CONFIG.json`, the database network config,
/// the peer key file, the bearer token file.
pub fn read_setup(path: &str) -> Result<String, String> {
    fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))
}

/// A controller's log file (its standard error), open for writing.
pub struct LogFile {
    pub name: String,
    pub path: PathBuf,
    pub file: fs::File,
}

/// The state directory.
pub struct Disk {
    state: PathBuf,
}

impl Disk {
    pub fn new(state: PathBuf) -> Disk {
        Disk { state }
    }

    pub fn create(&self) -> Result<(), String> {
        fs::create_dir_all(&self.state).map_err(|e| error(&self.state, e))
    }

    // ---- Signup events.

    /// The events reported before a restart (one JSON object per line).
    pub fn load_events(&self) -> Vec<Value> {
        fs::read_to_string(self.state.join("events.jsonl")).unwrap_or_default().lines().filter_map(|line| serde_json::from_str(line).ok()).collect()
    }

    pub fn append_event(&self, entry: &Value) {
        if let Ok(mut file) = fs::OpenOptions::new().create(true).append(true).open(self.state.join("events.jsonl")) {
            let _ = writeln!(file, "{entry}");
        }
    }

    // ---- Journals.

    /// The journal of a notify (`journal/DIGEST.jsonl`), its directory created.
    pub fn journal(&self, digest: &str) -> Result<PathBuf, String> {
        let journals = self.state.join("journal");
        fs::create_dir_all(&journals).map_err(|e| error(&journals, e))?;
        Ok(journals.join(format!("{digest}.jsonl")))
    }

    pub fn remove_journal(&self, digest: &str) {
        let _ = fs::remove_file(self.state.join("journal").join(format!("{digest}.jsonl")));
    }

    /// Journals of notifies that can no longer be resumed (older than `age`).
    pub fn prune_journals(&self, age: Duration) {
        if let Ok(entries) = fs::read_dir(self.state.join("journal")) {
            for entry in entries.flatten() {
                let old = entry.metadata().and_then(|m| m.modified()).ok().and_then(|t| t.elapsed().ok()).is_some_and(|elapsed| elapsed > age);
                if old {
                    let _ = fs::remove_file(entry.path());
                }
            }
        }
    }

    // ---- Working directories and the files a session is given.

    /// `work/NAME`, created.
    pub fn work(&self, name: &str) -> Result<PathBuf, String> {
        let path = self.state.join("work").join(name);
        fs::create_dir_all(&path).map_err(|e| error(&path, e))?;
        Ok(path)
    }

    /// The controller's hosts file (`WORK/hosts`, one host per line).
    pub fn write_hosts(&self, work: &Path, hosts: &[String]) -> Result<PathBuf, String> {
        let path = work.join("hosts");
        write(&path, hosts.iter().map(|h| format!("{h}\n")).collect::<String>().as_bytes())?;
        Ok(path)
    }

    /// A one-notify session's input: `WORK/request.json` and `WORK/message.txt`.
    pub fn write_notify(&self, work: &Path, request: &Request, message: &str) -> Result<(PathBuf, PathBuf), String> {
        let (request_file, message_file) = (work.join("request.json"), work.join("message.txt"));
        write(&request_file, request.file_json().to_string().as_bytes())?;
        write(&message_file, message.as_bytes())?;
        Ok((request_file, message_file))
    }

    /// A delete's input, `WORK/request.json`, and where the database client writes its evidence
    /// (`WORK/delete.json`, removed first).
    pub fn write_delete(&self, work: &Path, request: &Request) -> Result<(PathBuf, PathBuf), String> {
        let request_file = work.join("request.json");
        write(&request_file, request.file_json().to_string().as_bytes())?;
        let evidence = work.join("delete.json");
        let _ = fs::remove_file(&evidence);
        Ok((request_file, evidence))
    }

    /// The database client's delete evidence, if it wrote a JSON file.
    pub fn read_delete_evidence(&self, path: &Path) -> Option<Value> {
        fs::read_to_string(path).ok().and_then(|text| serde_json::from_str::<Value>(&text).ok())
    }

    // ---- The long-lived send session's directory (`SIGNAL_SERVE_DIR`).

    /// `WORK/serve`, emptied, with `jobs/`.
    pub fn reset_serve(&self, work: &Path) -> Result<PathBuf, String> {
        let serve = work.join("serve");
        let _ = fs::remove_dir_all(&serve);
        fs::create_dir_all(serve.join("jobs")).map_err(|e| error(&serve, e))?;
        Ok(serve)
    }

    /// Give the session a notify: its request and text as files, then `job.json` (written whole:
    /// staged, then renamed into place).
    pub fn hand_over(&self, serve: &Path, digest: &str, request: &Request, message: &str, journal: &Path) -> Result<(), String> {
        let request_file = serve.join("jobs").join(format!("{digest}-request.json"));
        let message_file = serve.join("jobs").join(format!("{digest}-message.txt"));
        write(&request_file, request.file_json().to_string().as_bytes())?;
        write(&message_file, message.as_bytes())?;
        let staged = serve.join("job.staged");
        write(&staged, json!({"job": digest, "request": request_file, "message": message_file, "journal": journal}).to_string().as_bytes())?;
        fs::rename(&staged, serve.join("job.json")).map_err(|e| format!("job file: {e}"))
    }

    /// The job is reported: its `job.json` goes.
    pub fn remove_handed(&self, serve: &Path) {
        let _ = fs::remove_file(serve.join("job.json"));
    }

    /// Ask the session to end between jobs (`stop`, holding the reason).
    pub fn ask_to_stop(&self, serve: &Path, why: &str) -> bool {
        fs::write(serve.join("stop"), why).is_ok()
    }

    pub fn stop_asked(&self, serve: &Path) -> bool {
        serve.join("stop").exists()
    }

    // ---- Logs.

    /// `logs/NAME`, created empty.
    pub fn create_log(&self, name: &str) -> Result<LogFile, String> {
        let logs = self.state.join("logs");
        fs::create_dir_all(&logs).map_err(|e| error(&logs, e))?;
        let path = logs.join(name);
        let file = fs::File::create(&path).map_err(|e| format!("{name}: {e}"))?;
        Ok(LogFile { name: name.to_string(), path, file })
    }
}
