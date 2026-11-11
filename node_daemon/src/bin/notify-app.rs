//! A stand-in for the application server, and the reference for how a real one integrates.
//! See ../../README.md. It holds the application's keys (through `handoff_client`, the database
//! project's own tool, which does every signature), talks to BOTH node daemons, and accepts a
//! result only when the two nodes report the same one.
//!
//!   notify-app token  --db-client C --app-config APP_CONFIG --id ID --work DIR
//!   notify-app notify --daemons A,B --db-client C --key NOTIFY_KEY --ids 1,2 --message-file F --work DIR [--timeout S]
//!   notify-app delete --daemons A,B --db-client C --key NOTIFY_KEY --network NET --ids 1,2 --work DIR [--timeout S]
//!   notify-app events --daemons A,B [--after N] [--wait S] [--until-id ID]
//!   notify-app status --daemons A,B
//!
//! Prints one JSON object. Exit status 0: done and both nodes agree; 1: otherwise.

use node_daemon::{Kind, Request, call};
use serde_json::{Value, json};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::thread;
use std::time::{Duration, Instant};

struct Options(HashMap<String, String>);

impl Options {
    fn get(&self, name: &str) -> Result<&str, String> {
        self.0.get(name).map(String::as_str).ok_or(format!("--{name} is required"))
    }
    fn number(&self, name: &str, default: u64) -> u64 {
        self.0.get(name).and_then(|v| v.parse().ok()).unwrap_or(default)
    }
    fn daemons(&self) -> Result<Vec<String>, String> {
        let list: Vec<String> = self.get("daemons")?.split(',').map(str::to_string).collect();
        if list.len() != 2 {
            return Err("--daemons takes the two nodes' addresses".into());
        }
        Ok(list)
    }
    fn work(&self, name: &str) -> Result<PathBuf, String> {
        let directory = PathBuf::from(self.get("work")?);
        fs::create_dir_all(&directory).map_err(|e| format!("{}: {e}", directory.display()))?;
        Ok(directory.join(name))
    }
}

/// The database project's client: it signs with the application's keys.
fn db_client(options: &Options, arguments: &[&str]) -> Result<String, String> {
    let out = Command::new(options.get("db-client")?).args(arguments).output().map_err(|e| format!("database client: {e}"))?;
    if !out.status.success() {
        return Err(format!("database client {}: {}", arguments.first().unwrap_or(&""), String::from_utf8_lossy(&out.stderr).trim()));
    }
    Ok(String::from_utf8_lossy(&out.stdout).to_string())
}

/// The same request to both daemons at once; each reply, or why there is none.
fn both(daemons: &[String], request: &Value, timeout: Duration) -> Vec<Result<Value, String>> {
    let handles: Vec<_> = daemons.iter().map(|address| {
        let (address, request) = (address.clone(), request.clone());
        thread::spawn(move || call(&address, &request, timeout))
    }).collect();
    handles.into_iter().map(|h| h.join().unwrap_or(Err("request thread failed".into()))).collect()
}

fn describe(reply: &Result<Value, String>) -> Value {
    match reply {
        Ok(value) => value.clone(),
        Err(why) => json!({"ok": false, "error": why}),
    }
}

/// Submit a signed request to both nodes, wait for both results, compare them.
fn submit(options: &Options, kind: Kind, request_file: &PathBuf, message: Option<&str>) -> Result<(Value, bool), String> {
    let daemons = options.daemons()?;
    let file: Value = serde_json::from_str(&fs::read_to_string(request_file).map_err(|e| format!("{}: {e}", request_file.display()))?)
        .map_err(|e| format!("{}: {e}", request_file.display()))?;
    let request = Request::parse(kind, &file)?;
    let job = hex::encode(request.digest());
    let mut body = json!({"op": kind.name(), "request": file});
    if let Some(message) = message {
        body["message"] = json!(message);
    }
    let started = Instant::now();
    let accepted = both(&daemons, &body, Duration::from_secs(10));
    // Each node must have accepted it under the digest computed here.
    let taken: Vec<bool> = accepted.iter().map(|r| r.as_ref().is_ok_and(|v| v["ok"] == json!(true) && v["job"].as_str() == Some(&job))).collect();
    let timeout = options.number("timeout", 900);
    // Also from a node that refused: the other one will report that it was left alone.
    let waited: Vec<Value> = both(&daemons, &json!({"op": "wait", "job": job, "timeout": timeout}), Duration::from_secs(timeout + 10)).iter().map(describe).collect();
    let results: Vec<&Value> = waited.iter().map(|w| &w["result"]).collect();
    let done = waited.iter().all(|w| w["state"] == json!("done"));
    let agreed = done && taken.iter().all(|t| *t) && results[0]["result_digest"].is_string() && results[0]["result_digest"] == results[1]["result_digest"]
        && results[0]["job"].as_str() == Some(&job);
    let mut common = results[0].clone();
    if let Some(object) = common.as_object_mut() {
        object.remove("node");
    }
    let report = json!({
        "job": job, "agreed": agreed, "seconds": (started.elapsed().as_secs_f64() * 10.0).round() / 10.0,
        "result": if agreed { common } else { Value::Null },
        "nodes": [
            {"accepted": describe(&accepted[0]), "reply": waited[0]},
            {"accepted": describe(&accepted[1]), "reply": waited[1]},
        ],
    });
    Ok((report, agreed))
}

fn run(command: &str, options: &Options) -> Result<(Value, bool), String> {
    match command {
        // A signup token for a new id: the application gives it to the user, who sends it to
        // the account as their first Signal message.
        "token" => {
            let out = options.work(&format!("token-{}", options.get("id")?))?;
            db_client(options, &["sign-signup", "--app-config", options.get("app-config")?, "--id", options.get("id")?, "--out", &out.display().to_string()])?;
            let token = fs::read_to_string(&out).map_err(|e| format!("{}: {e}", out.display()))?;
            Ok((json!({"id": options.get("id")?, "token": token.trim()}), true))
        }
        "notify" => {
            let message_file = options.get("message-file")?;
            let message = fs::read_to_string(message_file).map_err(|e| format!("{message_file}: {e}"))?;
            let out = options.work("notify-request.json")?;
            db_client(options, &["sign-request", "--key", options.get("key")?, "--ids", options.get("ids")?, "--message-file", message_file,
                "--out", &out.display().to_string()])?;
            let (report, agreed) = submit(options, Kind::Notify, &out, Some(&message))?;
            let completed = agreed && report["result"]["status"] == json!("completed");
            Ok((report, completed))
        }
        "delete" => {
            let out = options.work("delete-request.json")?;
            db_client(options, &["sign-delete", "--key", options.get("key")?, "--ids", options.get("ids")?, "--out", &out.display().to_string()])?;
            let (mut report, agreed) = submit(options, Kind::Delete, &out, None)?;
            // Each node's evidence, checked here: enough database nodes signed that they
            // committed THIS request.
            let mut verified = Vec::new();
            for party in 0..2 {
                let evidence = &report["nodes"][party]["reply"]["result"]["node"]["evidence"];
                let file = options.work(&format!("delete-evidence-{party}.json"))?;
                fs::write(&file, evidence.to_string()).map_err(|e| format!("{}: {e}", file.display()))?;
                verified.push(evidence.is_object() && db_client(options, &["verify-signatures", "--network", options.get("network")?,
                    "--delete-output", &file.display().to_string(), "--delete-request", &out.display().to_string()]).is_ok());
            }
            let deleted = agreed && report["result"]["status"] == json!("deleted") && verified.iter().all(|v| *v);
            report["evidence_verified"] = json!(verified);
            Ok((report, deleted))
        }
        // The signups both nodes report (each event: the id that signed up).
        "events" => {
            let daemons = options.daemons()?;
            let after = options.number("after", 0);
            let deadline = Instant::now() + Duration::from_secs(options.number("wait", 0));
            let until = options.0.get("until-id").cloned();
            loop {
                let left = deadline.saturating_duration_since(Instant::now()).as_secs();
                let replies = both(&daemons, &json!({"op": "events", "after": after, "wait": if until.is_some() { left.min(5) } else { left }}), Duration::from_secs(left + 10));
                let ids = |reply: &Result<Value, String>| -> Vec<String> {
                    reply.as_ref().ok().and_then(|v| v["events"].as_array().cloned()).unwrap_or_default().iter()
                        .filter(|e| e["event"] == json!("signup")).filter_map(|e| e["id"].as_str().map(str::to_string)).collect()
                };
                let (first, second) = (ids(&replies[0]), ids(&replies[1]));
                // An id counts as signed up when both nodes report it.
                let signups: Vec<String> = first.iter().filter(|id| second.contains(id)).cloned().collect();
                let found = until.as_ref().is_none_or(|id| signups.contains(id));
                if found || Instant::now() >= deadline {
                    let report = json!({"signups": signups, "agreed": first == second, "nodes": [describe(&replies[0]), describe(&replies[1])]});
                    return Ok((report, found && replies.iter().all(|r| r.is_ok())));
                }
                thread::sleep(Duration::from_millis(300));
            }
        }
        "status" => {
            let replies = both(&options.daemons()?, &json!({"op": "status"}), Duration::from_secs(5));
            Ok((json!({"nodes": [describe(&replies[0]), describe(&replies[1])]}), replies.iter().all(|r| r.is_ok())))
        }
        _ => Err("commands: token, notify, delete, events, status".into()),
    }
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let mut options = HashMap::new();
    let mut index = 1;
    while index + 1 < arguments.len() {
        if let Some(name) = arguments[index].strip_prefix("--") {
            options.insert(name.to_string(), arguments[index + 1].clone());
        }
        index += 2;
    }
    let outcome = match arguments.first() {
        Some(command) => run(command, &Options(options)),
        None => Err("usage: notify-app token|notify|delete|events|status --option value ...".into()),
    };
    match outcome {
        Ok((report, good)) => {
            println!("{report}");
            std::process::exit(if good { 0 } else { 1 });
        }
        Err(why) => {
            println!("{}", json!({"error": why}));
            std::process::exit(1);
        }
    }
}
