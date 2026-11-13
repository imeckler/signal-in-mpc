//! End-to-end check of pipe operation 93 with the REAL engines: the `cargo test` form of
//! tests/e2e_batches.py (which stays). Two node-worker processes (this build's binary) run the
//! Lean-generated flows of tests/engine_vectors.txt (random-joint, upgrade-public, bool, field,
//! xor) while this test plays the controller's side of both pipes and compares every reply with
//! the reply the Lean model computes for honest parties. Then one batch that `check` refuses (an
//! exchange with label 0): both workers must reject it, and stay terminal.
//!
//! Feature `e2e` only (it implies `engine`, so it is built only where the engine library is):
//! the two-party engines are heavy; run it alone, under scripts/guarded.py --heavy, e.g.
//!     cargo test --offline --release --features test-engine,e2e --target-dir target/v3-test --test e2e_engines
//! The `run` kernel `tls-reveal 7` comes from the local kernel cache (.deps/emp-hybrid-word-v1/
//! cache) into a one-kernel manifest (pins checked), so the workers run in strict circuit mode;
//! `xor-bit` is the pinned word circuit (loader.rs). Writes only under CARGO_TARGET_TMPDIR.
//! Port 23940 (the workers' control link).
#![cfg(feature = "e2e")]
mod common;

use sha2::{Digest, Sha256};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{Receiver, channel};
use std::time::{Duration, Instant, SystemTime};

const BATCH: u8 = 93;
const PORT: u16 = 23940;

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
}

fn sha_hex(b: &[u8]) -> String {
    common::hex(&Sha256::digest(b))
}

/// The value of `"key": "VALUE"` in a kernel cache record (flat JSON, string values).
fn json_string(text: &str, key: &str) -> Option<String> {
    let at = text.find(&format!("\"{key}\": \""))? + key.len() + 5;
    Some(text[at..].split('"').next()?.to_string())
}

/// A one-kernel manifest (tls-reveal 7) from the newest valid cache record, pins checked.
fn manifest(out: &Path) -> PathBuf {
    let dir = out.join("circuits");
    std::fs::create_dir_all(&dir).unwrap();
    let cache = repo().join(".deps/emp-hybrid-word-v1/cache");
    let mut records: Vec<(SystemTime, PathBuf)> = std::fs::read_dir(&cache)
        .expect("kernel cache")
        .filter_map(|e| e.ok())
        .map(|e| e.path().join("kernel-tls-reveal-7.json"))
        .filter(|p| p.is_file())
        .map(|p| (p.metadata().unwrap().modified().unwrap(), p))
        .collect();
    records.sort();
    for (_, record) in records.iter().rev() {
        let meta = std::fs::read_to_string(record).unwrap();
        let (Some(sha), Some(layout_sha)) = (json_string(&meta, "sha256"), json_string(&meta, "layout_sha256")) else {
            continue;
        };
        let (flat, layout) = (record.with_extension("flat"), record.with_extension("layout"));
        let (Ok(f), Ok(l)) = (std::fs::read(&flat), std::fs::read(&layout)) else { continue };
        if sha_hex(&f) != sha || sha_hex(&l) != layout_sha {
            continue;
        }
        std::fs::write(dir.join("kernel-tls-reveal-7.flat"), f).unwrap();
        std::fs::write(dir.join("kernel-tls-reveal-7.layout"), l).unwrap();
        std::fs::write(dir.join("manifest.txt"), format!("EMP_HYBRID_CIRCUIT_MANIFEST_V1\n{sha} {layout_sha} tls-reveal 7\n")).unwrap();
        eprintln!("e2e: kernel {}", record.display());
        return dir.join("manifest.txt");
    }
    panic!("no usable tls-reveal 7 kernel in the cache");
}

fn request(code: u8, seq: u64, payload: &[u8]) -> Vec<u8> {
    [&[code][..], &seq.to_be_bytes(), &(payload.len() as u32).to_be_bytes(), payload].concat()
}

/// [boolPublic 40 [1], exchange len 1 label 0 [byte]]: `check` refuses instruction 1.
fn refused(byte: u8) -> Vec<u8> {
    let mut b = 2u64.to_le_bytes().to_vec();
    b.push(3);
    b.extend(40u64.to_le_bytes());
    b.extend(1u64.to_le_bytes());
    b.push(1);
    b.push(21);
    b.extend(1u64.to_le_bytes());
    b.extend(0u64.to_le_bytes());
    b.extend(1u64.to_le_bytes());
    b.push(byte);
    b
}

struct Worker {
    child: Child,
    stdin: Option<ChildStdin>,
    replies: Receiver<Option<(u8, Vec<u8>)>>,
}

impl Worker {
    fn start(party: u8, out: &Path, work: &Path, manifest: &Path, session: &str, tag: &str) -> Worker {
        let mp = repo().join(".deps/two-party-comparison/data61-MP-SPDZ-113c4e4");
        let log = std::fs::File::create(out.join(format!("worker-{party}{tag}.log"))).unwrap();
        let mut child = Command::new(env!("CARGO_BIN_EXE_node-worker"))
            .arg(party.to_string())
            .arg(out.join("hosts"))
            .arg(PORT.to_string())
            .arg(repo().join("handshake_backend/EmpHybridWork/circuit_cache.py"))
            .arg(session)
            .current_dir(work)
            .env("DYLD_LIBRARY_PATH", &mp)
            .env("CIRCUIT_MANIFEST", manifest)
            .env("TLS_WORKER_PEER_WAIT", "120")
            .env("TLS_WORKER_TRIPLE_STOCK", "0")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(log)
            .spawn()
            .expect("node-worker");
        let stdin = child.stdin.take();
        let mut stdout = child.stdout.take().unwrap();
        let (tx, rx) = channel();
        std::thread::spawn(move || {
            loop {
                let mut head = [0u8; 5];
                if stdout.read_exact(&mut head).is_err() {
                    let _ = tx.send(None);
                    return;
                }
                let mut payload = vec![0u8; u32::from_be_bytes(head[1..5].try_into().unwrap()) as usize];
                if stdout.read_exact(&mut payload).is_err() {
                    let _ = tx.send(None);
                    return;
                }
                let _ = tx.send(Some((head[0], payload)));
            }
        });
        Worker { child, stdin, replies: rx }
    }
    fn send(&mut self, data: &[u8]) {
        let s = self.stdin.as_mut().unwrap();
        s.write_all(data).unwrap();
        s.flush().unwrap();
    }
    fn reply(&self) -> Option<(u8, Vec<u8>)> {
        self.replies.recv_timeout(Duration::from_secs(600)).ok().flatten()
    }
    /// Ends the pipe (the worker then ends its session with the peer).
    fn close(&mut self) {
        drop(self.stdin.take());
    }
    fn finish(mut self) -> Option<i32> {
        self.close();
        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            if let Ok(Some(status)) = self.child.try_wait() {
                return status.code();
            }
            if Instant::now() > deadline {
                let _ = self.child.kill();
                return self.child.wait().ok().and_then(|s| s.code());
            }
            std::thread::sleep(Duration::from_millis(50));
        }
    }
}

#[test]
fn lean_flows_on_the_real_engines() {
    let started = Instant::now();
    // The `program` flow needs its V3 programs loaded from pinned files (loader.rs
    // FIELD_PROGRAMS; the files are the V3 re-export's, FIELD_PROGRAMS_V3.md). Its rounds that
    // name only pinned programs (`field-quotient`) run here; `test-allrows` is a vector-only
    // program (no pin), so the rounds from its first use on run on the stand-in engines only
    // (tests/batch_pair.rs).
    let names_allrows = |b: &[u8]| b.windows(12).any(|w| w == b"test-allrows");
    let flows: Vec<_> = common::flows(&common::text())
        .into_iter()
        .map(|mut f| {
            if f.name == "program" {
                let cut = f.rounds.iter().position(|r| r.batch.iter().any(|b| names_allrows(b))).unwrap_or(f.rounds.len());
                f.rounds.truncate(cut);
            }
            f
        })
        .collect();
    assert!(flows.iter().any(|f| f.name == "program" && !f.rounds.is_empty()), "no program round runs");
    let out = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("node-worker-e2e-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&out);
    std::fs::create_dir_all(&out).unwrap();
    let manifest = manifest(&out);
    let work = out.join("work");
    std::fs::create_dir_all(&work).unwrap();
    let mp = repo().join(".deps/two-party-comparison/data61-MP-SPDZ-113c4e4");
    let ssl = Command::new("bash")
        .arg(mp.join("Scripts/setup-ssl.sh"))
        .arg("2")
        .current_dir(&work)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .expect("setup-ssl.sh");
    assert!(ssl.success(), "setup-ssl.sh");
    std::fs::write(out.join("hosts"), "127.0.0.1\n127.0.0.1\n").unwrap();
    // Two sessions, each on a fresh pair of workers: the vectors' `program` flow starts from an
    // empty context (its handles 1… would clash with the earlier flows' live handles).
    let first: Vec<&common::Flow> = flows.iter().filter(|f| f.name != "program").collect();
    let second: Vec<&common::Flow> = flows.iter().filter(|f| f.name == "program").collect();
    one_session(&first, &out, &work, &manifest, "", true, started);
    one_session(&second, &out, &work, &manifest, "-program", false, started);
    eprintln!("e2e: passed ({} flows)", flows.len());
}

/// One worker session: the flows, then (if `refusal`) a batch `check` refuses and the latch.
fn one_session(
    flows: &[&common::Flow],
    out: &Path,
    work: &Path,
    manifest: &Path,
    tag: &str,
    refusal: bool,
    started: Instant,
) {
    let session = sha_hex(format!("{:?} {} {tag}", SystemTime::now(), std::process::id()).as_bytes());
    let mut ws = [Worker::start(0, out, work, manifest, &session, tag), Worker::start(1, out, work, manifest, &session, tag)];

    let mut failure = None;
    let mut seq = 0u64;
    'flows: for flow in flows {
        for (i, round) in flow.rounds.iter().enumerate() {
            let t = Instant::now();
            for p in 0..2 {
                ws[p].send(&request(BATCH, seq, &round.batch[p]));
            }
            let got = [ws[0].reply(), ws[1].reply()];
            eprintln!("e2e: {} round {i} (sequence {seq}) {:.3}s", flow.name, t.elapsed().as_secs_f64());
            for p in 0..2 {
                if got[p].as_ref().map(|(s, r)| (*s, r.as_slice())) != Some((0, &round.reply[p][..])) {
                    failure = Some(format!(
                        "{} round {i}: party {p} got {:?}, Lean says {}",
                        flow.name,
                        got[p].as_ref().map(|(s, r)| (*s, common::hex(r))),
                        common::hex(&round.reply[p])
                    ));
                    break 'flows;
                }
            }
            seq += 1;
        }
    }
    if failure.is_none() && refusal {
        for (p, w) in ws.iter_mut().enumerate() {
            w.send(&request(BATCH, seq, &refused(p as u8 + 1)));
        }
        let got = [ws[0].reply(), ws[1].reply()];
        if got.iter().any(|g| g.as_ref().map(|x| x.0) != Some(1)) {
            failure = Some("a batch refused by check was not rejected by both".into());
        }
        for (p, w) in ws.iter_mut().enumerate() {
            w.send(&request(BATCH, seq + 1, &refused(p as u8 + 1)));
        }
        let got = [ws[0].reply(), ws[1].reply()];
        if failure.is_none() && got.iter().any(|g| g.as_ref().map(|x| x.0) != Some(1)) {
            failure = Some("the latch is not terminal after a rejected batch".into());
        }
    }
    // Both pipes end before either worker is waited for (each ends its session with the other).
    for w in ws.iter_mut() {
        w.close();
    }
    let [a, b] = ws;
    let codes = [a.finish(), b.finish()];
    eprintln!("e2e{tag}: exit codes {codes:?}, {:.1}s, logs in {}", started.elapsed().as_secs_f64(), out.display());
    for p in 0..2 {
        let log = std::fs::read_to_string(out.join(format!("worker-{p}{tag}.log"))).unwrap_or_default();
        for line in log.lines().filter(|l| l.contains("security_mode") || l.contains("rejected") || l.contains("aborted")) {
            eprintln!("e2e{tag}: worker {p}: {}", &line[..line.len().min(300)]);
        }
    }
    if let Some(f) = failure {
        panic!("{f}");
    }
    assert_eq!(codes, [Some(0), Some(0)], "both workers end cleanly");
}
