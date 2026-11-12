//! node-worker PARTY HOSTS PORT CIRCUIT_CACHE_SCRIPT SESSION_ID_HEX
//!
//! The Rust worker shell (REORGANIZATION_PLAN.md S8). Speaks the controller's pipe protocol
//! unchanged (`TlsMpc/TlsWorkerPipe.lean`): a drop-in for `tls-worker-fixture-v3`. See lib.rs.
#![cfg_attr(not(feature = "engine"), allow(unused_imports))]
use node_worker::config::Config;
use node_worker::engines::Engines;
use node_worker::link::Link;
use node_worker::loader::{Circuits, Kernels};
use node_worker::pipe::{self, ABORT, Latch, PipeError};
use node_worker::profile::{PREFIX, Profile};
use node_worker::shell::Shell;
use std::io::Write;
use std::time::Instant;

fn main() {
    // The engines need deep stacks (big_stack.h: 1 GiB in the C++ worker).
    let worker = std::thread::Builder::new().stack_size(1 << 30).spawn(run).expect("worker thread");
    let code = worker.join().unwrap_or(1);
    std::process::exit(code);
}

#[cfg(not(feature = "engine"))]
fn run() -> i32 {
    eprintln!("{PREFIX} aborted: node-worker was built without feature `engine`");
    2
}

#[cfg(feature = "engine")]
fn run() -> i32 {
    use node_worker::engines::native::{NativeEngines, build_identity};
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 6 {
        return 2;
    }
    let mut rpc = match pipe::take_stdout() {
        Ok(f) => f,
        Err(_) => return 2,
    };
    let config = match Config::parse(&args, |k| std::env::var(k).ok()) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("{PREFIX} configuration: {e}");
            return 2;
        }
    };
    let started = Instant::now();
    let (mode, test_build) = build_identity();
    let expected = if cfg!(feature = "semi-honest") { "semi-honest" } else { "malicious-128" };
    let setup = || -> Result<Shell<NativeEngines>, String> {
        if mode != expected || test_build != cfg!(feature = "test-engine") {
            return Err(format!("engine library {mode} (test {test_build}) does not match this build"));
        }
        if config.remote() || config.listen.is_some() {
            eprintln!(
                "{PREFIX} peer={} listen={}",
                config.peer,
                config.listen.map_or("any".to_string(), |l| l.to_string())
            );
        }
        let circuits = Circuits::from_environment(std::env::var("CIRCUIT_MANIFEST").ok(), cfg!(feature = "test-engine"))?;
        let port = u16::try_from(config.link_port()).map_err(|_| "port")?;
        let mut link = if config.leader() {
            Link::listen(config.listen, port)
        } else {
            Link::dial(config.peer, port, config.peer_wait)
        }
        .map_err(|e| format!("control link: {e}"))?;
        link.hello(&config.session_id, config.peer_wait)?;
        // The circuit manifest, agreed once before anything else (kernel.h's agreement, moved).
        let digest = circuits.digest();
        link.send(&node_worker::link::PeerFrame::Agreement(digest)).map_err(|e| format!("control link: {e}"))?;
        match link.recv(config.peer_wait) {
            Ok(node_worker::link::PeerFrame::Agreement(peer)) if peer == digest => {}
            Ok(_) => return Err("circuit manifest disagreement".into()),
            Err(e) => return Err(format!("control link: {e}")),
        }
        let kernels = match &circuits {
            Circuits::Pinned(manifest) => Kernels::from_manifest(manifest)?,
            Circuits::Unpinned => Kernels::default(),
        };
        let engines = NativeEngines::open(&config, matches!(circuits, Circuits::Pinned(_)) || !cfg!(feature = "test-engine"))?;
        let mut shell = Shell::new(config.leader(), config.session.clone(), link, engines, config.peer_wait);
        shell.kernels = kernels;
        Ok(shell)
    };
    let mut shell = match setup() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{PREFIX} aborted: {e}");
            let _ = pipe::write_reply(&mut rpc, false, &[]);
            return 1;
        }
    };
    eprintln!("{PREFIX} security_mode={mode} key_agreement={}", if config.ladder { "ladder" } else { "split" });
    let mut profile = Profile::new(started);
    eprintln!("{}", profile.ready(&shell.engines.counters()));
    let mut latch = Latch::default();
    let mut input = std::io::stdin().lock();
    loop {
        let request = match pipe::read_request(&mut input) {
            Ok(Some(r)) => r,
            Ok(None) => break,
            Err(PipeError::Bound) => {
                eprintln!("{PREFIX} aborted: request bound");
                let _ = pipe::write_reply(&mut rpc, false, &[]);
                return 1;
            }
            Err(PipeError::Io(e)) => {
                eprintln!("{PREFIX} aborted: pipe: {e}");
                return 1;
            }
        };
        let reply = |rpc: &mut std::fs::File, ok: bool, payload: &[u8]| pipe::write_reply(rpc, ok, payload);
        if request.code == ABORT {
            // Local and idempotent; not an erasure receipt.
            shell.engines.profile_report(&format!("{PREFIX} profile"));
            shell.abort();
            latch.fail();
            eprintln!("{PREFIX} operation 8 ok (local abort)");
            if reply(&mut rpc, true, &[]).is_err() {
                return 1;
            }
            continue;
        }
        if !latch.admit(request.sequence) {
            if reply(&mut rpc, false, &[]).is_err() {
                return 1;
            }
            continue;
        }
        let entered = Instant::now();
        let written = match shell.call(request.code, request.sequence, &request.payload) {
            Ok(out) => {
                let spent = entered.elapsed().as_secs_f64();
                if let Some(line) = profile.finished(request.code, spent, out.is_empty(), &shell.engines.counters()) {
                    eprintln!("{line}");
                }
                reply(&mut rpc, true, &out)
            }
            Err(e) => {
                eprintln!("{PREFIX} operation {} rejected: {e}", request.code);
                latch.fail();
                shell.abort();
                reply(&mut rpc, false, &[])
            }
        };
        if written.is_err() {
            return 1;
        }
    }
    shell.engines.profile_report(&format!("{PREFIX} profile"));
    for line in Profile::totals(&shell.engines.counters(), config.stock_factories) {
        eprintln!("{line}");
    }
    let _ = std::io::stderr().flush();
    0
}
