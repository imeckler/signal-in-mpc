//! This machine: the clock, the random generator, the stop signals, the daemon's standard
//! streams and arguments, and its exit.

use std::io::{Read, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

// ---- The clock.

/// Wall-clock time in Unix seconds (request freshness, peer message times, event times).
pub fn unix_now() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

/// A point of the monotonic clock (timeouts, ages, back-off). Every reading of it is a call here.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Moment(Instant);

impl Moment {
    pub fn now() -> Moment {
        Moment(Instant::now())
    }

    /// Time since this moment (zero for a moment in the future).
    pub fn elapsed(self) -> Duration {
        self.0.elapsed()
    }

    pub fn after(self, duration: Duration) -> Moment {
        Moment(self.0 + duration)
    }

    /// The time left until this moment; `None` once it is reached.
    pub fn remaining(self) -> Option<Duration> {
        let now = Instant::now();
        if now >= self.0 { None } else { Some(self.0 - now) }
    }
}

pub fn sleep(duration: Duration) {
    std::thread::sleep(duration);
}

// ---- Randomness: the operating system's generator.

pub fn random_bytes(count: usize) -> Result<Vec<u8>, String> {
    let mut out = vec![0u8; count];
    std::fs::File::open("/dev/urandom").and_then(|mut f| f.read_exact(&mut out)).map_err(|e| format!("randomness: {e}"))?;
    Ok(out)
}

// ---- Stop signals (SIGTERM, SIGINT): the daemon ends its sessions and exits.

static STOP: AtomicBool = AtomicBool::new(false);

extern "C" fn on_signal(_: libc::c_int) {
    STOP.store(true, Ordering::SeqCst);
}

pub fn catch_stop_signals() {
    unsafe {
        libc::signal(libc::SIGTERM, on_signal as extern "C" fn(libc::c_int) as libc::sighandler_t);
        libc::signal(libc::SIGINT, on_signal as extern "C" fn(libc::c_int) as libc::sighandler_t);
    }
}

pub fn stopping() -> bool {
    STOP.load(Ordering::SeqCst)
}

// ---- Standard streams, arguments, exit.

/// The daemon's log: standard error, one line per event, prefixed with the Unix time.
pub fn log(text: &str) {
    eprintln!("{} node-daemon: {text}", unix_now());
}

/// The one line on standard output, once both listeners are bound (the harness waits for it).
pub fn announce_listening(listen: &str, peer_listen: &str) {
    println!("listening {listen} peer {peer_listen}");
    let _ = std::io::stdout().flush();
}

pub fn arguments() -> Vec<String> {
    std::env::args().collect()
}

/// A start-up failure: `text` on standard error, exit status 2.
pub fn fail(text: &str) -> ! {
    eprintln!("{text}");
    std::process::exit(2);
}
