//! The worker's measurement lines on stderr, as `tls_worker_v3.cpp` prints them (the harnesses
//! parse `operation N ok seconds=… and_gates=… emp_sent_bytes=… field_sent_bytes=… field_products=…`).
//! Public counters only. The engines' own per-label rows come through `ea_profile_report`.
use crate::engines::Counters;
use std::time::Instant;

/// The prefix of every line (kept from the C++ worker so that existing log readers work).
pub const PREFIX: &str = "tls-worker-v3";

pub struct Profile {
    started: Instant,
    /// Time inside the worker since the last printed line (this call and any empty polls).
    busy: f64,
}

impl Profile {
    pub fn new(started: Instant) -> Profile {
        Profile { started, busy: 0.0 }
    }
    fn seconds(&self) -> f64 {
        self.started.elapsed().as_secs_f64()
    }
    pub fn counters_text(c: &Counters) -> String {
        format!(
            "and_gates={} emp_sent_bytes={} field_sent_bytes={} field_products={}",
            c.and_gates, c.boolean_bytes, c.field_bytes, c.field_products
        )
    }
    /// Setup done (operation 0).
    pub fn ready(&self, c: &Counters) -> String {
        format!("{PREFIX} operation 0 ok seconds={} {}", self.seconds(), Self::counters_text(c))
    }
    /// One finished operation: the line, or None for an empty poll (17 with no record), whose
    /// time is carried into the next line's `busy`.
    pub fn finished(&mut self, code: u8, spent: f64, reply_empty: bool, c: &Counters) -> Option<String> {
        self.busy += spent;
        if code == 17 && reply_empty {
            return None;
        }
        let busy = std::mem::take(&mut self.busy);
        Some(format!("{PREFIX} operation {code} ok seconds={} {} busy={busy}", self.seconds(), Self::counters_text(c)))
    }
    pub fn totals(c: &Counters, factories: u32) -> [String; 2] {
        [
            format!("{PREFIX} stock factories={factories} minted={} mint_seconds={}", c.stock_minted, c.stock_seconds),
            format!("{PREFIX} totals and_gates={} emp_sent_bytes={}", c.and_gates, c.boolean_bytes),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_polls_carry_their_time_forward() {
        let mut p = Profile::new(Instant::now());
        let c = Counters { and_gates: 5, boolean_bytes: 6, field_bytes: 7, field_products: 8, ..Default::default() };
        assert!(p.finished(17, 0.25, true, &c).is_none());
        let line = p.finished(12, 0.5, false, &c).unwrap();
        assert!(line.starts_with("tls-worker-v3 operation 12 ok seconds="));
        assert!(line.ends_with("and_gates=5 emp_sent_bytes=6 field_sent_bytes=7 field_products=8 busy=0.75"));
        assert!(p.finished(17, 0.1, false, &c).unwrap().ends_with("busy=0.1"));
    }
}
