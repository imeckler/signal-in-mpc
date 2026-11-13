//! Stage S11 on two shells with STAND-IN engines (an ideal two-party functionality computed in
//! the clear, as tests/s10_pair.rs): the Lean curve flows (TlsMpc/Node/Flows/Curve.lean) run batch
//! by batch through pipe operation 93 with the REAL field programs (Lean's renders of the exported
//! declarations, evaluated by program.rs on the stand-in field engine); every reply must equal the
//! reply the Lean model computes (tests/s11_vectors.txt, from tests/lean/S11Vectors.lean).
//!
//! Scenarios (plan 10.1 set E, `rounds_fixture` as scripts): split ECDH, nine X25519 agreements, the
//! offset agreement (prepare, both step programs), the hinted programs (lift, hints, tables, three
//! agreements, a signature point, torsion), op 66 with an invalid key in the batch; cheating party B:
//! an off-curve agreement share, an off-curve mask point, a wrong hint, a K₀ half that is not a
//! point. A staged flow's local step (`local a` / `local b` lines) is the controller's own work
//! between two scripts: nothing reaches the shells.
mod common;

use node_worker::engines::{Counters, Engines};
use node_worker::interp::BATCH;
use node_worker::link::Link;
use node_worker::loader::{FIELD_PROGRAMS, Kernels, hex as hexs};
use node_worker::shell::Shell;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::net::{Ipv4Addr, TcpListener};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

use common::field::{Fe, add, bytes_of, fe_of, inv, mul, sub};

// ---- the ideal functionality, one stand-in per party (as tests/s10_pair.rs; no Boolean circuit)

#[derive(Default)]
struct Meeting {
    slots: Mutex<HashMap<u64, [Option<Vec<u8>>; 2]>>,
    cv: Condvar,
}

impl Meeting {
    fn meet(&self, call: u64, party: usize, mine: Vec<u8>) -> [Vec<u8>; 2] {
        let mut slots = self.slots.lock().unwrap();
        slots.entry(call).or_default()[party] = Some(mine);
        self.cv.notify_all();
        loop {
            let e = &slots[&call];
            if let [Some(a), Some(b)] = e {
                return [a.clone(), b.clone()];
            }
            let (g, t) = self.cv.wait_timeout(slots, Duration::from_secs(120)).unwrap();
            slots = g;
            assert!(!t.timed_out(), "interactive call {call}: the other party never came");
        }
    }
}

struct Ideal {
    party: usize,
    meeting: Arc<Meeting>,
    calls: u64,
    next: u64,
    bools: HashMap<u64, Vec<u8>>,
    fields: HashMap<u64, Fe>,
}

impl Ideal {
    fn new(party: usize, meeting: Arc<Meeting>) -> Ideal {
        Ideal { party, meeting, calls: 0, next: 1, bools: HashMap::new(), fields: HashMap::new() }
    }
    fn meet(&mut self, mine: Vec<u8>) -> [Vec<u8>; 2] {
        self.calls += 1;
        self.meeting.meet(self.calls, self.party, mine)
    }
    fn handle(&mut self) -> u64 {
        self.next += 1;
        self.next
    }
    fn put_bool(&mut self, v: Vec<u8>) -> u64 {
        let h = self.handle();
        self.bools.insert(h, v);
        h
    }
    fn put_field(&mut self, v: Fe) -> u64 {
        let h = self.handle();
        self.fields.insert(h, v);
        h
    }
    fn bool(&self, h: u64) -> Result<Vec<u8>, String> {
        self.bools.get(&h).cloned().ok_or_else(|| "unknown handle".into())
    }
    fn field(&self, h: u64) -> Result<Fe, String> {
        self.fields.get(&h).copied().ok_or_else(|| "unknown handle".into())
    }
}

impl Engines for Ideal {
    fn counters(&mut self) -> Counters {
        Counters::default()
    }
    fn legacy(&mut self, _: u8, _: u64, _: &[u8]) -> Result<Vec<u8>, String> {
        Err("no legacy library".into())
    }
    fn select(&mut self, _: u8) -> Result<(), String> {
        Ok(())
    }
    fn reset(&mut self) -> Result<(), String> {
        Ok(())
    }
    fn abort(&mut self) {}
    fn profile_report(&mut self, _: &str) {}

    fn circuit_load(&mut self, _path: &str, _sha256: &str) -> Result<(u64, u32, u32), String> {
        Err("no circuits in the S11 flows".into())
    }
    fn bool_input_private(&mut self, owner: u8, bits: &[u8]) -> Result<u64, String> {
        let both = self.meet(bits.to_vec());
        Ok(self.put_bool(both[owner as usize].clone()))
    }
    fn bool_input_both(&mut self, bits: &[u8]) -> Result<(u64, u64), String> {
        let both = self.meet(bits.to_vec());
        Ok((self.put_bool(both[0].clone()), self.put_bool(both[1].clone())))
    }
    fn bool_public(&mut self, bits: &[u8]) -> Result<u64, String> {
        Ok(self.put_bool(bits.to_vec()))
    }
    fn bool_run(&mut self, _circuit: u64, _copies: u32, _input: u64) -> Result<u64, String> {
        Err("no circuits in the S11 flows".into())
    }
    fn bool_open(&mut self, h: u64, count: usize) -> Result<Vec<u8>, String> {
        let v = self.bool(h)?;
        if v.len() != count {
            return Err("opened width".into());
        }
        Ok(v)
    }
    fn bool_open_to(&mut self, h: u64, recipient: u8, count: usize) -> Result<Vec<u8>, String> {
        let v = self.bool(h)?;
        if v.len() != count {
            return Err("opened width".into());
        }
        Ok(if recipient as usize == self.party { v } else { vec![0; count] })
    }
    fn bool_concat(&mut self, hs: &[u64]) -> Result<u64, String> {
        let mut v = vec![];
        for &h in hs {
            v.extend(self.bool(h)?);
        }
        Ok(self.put_bool(v))
    }
    fn bool_pick(&mut self, h: u64, indices: &[u64]) -> Result<u64, String> {
        let v = self.bool(h)?;
        Ok(self.put_bool(indices.iter().map(|&i| v[i as usize]).collect()))
    }
    fn bool_slice(&mut self, h: u64, lo: usize, hi: usize) -> Result<u64, String> {
        let v = self.bool(h)?;
        Ok(self.put_bool(v[lo..hi].to_vec()))
    }
    fn bool_free(&mut self, h: u64) -> Result<(), String> {
        self.bools.remove(&h).map(|_| ()).ok_or_else(|| "unknown handle".into())
    }
    fn field_input_coins(&mut self, local: &[u64]) -> Result<(Vec<u64>, Vec<u64>), String> {
        let both = self.meet(local.iter().flat_map(|c| c.to_le_bytes()).collect());
        let take = |s: &mut Self, b: &[u8]| -> Vec<u64> {
            b.chunks(8).map(|c| s.put_field([u64::from_le_bytes(c.try_into().unwrap()), 0, 0, 0])).collect()
        };
        Ok((take(self, &both[0]), take(self, &both[1])))
    }
    fn field_input_elements(&mut self, local: &[[u8; 32]]) -> Result<(Vec<u64>, Vec<u64>), String> {
        let both = self.meet(local.concat());
        let take = |s: &mut Self, b: &[u8]| -> Vec<u64> { b.chunks(32).map(|c| s.put_field(fe_of(c.try_into().unwrap()))).collect() };
        Ok((take(self, &both[0]), take(self, &both[1])))
    }
    fn field_constant(&mut self, value: u64) -> Result<u64, String> {
        Ok(self.put_field([value, 0, 0, 0]))
    }
    fn field_public(&mut self, value: &[u8; 32]) -> Result<u64, String> {
        Ok(self.put_field(fe_of(value)))
    }
    fn field_add(&mut self, a: u64, b: u64) -> Result<u64, String> {
        let v = add(&self.field(a)?, &self.field(b)?);
        Ok(self.put_field(v))
    }
    fn field_sub(&mut self, a: u64, b: u64) -> Result<u64, String> {
        let v = sub(&self.field(a)?, &self.field(b)?);
        Ok(self.put_field(v))
    }
    fn field_scale(&mut self, a: u64, constant: u64) -> Result<u64, String> {
        let v = mul(&self.field(a)?, &[constant, 0, 0, 0]);
        Ok(self.put_field(v))
    }
    fn field_divide_public(&mut self, a: u64, c: &[u8; 32]) -> Result<u64, String> {
        let v = mul(&self.field(a)?, &inv(&fe_of(c)));
        Ok(self.put_field(v))
    }
    fn field_mul(&mut self, a: &[u64], b: &[u64]) -> Result<Vec<u64>, String> {
        let mut outs = vec![];
        for (&x, &y) in a.iter().zip(b) {
            let v = mul(&self.field(x)?, &self.field(y)?);
            outs.push(self.put_field(v));
        }
        Ok(outs)
    }
    fn field_check(&mut self) -> Result<(), String> {
        Ok(())
    }
    fn field_checked_open(&mut self, hs: &[u64]) -> Result<Vec<[u8; 32]>, String> {
        hs.iter().map(|&h| self.field(h).map(|v| bytes_of(&v))).collect()
    }
    fn field_free(&mut self, h: u64) -> Result<(), String> {
        self.fields.remove(&h).map(|_| ()).ok_or_else(|| "unknown handle".into())
    }
}

// ---- the vectors

#[derive(Debug, Default, Clone)]
struct Round {
    batch: [Vec<u8>; 2],
    verdict: [String; 2],
    reply: [Vec<u8>; 2],
}

#[derive(Debug, Clone)]
struct Flow {
    name: String,
    rounds: Vec<Round>,
    locals: usize,
    end: String,
}

fn text() -> String {
    std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/s11_vectors.txt")).expect("tests/s11_vectors.txt")
}

fn flows(text: &str) -> Vec<Flow> {
    let mut out: Vec<Flow> = vec![];
    let mut party = 0usize;
    for line in text.lines() {
        let (key, rest) = line.split_once(' ').unwrap_or((line, ""));
        match key {
            "flow" => out.push(Flow { name: rest.to_string(), rounds: vec![], locals: 0, end: String::new() }),
            "round" => out.last_mut().unwrap().rounds.push(Round::default()),
            "local" => out.last_mut().unwrap().locals += 1,
            "party" => party = if rest == "a" { 0 } else { 1 },
            "batch" => out.last_mut().unwrap().rounds.last_mut().unwrap().batch[party] = common::unhex(rest),
            "verdict" => out.last_mut().unwrap().rounds.last_mut().unwrap().verdict[party] = rest.to_string(),
            "reply" => out.last_mut().unwrap().rounds.last_mut().unwrap().reply[party] = common::unhex(rest),
            "finished" | "abort" | "error" => out.last_mut().unwrap().end = line.to_string(),
            _ => {}
        }
    }
    out
}

fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

type Pair = (Shell<Ideal>, Shell<Ideal>);

fn pair(text: &str) -> Pair {
    let port = free_port();
    let wait = Some(Duration::from_secs(120));
    let leader = std::thread::spawn(move || Link::listen(Some(Ipv4Addr::LOCALHOST), port).unwrap());
    let mut b = Link::dial(Ipv4Addr::LOCALHOST, port, wait).unwrap();
    let mut a = leader.join().unwrap();
    let t = std::thread::spawn(move || {
        a.hello(&[11; 32], wait).unwrap();
        a
    });
    b.hello(&[11; 32], wait).unwrap();
    let a = t.join().unwrap();
    let meeting = Arc::new(Meeting::default());
    let mut sa = Shell::new(true, "s11".into(), a, Ideal::new(0, meeting.clone()), wait);
    let mut sb = Shell::new(false, "s11".into(), b, Ideal::new(1, meeting), wait);
    sa.kernels = Kernels::default();
    sb.kernels = Kernels::default();
    sa.set_programs(common::programs(text));
    sb.set_programs(common::programs(text));
    (sa, sb)
}

type Results = (Result<Vec<u8>, String>, Result<Vec<u8>, String>);

fn both(p: Pair, seq: u64, pa: Vec<u8>, pb: Vec<u8>) -> (Pair, Results) {
    let (a, mut b) = p;
    let t = std::thread::spawn(move || {
        let mut a = a;
        let r = a.call(BATCH, seq, &pa);
        (a, r)
    });
    let rb = b.call(BATCH, seq, &pb);
    let (a, ra) = t.join().unwrap();
    ((a, b), (ra, rb))
}

fn run(text: &str, flow: &Flow) -> Pair {
    let mut p = pair(text);
    for (seq, round) in flow.rounds.iter().enumerate() {
        assert_eq!(round.verdict, ["ok".to_string(), "ok".to_string()], "{} round {seq}: Lean's check admits both batches", flow.name);
        let (np, (ra, rb)) = both(p, seq as u64, round.batch[0].clone(), round.batch[1].clone());
        p = np;
        assert_eq!(ra.as_deref(), Ok(&round.reply[0][..]), "{} round {seq}: party A's reply", flow.name);
        assert_eq!(rb.as_deref(), Ok(&round.reply[1][..]), "{} round {seq}: party B's reply", flow.name);
    }
    p
}

#[test]
fn s11_vectors_are_consistent() {
    let t = text();
    // Every value check of the Lean model passed: the programs' validity and shapes, the honest
    // flows' results against Local/Edwards and X25519.spec, every cheating case aborts.
    let checks: Vec<&str> = t.lines().filter(|l| l.starts_with("check ")).collect();
    assert!(checks.len() >= 50, "{}", checks.len());
    for c in &checks {
        assert!(c.ends_with(" ok"), "{c}");
    }
    // Every program a curve flow names is listed in loader.rs (pinned, or a placeholder that fails
    // closed until the re-export), and each `pin` line is the SHA-256 of the program text given.
    let texts: HashMap<String, Vec<u8>> = t
        .lines()
        .filter_map(|l| l.strip_prefix("prog "))
        .map(|l| {
            let f: Vec<&str> = l.split(' ').collect();
            (String::from_utf8(common::unhex(f[0])).unwrap(), common::unhex(f[1]))
        })
        .collect();
    let mut pins = 0;
    for l in t.lines().filter_map(|l| l.strip_prefix("pin ")) {
        let (name, pin) = l.split_once(' ').unwrap();
        assert!(FIELD_PROGRAMS.iter().any(|p| p.name == name), "{name} is not in FIELD_PROGRAMS");
        assert_eq!(hexs(&Sha256::digest(&texts[name])), pin, "{name}");
        // program.rs parses Lean's text (the canonical form the pin names).
        node_worker::program::parse(&texts[name]).expect("Lean's V3 text parses");
        pins += 1;
    }
    assert_eq!(pins, 17);
}

#[test]
fn s11_honest_flows_on_two_shells() {
    let t = text();
    let fl = flows(&t);
    for name in ["s11-split", "s11-agree", "s11-offset", "s11-hinted", "s11-prepare"] {
        let f = fl.iter().find(|f| f.name == name).expect(name);
        assert_eq!(f.end, "finished", "{name}");
        let p = run(&t, f);
        assert_eq!(p.0.engines.fields.len(), p.0.interp.ctx.fields.len(), "{name}: engine values = live handles");
        eprintln!("stand-in: S11 flow {name} ok ({} rounds, {} local steps)", f.rounds.len(), f.locals);
    }
}

#[test]
fn s11_cheating_party_aborts() {
    let t = text();
    let fl = flows(&t);
    for (name, why) in [
        ("cheat-split-share", "abort a agreement share is not a curve point"),
        ("cheat-mask-point", "abort a hinted lift: a mask contribution is not a bit or not a curve point"),
        ("cheat-hint", "abort a bit table: a hint is wrong"),
        ("cheat-k0-half", "abort a point encoding"),
    ] {
        let f = fl.iter().find(|f| f.name == name).expect(name);
        assert_eq!(f.end, why, "{name}");
        let _ = run(&t, f);
        eprintln!("stand-in: {name} aborts after {} rounds", f.rounds.len());
    }
}
