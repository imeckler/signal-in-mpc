//! Stage S13 on two shells with STAND-IN engines (an ideal two-party functionality computed in
//! the clear, as tests/s12_pair.rs): the Lean send flows (`Send.sealScript` op 41, `requestScript`
//! op 42 and the request's record phase `requestCtrScript`; `devicesScript` op 61 with two devices,
//! `requestDevicesScript` op 62 and the record phase with `bundle-request-ctr`), run batch by batch
//! through pipe operation 93; every reply must equal the reply the Lean model computes
//! (tests/s13_vectors.txt, from tests/lean/S13Vectors.lean). Each flow starts a fresh pair of shells
//! (each starts from an empty handle table, as the Lean model's flow does).
//!
//! The stand-in circuits are a TABLE of the Lean model's evaluations (`eval` lines: `signal-widths`
//! itself, the seal and request kernels' specifications on the inputs the flow produced): the test
//! is about the shells (the agreement, `check` with the kernels' marks, plumbing, the openings, the
//! frees) handing the Lean scripts exactly the replies of Lean's model. The vectors' `check` lines
//! are the model's values against the Lean references: the opened envelopes are `sealV1` of the
//! reference send step, the kept states the advanced records, the opened request records the CTR
//! encryption of the filled request frames.
mod common;

use node_worker::engines::{Counters, Engines};
use node_worker::interp::BATCH;
use node_worker::link::Link;
use node_worker::loader::{Kernel, Kernels};
use node_worker::shell::Shell;
use std::collections::HashMap;
use std::net::{Ipv4Addr, TcpListener};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

use common::field::{Fe, add, bytes_of, fe_of, inv, mul, sub};

type Table = HashMap<(String, Vec<u8>), Vec<u8>>;

fn text() -> String {
    std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/s13_vectors.txt")).expect("tests/s13_vectors.txt")
}

/// The circuit evaluations (`eval NAME_HEX IN_HEX OUT_HEX`, one byte per bit).
fn table(text: &str) -> Table {
    let mut t = Table::new();
    for l in text.lines().filter_map(|l| l.strip_prefix("eval ")) {
        let f: Vec<&str> = l.split(' ').collect();
        let name = String::from_utf8(common::unhex(f[0])).unwrap();
        t.insert((name, common::unhex(f[1])), common::unhex(f[2]));
    }
    t
}

/// The circuits' shapes from the `sig` lines (input width, output width of one copy).
fn shapes(text: &str) -> HashMap<String, (u32, u32)> {
    common::sigs(text)
        .into_iter()
        .map(|(n, s)| (String::from_utf8(n).unwrap(), (s.in_width as u32, s.out_marks.len() as u32)))
        .collect()
}

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
            let (g, t) = self.cv.wait_timeout(slots, Duration::from_secs(60)).unwrap();
            slots = g;
            assert!(!t.timed_out(), "interactive call {call}: the other party never came");
        }
    }
}

struct Ideal {
    party: usize,
    meeting: Arc<Meeting>,
    table: Arc<Table>,
    shapes: Arc<HashMap<String, (u32, u32)>>,
    calls: u64,
    next: u64,
    bools: HashMap<u64, Vec<u8>>,
    fields: HashMap<u64, Fe>,
    circuits: HashMap<u64, String>,
}

impl Ideal {
    fn new(party: usize, meeting: Arc<Meeting>, table: Arc<Table>, shapes: Arc<HashMap<String, (u32, u32)>>) -> Ideal {
        Ideal { party, meeting, table, shapes, calls: 0, next: 1, bools: HashMap::new(), fields: HashMap::new(), circuits: HashMap::new() }
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

    fn circuit_load(&mut self, path: &str, _sha256: &str) -> Result<(u64, u32, u32), String> {
        let name = path.strip_prefix("fake/").ok_or("path")?.to_string();
        let s = *self.shapes.get(&name).ok_or("no such circuit")?;
        let h = self.handle();
        self.circuits.insert(h, name);
        Ok((h, s.0, s.1))
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
    fn bool_run(&mut self, circuit: u64, copies: u32, input: u64) -> Result<u64, String> {
        let name = self.circuits.get(&circuit).ok_or("circuit")?.clone();
        let v = self.bool(input)?;
        let per = v.len() / copies as usize;
        let mut out = vec![];
        for j in 0..copies as usize {
            let x = v[j * per..(j + 1) * per].to_vec();
            let y = self.table.get(&(name.clone(), x)).ok_or_else(|| format!("no evaluation of {name} on this input"))?;
            out.extend(y);
        }
        Ok(self.put_bool(out))
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

#[derive(Debug, Default, Clone)]
struct Round {
    batch: [Vec<u8>; 2],
    verdict: [String; 2],
    reply: [Vec<u8>; 2],
}

/// The flows of the file, each its rounds and how it ended.
fn flows(text: &str) -> Vec<(String, Vec<Round>, String)> {
    let mut out: Vec<(String, Vec<Round>, String)> = vec![];
    let mut party = 0usize;
    for line in text.lines() {
        let (key, rest) = line.split_once(' ').unwrap_or((line, ""));
        match key {
            "flow" => out.push((rest.to_string(), vec![], String::new())),
            "round" => out.last_mut().unwrap().1.push(Round::default()),
            "party" => party = if rest == "a" { 0 } else { 1 },
            "batch" => out.last_mut().unwrap().1.last_mut().unwrap().batch[party] = common::unhex(rest),
            "verdict" => out.last_mut().unwrap().1.last_mut().unwrap().verdict[party] = rest.to_string(),
            "reply" => out.last_mut().unwrap().1.last_mut().unwrap().reply[party] = common::unhex(rest),
            "finished" | "abort" | "error" => {
                if let Some(f) = out.last_mut() {
                    f.2 = line.to_string()
                }
            }
            _ => {}
        }
    }
    out
}

fn kernels(text: &str) -> Kernels {
    let mut k = Kernels::default();
    for (name, sig) in common::sigs(text) {
        let path = format!("fake/{}", String::from_utf8(name.clone()).unwrap());
        k.insert(&name, Kernel { flat: path.into(), sha256: String::new(), sig });
    }
    k
}

fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

type Pair = (Shell<Ideal>, Shell<Ideal>);

fn pair(text: &str) -> Pair {
    let port = free_port();
    let wait = Some(Duration::from_secs(60));
    let leader = std::thread::spawn(move || Link::listen(Some(Ipv4Addr::LOCALHOST), port).unwrap());
    let mut b = Link::dial(Ipv4Addr::LOCALHOST, port, wait).unwrap();
    let mut a = leader.join().unwrap();
    let t = std::thread::spawn(move || {
        a.hello(&[9; 32], wait).unwrap();
        a
    });
    b.hello(&[9; 32], wait).unwrap();
    let a = t.join().unwrap();
    let meeting = Arc::new(Meeting::default());
    let tb = Arc::new(table(text));
    let sh = Arc::new(shapes(text));
    let mut sa = Shell::new(true, "s13".into(), a, Ideal::new(0, meeting.clone(), tb.clone(), sh.clone()), wait);
    let mut sb = Shell::new(false, "s13".into(), b, Ideal::new(1, meeting, tb, sh), wait);
    sa.kernels = kernels(text);
    sb.kernels = kernels(text);
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

#[test]
fn s13_vectors_are_consistent() {
    let t = text();
    let checks: Vec<&str> = t.lines().filter(|l| l.starts_with("check ")).collect();
    assert_eq!(checks.len(), 4, "{checks:?}");
    for c in &checks {
        assert!(c.ends_with(" ok"), "{c}");
    }
    let fs = flows(&t);
    assert_eq!(fs.len(), 2);
    for (name, rs, end) in &fs {
        assert_eq!(end, "finished", "{name}");
        assert!(rs.len() >= 6, "{name}: {} rounds", rs.len());
        for (i, r) in rs.iter().enumerate() {
            assert_eq!(r.verdict, ["ok".to_string(), "ok".to_string()], "{name} round {i}: Lean's check admits both batches");
        }
    }
    // The four kernels the flows name: widths, the seal, the two request sealers.
    assert_eq!(common::sigs(&t).len(), 4);
}

#[test]
fn s13_send_flows_on_two_shells() {
    let t = text();
    for (name, rs, _) in flows(&t) {
        let mut p = pair(&t);
        for (seq, round) in rs.iter().enumerate() {
            let (np, (ra, rb)) = both(p, seq as u64, round.batch[0].clone(), round.batch[1].clone());
            p = np;
            assert_eq!(ra.as_deref(), Ok(&round.reply[0][..]), "{name} round {seq}: party A's reply");
            assert_eq!(rb.as_deref(), Ok(&round.reply[1][..]), "{name} round {seq}: party B's reply");
        }
        // Every engine value the flow left is a live Lean handle.
        assert_eq!(p.0.engines.bools.len(), p.0.interp.ctx.bools.len(), "{name}");
        assert_eq!(p.1.engines.bools.len(), p.1.interp.ctx.bools.len(), "{name}");
        eprintln!("stand-in: S13 flow {name} ok ({} rounds)", rs.len());
    }
}
