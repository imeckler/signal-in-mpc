//! Stage S10 on two shells with STAND-IN engines (an ideal two-party functionality computed in
//! the clear, as tests/batch_pair.rs): the Lean flows `Masks.generate` (with the TEST parameters
//! `Masks.testParams 3 1`: N = 3, B = 2, one bit block — a `Config.test` deviation, not a deployed
//! profile), word to field, field to word, bits to field, shared bits and the masked quotient, run
//! batch by batch through pipe operation 93; every reply must equal the reply the Lean model
//! computes (tests/s10_vectors.txt, from tests/lean/S10Vectors.lean).
//!
//! The cheating cases (party B deviates, as `EMP_TEST_WORD_*` / `EMP_TEST_BITBLOCK_*` do in the C++
//! fixtures): a wrong cut candidate, a wrong bucket member, a non-bit, a reference ≥ p, a wrong bit
//! block. The decision to abort is the Lean script's (the honest party's continuation reads the
//! opened values and aborts); this test checks that the shells with stand-in engines release
//! exactly the values Lean's model releases up to that point (so the real worker hands the Lean
//! script the same replies), and that Lean's honest party aborts there (the vectors' `abort` and
//! `check … aborts ok` lines). The stand-in circuits compute the word circuits' exact
//! specifications on every input, canonical or not (ConvertBase.lean `addModSpec`, …), so the
//! non-canonical cases behave as the pinned circuits do.
mod common;

use node_worker::engines::{Counters, Engines};
use node_worker::interp::BATCH;
use node_worker::link::Link;
use node_worker::loader::{FIELD_MASK_SUB_SHA256, Kernel, Kernels, hex as hexs};
use node_worker::shell::Shell;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::net::{Ipv4Addr, TcpListener};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

use common::field::{Fe, P, add, bytes_of, fe_of, inv, mul, sub};

// ---- the word circuits' specifications, on bit vectors (least significant bit first)

fn p_bits(n: usize) -> Vec<u8> {
    (0..n).map(|i| if i < 256 { ((P[i / 64] >> (i % 64)) & 1) as u8 } else { 0 }).collect()
}
/// a + b, one bit longer.
fn add_bits(a: &[u8], b: &[u8]) -> Vec<u8> {
    let n = a.len().max(b.len());
    let mut out = Vec::with_capacity(n + 1);
    let mut c = 0u8;
    for i in 0..n {
        let s = a.get(i).copied().unwrap_or(0) + b.get(i).copied().unwrap_or(0) + c;
        out.push(s & 1);
        c = s >> 1;
    }
    out.push(c);
    out
}
fn ge_bits(a: &[u8], b: &[u8]) -> bool {
    let n = a.len().max(b.len());
    for i in (0..n).rev() {
        let (x, y) = (a.get(i).copied().unwrap_or(0), b.get(i).copied().unwrap_or(0));
        if x != y {
            return x > y;
        }
    }
    true
}
/// a − b for a ≥ b (a's length).
fn sub_bits(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(a.len());
    let mut borrow = 0i8;
    for i in 0..a.len() {
        let d = a[i] as i8 - b.get(i).copied().unwrap_or(0) as i8 - borrow;
        out.push((d & 1) as u8);
        borrow = if d < 0 { 1 } else { 0 };
    }
    out
}
/// `addModSpec`: the 256-bit sum, minus p when at least p, truncated to 255 bits.
fn addmod_spec(x: &[u8], y: &[u8]) -> Vec<u8> {
    let s = add_bits(x, y);
    let s = if ge_bits(&s, &p_bits(256)) { sub_bits(&s, &p_bits(256)) } else { s };
    s[..255].to_vec()
}
/// `reduceSpec`.
fn reduce_spec(u: &[u8]) -> Vec<u8> {
    if ge_bits(u, &p_bits(255)) { sub_bits(u, &p_bits(255)) } else { u.to_vec() }
}
fn below_p(x: &[u8]) -> bool {
    !ge_bits(x, &p_bits(255))
}
fn at_least_32(x: &[u8]) -> bool {
    x[5..].iter().any(|b| *b == 1)
}
fn swap_bit(v: &[u8], t: usize) -> u8 {
    if t == 2 {
        v[3]
    } else if t == 253 {
        1 - v[253]
    } else {
        v[t + 1] ^ v[t]
    }
}

/// The stand-in circuits (ConvertBase.lean `WordLoaded`).
fn eval(name: &str, input: &[u8]) -> Vec<u8> {
    let (x, y) = (&input[..255.min(input.len())], if input.len() >= 510 { &input[255..510] } else { &[][..] });
    match name {
        "modadd" | "modadd-open" => addmod_spec(x, y),
        "finalize-mask" => [addmod_spec(x, y), vec![(below_p(x) && below_p(y)) as u8]].concat(),
        "finalize-bits" => {
            let xs: Vec<u8> = x.iter().zip(y).map(|(a, b)| a ^ b).collect();
            [xs, vec![(below_p(x) && below_p(y) && at_least_32(x) && at_least_32(y)) as u8]].concat()
        }
        "into-field-open" => addmod_spec(&reduce_spec(x), y),
        "xor-bit" | "xor-bit-open" => vec![input[0] ^ input[1]],
        "swap-bits" => (0..252).map(|k| swap_bit(input, k + 2)).collect(),
        other => panic!("no stand-in for {other}"),
    }
}

fn shape(name: &str) -> Option<(u32, u32)> {
    Some(match name {
        "modadd" | "modadd-open" | "into-field-open" => (510, 255),
        "finalize-mask" | "finalize-bits" => (510, 256),
        "xor-bit" | "xor-bit-open" => (2, 1),
        "swap-bits" => (256, 252),
        _ => return None,
    })
}

// ---- the ideal functionality, one stand-in per party (as tests/batch_pair.rs)

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
    calls: u64,
    next: u64,
    bools: HashMap<u64, Vec<u8>>,
    fields: HashMap<u64, Fe>,
    circuits: HashMap<u64, String>,
}

impl Ideal {
    fn new(party: usize, meeting: Arc<Meeting>) -> Ideal {
        Ideal { party, meeting, calls: 0, next: 1, bools: HashMap::new(), fields: HashMap::new(), circuits: HashMap::new() }
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
        let s = shape(&name).ok_or("no such circuit")?;
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
        let out = (0..copies as usize).flat_map(|j| eval(&name, &v[j * per..(j + 1) * per])).collect();
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
    end: String,
}

fn text() -> String {
    std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/s10_vectors.txt")).expect("tests/s10_vectors.txt")
}

fn flows(text: &str) -> Vec<Flow> {
    let mut out: Vec<Flow> = vec![];
    let mut party = 0usize;
    for line in text.lines() {
        let (key, rest) = line.split_once(' ').unwrap_or((line, ""));
        match key {
            "flow" => out.push(Flow { name: rest.to_string(), rounds: vec![], end: String::new() }),
            "round" => out.last_mut().unwrap().rounds.push(Round::default()),
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
        a.hello(&[7; 32], wait).unwrap();
        a
    });
    b.hello(&[7; 32], wait).unwrap();
    let a = t.join().unwrap();
    let meeting = Arc::new(Meeting::default());
    let mut sa = Shell::new(true, "s10".into(), a, Ideal::new(0, meeting.clone()), wait);
    let mut sb = Shell::new(false, "s10".into(), b, Ideal::new(1, meeting), wait);
    sa.kernels = kernels(text);
    sb.kernels = kernels(text);
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
fn s10_vectors_are_consistent() {
    let t = text();
    // Every value check of the Lean model passed (P-CUT (a) on the generated pool, the conversions,
    // the quotient; every cheating case aborts).
    let checks: Vec<&str> = t.lines().filter(|l| l.starts_with("check ")).collect();
    assert!(checks.len() >= 17, "{checks:?}");
    for c in &checks {
        assert!(c.ends_with(" ok"), "{c}");
    }
    // The natively written program's pin is loader.rs's.
    let native = t.lines().find_map(|l| l.strip_prefix("native field-mask-sub ")).expect("native line");
    let (text_hex, pin) = native.split_once(' ').unwrap();
    assert_eq!(hexs(&Sha256::digest(common::unhex(text_hex))), pin);
    assert_eq!(pin, FIELD_MASK_SUB_SHA256);
}

#[test]
fn s10_honest_flows_on_two_shells() {
    let t = text();
    let fl = flows(&t);
    for name in ["s10-generate", "s10-demo"] {
        let f = fl.iter().find(|f| f.name == name).expect(name);
        assert_eq!(f.end, "finished", "{name}");
        let p = run(&t, f);
        // Every engine value the flow left is a live Lean handle (the conversions free their masks).
        assert_eq!(p.0.engines.bools.len(), p.0.interp.ctx.bools.len(), "{name}");
        assert_eq!(p.0.engines.fields.len(), p.0.interp.ctx.fields.len(), "{name}");
        eprintln!("stand-in: S10 flow {name} ok ({} rounds)", f.rounds.len());
    }
}

#[test]
fn s10_cheating_party_aborts() {
    let t = text();
    let fl = flows(&t);
    for (name, why) in [
        ("cheat-cut", "abort a cross-domain candidate mismatch"),
        ("cheat-bucket", "abort a cross-domain bucket mismatch"),
        ("cheat-nonbit", "abort a bit block inconsistent with verified reference"),
        ("cheat-reference", "abort a kept reference out of range"),
        ("cheat-bitblock", "abort a bit block inconsistent with verified reference"),
    ] {
        let f = fl.iter().find(|f| f.name == name).expect(name);
        // Lean's honest party A aborts at the step the C++ throws at.
        assert_eq!(f.end, why, "{name}");
        // The stand-in shells release exactly what the Lean model releases up to that point, so the
        // worker hands the Lean script the replies on which it aborts.
        let _ = run(&t, f);
        eprintln!("stand-in: {name} aborts after {} rounds", f.rounds.len());
    }
}
