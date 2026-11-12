//! Two shells (leader A, follower B) over a real control link on 127.0.0.1 run Lean-generated
//! batches (tests/engine_vectors.txt) through pipe operation 93, with STAND-IN engines: an ideal
//! two-party functionality computed in the clear (each party's stand-in sees both parties'
//! inputs through an in-process meeting point). What this tests is the shell's side: decoding,
//! payload checks, the skeleton agreement, `check` before execution, the handle mapping, the
//! engine calls each opcode makes, the exchange, and the reply items, which must equal the
//! replies the Lean model computes for honest parties (`Random.joint`, `Upgrade.publicUpgrade`,
//! the Boolean and field round trips). The real engines run the same flows in
//! tests/e2e_batches.py (two node-worker processes; not a cargo test: it needs the engines'
//! links, MP-SPDZ certificates and the heavy-job lock).
mod common;

use node_worker::engines::{Counters, Engines};
use node_worker::interp::{BATCH, Datum, Party, Wire, decode_batch, decode_replies, encode_batch};
use node_worker::link::Link;
use node_worker::loader::{Kernel, Kernels};
use node_worker::shell::Shell;
use std::collections::HashMap;
use std::net::{Ipv4Addr, TcpListener};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

// ---- integers mod p = 2^255 - 19, four little-endian 64-bit limbs (test arithmetic only)

type Fe = [u64; 4];
const P: Fe = [0xffff_ffff_ffff_ffed, u64::MAX, u64::MAX, 0x7fff_ffff_ffff_ffff];

fn ge(a: &Fe, b: &Fe) -> bool {
    for i in (0..4).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}
fn raw_sub(a: &Fe, b: &Fe) -> Fe {
    let mut r = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (d, b1) = a[i].overflowing_sub(b[i]);
        let (d, b2) = d.overflowing_sub(borrow);
        r[i] = d;
        borrow = (b1 || b2) as u64;
    }
    r
}
fn raw_add(a: &Fe, b: &Fe) -> Fe {
    let mut r = [0u64; 4];
    let mut carry = 0u64;
    for i in 0..4 {
        let (s, c1) = a[i].overflowing_add(b[i]);
        let (s, c2) = s.overflowing_add(carry);
        r[i] = s;
        carry = (c1 || c2) as u64;
    }
    r
}
/// a + b mod p for a, b < p (the sum is below 2^256).
fn add(a: &Fe, b: &Fe) -> Fe {
    let s = raw_add(a, b);
    if ge(&s, &P) { raw_sub(&s, &P) } else { s }
}
fn sub(a: &Fe, b: &Fe) -> Fe {
    if ge(a, b) { raw_sub(a, b) } else { raw_sub(&raw_add(a, &P), b) }
}
fn mul(a: &Fe, b: &Fe) -> Fe {
    let mut r = [0u64; 4];
    for i in (0..256).rev() {
        r = add(&r, &r);
        if (b[i / 64] >> (i % 64)) & 1 == 1 {
            r = add(&r, a);
        }
    }
    r
}
fn inv(a: &Fe) -> Fe {
    let e = raw_sub(&P, &[2, 0, 0, 0]);
    let mut r = [1, 0, 0, 0];
    for i in (0..256).rev() {
        r = mul(&r, &r);
        if (e[i / 64] >> (i % 64)) & 1 == 1 {
            r = mul(&r, a);
        }
    }
    r
}
fn fe_of(b: &[u8; 32]) -> Fe {
    let mut r = [0u64; 4];
    for (i, limb) in r.iter_mut().enumerate() {
        *limb = u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap());
    }
    r
}
fn bytes_of(f: &Fe) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * i + 8].copy_from_slice(&f[i].to_le_bytes());
    }
    out
}

// ---- the ideal functionality, one stand-in per party

/// Where the two stand-ins exchange their private contributions to one interactive call.
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
            let (g, t) = self.cv.wait_timeout(slots, Duration::from_secs(20)).unwrap();
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
    /// Every engine call made, by name.
    log: Vec<&'static str>,
}

impl Ideal {
    fn new(party: usize, meeting: Arc<Meeting>) -> Ideal {
        Ideal { party, meeting, calls: 0, next: 1, bools: HashMap::new(), fields: HashMap::new(), circuits: HashMap::new(), log: vec![] }
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

fn byte_bits(b: u8) -> Vec<u8> {
    (0..8).map(|i| (b >> i) & 1).collect()
}
fn bits_byte(bits: &[u8]) -> u8 {
    bits.iter().enumerate().map(|(i, &b)| b << i).sum()
}

/// The stand-in circuits: `tls-reveal 7` (HybridKernels.tlsReveal) and `toy` (identity on 4 bits).
fn eval(name: &str, input: &[u8]) -> Vec<u8> {
    match name {
        "tls-reveal 7" => {
            let byte = |at: usize| bits_byte(&input[at..at + 8]);
            let picked = (0..7).fold(0u8, |acc, i| acc ^ (byte(16 + 8 * i) & byte(72 + 8 * i)));
            [input[..16].to_vec(), byte_bits(picked)].concat()
        }
        "toy" => input.to_vec(),
        other => panic!("no stand-in for {other}"),
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
        self.log.push("circuit_load");
        let name = path.strip_prefix("fake/").ok_or("path")?.to_string();
        let shape = match name.as_str() {
            "tls-reveal 7" => (128, 24),
            "toy" => (4, 4),
            _ => return Err("no such circuit".into()),
        };
        let h = self.handle();
        self.circuits.insert(h, name);
        Ok((h, shape.0, shape.1))
    }
    fn bool_input_private(&mut self, owner: u8, bits: &[u8]) -> Result<u64, String> {
        self.log.push("bool_input_private");
        let both = self.meet(bits.to_vec());
        assert_eq!(both[0].len(), both[1].len(), "the non-owner passes width placeholder bits");
        Ok(self.put_bool(both[owner as usize].clone()))
    }
    fn bool_input_both(&mut self, bits: &[u8]) -> Result<(u64, u64), String> {
        self.log.push("bool_input_both");
        let both = self.meet(bits.to_vec());
        Ok((self.put_bool(both[0].clone()), self.put_bool(both[1].clone())))
    }
    fn bool_public(&mut self, bits: &[u8]) -> Result<u64, String> {
        self.log.push("bool_public");
        Ok(self.put_bool(bits.to_vec()))
    }
    fn bool_run(&mut self, circuit: u64, copies: u32, input: u64) -> Result<u64, String> {
        self.log.push("bool_run");
        let name = self.circuits.get(&circuit).ok_or("circuit")?.clone();
        let v = self.bool(input)?;
        let per = v.len() / copies as usize;
        let out = (0..copies as usize).flat_map(|j| eval(&name, &v[j * per..(j + 1) * per])).collect();
        Ok(self.put_bool(out))
    }
    fn bool_open(&mut self, h: u64, count: usize) -> Result<Vec<u8>, String> {
        self.log.push("bool_open");
        let v = self.bool(h)?;
        if v.len() != count {
            return Err("opened width".into());
        }
        Ok(v)
    }
    fn bool_open_to(&mut self, h: u64, recipient: u8, count: usize) -> Result<Vec<u8>, String> {
        self.log.push("bool_open_to");
        let v = self.bool(h)?;
        if v.len() != count {
            return Err("opened width".into());
        }
        Ok(if recipient as usize == self.party { v } else { vec![0; count] })
    }
    fn bool_concat(&mut self, hs: &[u64]) -> Result<u64, String> {
        self.log.push("bool_concat");
        let mut v = vec![];
        for &h in hs {
            v.extend(self.bool(h)?);
        }
        Ok(self.put_bool(v))
    }
    fn bool_pick(&mut self, h: u64, indices: &[u64]) -> Result<u64, String> {
        self.log.push("bool_pick");
        let v = self.bool(h)?;
        Ok(self.put_bool(indices.iter().map(|&i| v[i as usize]).collect()))
    }
    fn bool_slice(&mut self, h: u64, lo: usize, hi: usize) -> Result<u64, String> {
        self.log.push("bool_slice");
        let v = self.bool(h)?;
        Ok(self.put_bool(v[lo..hi].to_vec()))
    }
    fn bool_free(&mut self, h: u64) -> Result<(), String> {
        self.log.push("bool_free");
        self.bools.remove(&h).map(|_| ()).ok_or_else(|| "unknown handle".into())
    }
    fn field_input_coins(&mut self, local: &[u64]) -> Result<(Vec<u64>, Vec<u64>), String> {
        self.log.push("field_input_coins");
        let both = self.meet(local.iter().flat_map(|c| c.to_le_bytes()).collect());
        let take = |s: &mut Self, b: &[u8]| -> Vec<u64> {
            b.chunks(8).map(|c| s.put_field([u64::from_le_bytes(c.try_into().unwrap()), 0, 0, 0])).collect()
        };
        Ok((take(self, &both[0]), take(self, &both[1])))
    }
    fn field_input_elements(&mut self, local: &[[u8; 32]]) -> Result<(Vec<u64>, Vec<u64>), String> {
        self.log.push("field_input_elements");
        let both = self.meet(local.concat());
        let take = |s: &mut Self, b: &[u8]| -> Vec<u64> { b.chunks(32).map(|c| s.put_field(fe_of(c.try_into().unwrap()))).collect() };
        Ok((take(self, &both[0]), take(self, &both[1])))
    }
    fn field_constant(&mut self, value: u64) -> Result<u64, String> {
        self.log.push("field_constant");
        Ok(self.put_field([value, 0, 0, 0]))
    }
    fn field_public(&mut self, value: &[u8; 32]) -> Result<u64, String> {
        self.log.push("field_public");
        Ok(self.put_field(fe_of(value)))
    }
    fn field_add(&mut self, a: u64, b: u64) -> Result<u64, String> {
        self.log.push("field_add");
        let v = add(&self.field(a)?, &self.field(b)?);
        Ok(self.put_field(v))
    }
    fn field_sub(&mut self, a: u64, b: u64) -> Result<u64, String> {
        self.log.push("field_sub");
        let v = sub(&self.field(a)?, &self.field(b)?);
        Ok(self.put_field(v))
    }
    fn field_scale(&mut self, a: u64, constant: u64) -> Result<u64, String> {
        self.log.push("field_scale");
        let v = mul(&self.field(a)?, &[constant, 0, 0, 0]);
        Ok(self.put_field(v))
    }
    fn field_divide_public(&mut self, a: u64, c: &[u8; 32]) -> Result<u64, String> {
        self.log.push("field_divide_public");
        let v = mul(&self.field(a)?, &inv(&fe_of(c)));
        Ok(self.put_field(v))
    }
    fn field_mul(&mut self, a: &[u64], b: &[u64]) -> Result<Vec<u64>, String> {
        self.log.push("field_mul");
        let mut outs = vec![];
        for (&x, &y) in a.iter().zip(b) {
            let v = mul(&self.field(x)?, &self.field(y)?);
            outs.push(self.put_field(v));
        }
        Ok(outs)
    }
    fn field_check(&mut self) -> Result<(), String> {
        self.log.push("field_check");
        Ok(())
    }
    fn field_checked_open(&mut self, hs: &[u64]) -> Result<Vec<[u8; 32]>, String> {
        self.log.push("field_checked_open");
        hs.iter().map(|&h| self.field(h).map(|v| bytes_of(&v))).collect()
    }
    fn field_free(&mut self, h: u64) -> Result<(), String> {
        self.log.push("field_free");
        self.fields.remove(&h).map(|_| ()).ok_or_else(|| "unknown handle".into())
    }
}

// ---- two shells

fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

fn kernels() -> Kernels {
    let text = common::text();
    let mut k = Kernels::default();
    for (name, sig) in common::sigs(&text) {
        let path = format!("fake/{}", String::from_utf8(name.clone()).unwrap());
        k.insert(&name, Kernel { flat: path.into(), sha256: String::new(), sig });
    }
    k
}

type Pair = (Shell<Ideal>, Shell<Ideal>);

fn pair() -> Pair {
    let port = free_port();
    let wait = Some(Duration::from_secs(20));
    let leader = std::thread::spawn(move || Link::listen(Some(Ipv4Addr::LOCALHOST), port).unwrap());
    let mut b = Link::dial(Ipv4Addr::LOCALHOST, port, wait).unwrap();
    let mut a = leader.join().unwrap();
    let t = std::thread::spawn(move || {
        a.hello(&[5; 32], wait).unwrap();
        a
    });
    b.hello(&[5; 32], wait).unwrap();
    let a = t.join().unwrap();
    let meeting = Arc::new(Meeting::default());
    let mut sa = Shell::new(true, "s".into(), a, Ideal::new(0, meeting.clone()), wait);
    let mut sb = Shell::new(false, "s".into(), b, Ideal::new(1, meeting), wait);
    sa.kernels = kernels();
    sb.kernels = kernels();
    (sa, sb)
}

type Results = (Result<Vec<u8>, String>, Result<Vec<u8>, String>);

/// Both shells run one request at once.
fn both(p: Pair, code: u8, seq: u64, pa: Vec<u8>, pb: Vec<u8>) -> (Pair, Results) {
    let (a, mut b) = p;
    let t = std::thread::spawn(move || {
        let mut a = a;
        let r = a.call(code, seq, &pa);
        (a, r)
    });
    let rb = b.call(code, seq, &pb);
    let (a, ra) = t.join().unwrap();
    ((a, b), (ra, rb))
}

#[test]
fn lean_flows_on_two_shells() {
    let text = common::text();
    let flows = common::flows(&text);
    assert_eq!(flows.iter().map(|f| f.name.as_str()).collect::<Vec<_>>(), ["random-joint", "upgrade-public", "bool", "field"]);
    for flow in flows {
        let mut p = pair();
        for (seq, round) in flow.rounds.iter().enumerate() {
            let (np, (ra, rb)) = both(p, BATCH, seq as u64, round.batch[0].clone(), round.batch[1].clone());
            p = np;
            assert_eq!(ra.as_deref(), Ok(&round.reply[0][..]), "{} round {seq}: party A's reply", flow.name);
            assert_eq!(rb.as_deref(), Ok(&round.reply[1][..]), "{} round {seq}: party B's reply", flow.name);
        }
        // Every engine value the flow created and did not open-and-keep is accounted for: the
        // stand-ins hold exactly the live Lean handles.
        assert_eq!(p.0.engines.bools.len(), p.0.interp.ctx.bools.len(), "{}", flow.name);
        assert_eq!(p.0.engines.fields.len(), p.0.interp.ctx.fields.len(), "{}", flow.name);
        eprintln!("stand-in: flow {} ok ({} rounds)", flow.name, flow.rounds.len());
    }
}

#[test]
fn every_instruction_on_two_shells() {
    let text = common::text();
    let cases = common::cases(&text);
    let get = |name: &str| cases.iter().find(|(n, _)| n == name).unwrap().1.clone();
    let (ba, bb) = (get("all-a"), get("all-b"));
    let mut p = pair();
    let mut replies = vec![];
    for (seq, (a, b)) in ba.iter().zip(&bb).enumerate() {
        let (np, (ra, rb)) = both(p, BATCH, seq as u64, a.clone(), b.clone());
        p = np;
        replies.push((decode_replies(&ra.unwrap()).unwrap(), decode_replies(&rb.unwrap()).unwrap()));
    }
    // Batch 1 ends in openBoolTo to A: A gets toy(input 1)[1..2] = [0]; B gets no item.
    assert_eq!(replies[0], (vec![Datum::Bits(vec![false])], vec![]));
    // Batch 2: openBool of (input 1 ++ A's both-input)[0..4] = 1011, to both.
    let opened = Datum::Bits(vec![true, false, true, true]);
    assert_eq!(replies[1], (vec![opened.clone()], vec![opened]));
    // Batch 3: openField [9, 10]; 10 = x_A1 * x_A2 = 11 * 22.
    let (Datum::Elems(va), Datum::Elems(vb)) = (&replies[2].0[0], &replies[2].1[0]) else { panic!("elements") };
    assert_eq!(va, vb);
    assert_eq!(fe_of(&va[1]), [242, 0, 0, 0]);
    // Batch 4: the exchange.
    assert_eq!(replies[3], (vec![Datum::Bytes(vec![6, 7, 8, 9, 10])], vec![Datum::Bytes(vec![1, 2, 3, 4, 5])]));
    // Consumed once handles (2, 3, 5, 6, 7) and freed ones are gone from the engine too.
    assert_eq!(p.0.engines.bools.len(), p.0.interp.ctx.bools.len());
    assert_eq!(p.1.engines.fields.len(), p.1.interp.ctx.fields.len());
    // Every engine call of the instruction set was made.
    let mut calls = p.0.engines.log.clone();
    calls.sort();
    calls.dedup();
    assert_eq!(calls.len(), 22, "{calls:?}");
}

#[test]
fn refusals_on_two_shells() {
    let text = common::text();
    let cases = common::cases(&text);
    let get = |name: &str| cases.iter().find(|(n, _)| n == name).unwrap().1.clone();

    // Party B's wires of a case written for party A: A's own inputs carry no bits at B.
    let for_b = |bytes: &[u8]| {
        let mut batch = decode_batch(bytes).unwrap();
        for w in &mut batch {
            if let Wire::BoolInput { owner: Party::A, bits, .. } = w {
                bits.clear();
            }
        }
        encode_batch(&batch)
    };

    // `check` refuses the whole batch on both sides before any engine call (instruction 3 of 4).
    let mid = get("refused-mid-batch");
    let p = pair();
    let (p, (ra, rb)) = both(p, BATCH, 0, mid[0].clone(), for_b(&mid[0]));
    assert!(ra.is_ok() && rb.is_ok());
    let calls = p.0.engines.log.len();
    let (p, (ra, rb)) = both(p, BATCH, 1, mid[1].clone(), for_b(&mid[1]));
    assert_eq!(ra.unwrap_err(), "instruction 2 refused by check");
    assert_eq!(rb.unwrap_err(), "instruction 2 refused by check");
    assert_eq!(p.0.engines.log.len(), calls, "nothing of a refused batch runs");

    // Different skeletons: both refuse at the agreement.
    let p = pair();
    let x = encode_batch(&[Wire::Exchange { len: 1, label: 9, payload: vec![1] }]);
    let y = encode_batch(&[Wire::Exchange { len: 1, label: 8, payload: vec![1] }]);
    let (p, (ra, rb)) = both(p, BATCH, 0, x.clone(), y);
    assert_eq!((ra.unwrap_err(), rb.unwrap_err()), ("request disagreement".to_string(), "request disagreement".to_string()));
    drop(p);

    // Same skeleton, different private payloads: agreed (only the skeleton is).
    let p = pair();
    let y = encode_batch(&[Wire::Exchange { len: 1, label: 9, payload: vec![2] }]);
    let (p, (ra, rb)) = both(p, BATCH, 0, x.clone(), y);
    assert_eq!((ra.unwrap(), rb.unwrap()), (vec![1, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 2], vec![1, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1]));

    // A payload that does not fit its skeleton: that party says why, the other stops at the
    // agreement instead of waiting in the exchange.
    let short = encode_batch(&[Wire::Exchange { len: 2, label: 9, payload: vec![1] }]);
    let fits = encode_batch(&[Wire::Exchange { len: 2, label: 9, payload: vec![1, 2] }]);
    let (p, (ra, rb)) = both(p, BATCH, 1, short, fits);
    assert_eq!(ra.unwrap_err(), "private payload of instruction 0 does not fit its skeleton");
    assert_eq!(rb.unwrap_err(), "request disagreement");
    drop(p);

    // An undecodable batch, likewise.
    let p = pair();
    let mut bad = x.clone();
    bad.push(0);
    assert_eq!(decode_batch(&bad), None);
    let (_p, (ra, rb)) = both(p, BATCH, 0, bad, x);
    assert_eq!(ra.unwrap_err(), "batch encoding");
    assert_eq!(rb.unwrap_err(), "request disagreement");
}
