//! The engine instruction set's interpreter (REORGANIZATION_PLAN.md 5.1, 5.2; stage S9): pipe
//! operation [`BATCH`] carries one batch of agreed instructions, specified byte for byte by
//! `TlsMpc/Node/Engine.lean` (its top design note is the specification; Lean names are given
//! next to each part here).
//!
//! One batch, in this order ([`crate::shell::Shell`] drives it):
//! 1. [`decode_batch`] (Lean `decodeBatch`): u64 little-endian numbers, lists as a count then the
//!    items, bits and flags one byte 0/1, field elements 32 bytes little-endian below
//!    p = 2^255 - 19, opcodes 1-22; nothing may follow the batch.
//! 2. [`validate_payloads`]: this party's private payloads have the shapes the skeleton declares
//!    (design note item 5, Lean `Wire.payloadOk`: `fill`'s conditions). 1 and 2 together are
//!    Lean `usableBatch` ([`usable_batch`]).
//! 3. Agreement on [`agreed_bytes`] (Lean `agreedBytes`): [`skeleton_bytes`] (Lean
//!    `skeletonBytes`: the batch with every private payload emptied, re-encoded) through
//!    `agree.rs`. A batch this party cannot decode or whose payloads do not fit is agreed as
//!    [`UNUSABLE`] (Lean `unusable`), so the other party fails at the agreement instead of
//!    waiting inside an engine call (Lean `unusable_rejected_by_both`).
//! 4. [`Interp::admit`]: Lean `checkBatch` (handles.rs [`handles::check_batch`]: `check` per
//!    instruction, and decision D8, a release must be the batch's last instruction) over the
//!    WHOLE batch before the first engine call, from the context carried across batches; a
//!    refusal rejects the batch and nothing runs.
//! 5. [`Interp::execute`]: each instruction through the engine ABI (opcodes map 1:1 to
//!    `ea_bool_*` / `ea_field_*`, opcode 21 to the control link's exchange, opcode 22 to
//!    program.rs's evaluator of a loaded V3 field program), collecting the reply
//!    items (Lean `encodeReplies`): one datum per release to this party ([`Wire::releases_to`],
//!    not the check's shape: `openBoolTo` has shape unit but gives its recipient an item), in
//!    order.
//!
//! Handles: the Lean script names handles (two name spaces, Boolean and field); the engines issue
//! their own. [`Interp`] maps the first to the second. The lifetime rule (design note item 5):
//! an engine value lives as long as its Lean handle is live; an explicit free releases it at
//! once, and a Boolean handle consumed as a `once` operand, or a field mask consumed by a
//! program, is released in the engine at the end of the batch.
use crate::engines::Engines;
use crate::handles::{self, Ctx, Shape, Sig};
use crate::loader::{Kernels, Programs};
use crate::program;
use std::collections::HashMap;

/// The pipe operation code of a batch: the next free code after the shell's 90-92.
pub const BATCH: u8 = 93;

/// Lean `unusable`: what is agreed in place of the skeleton when this party's batch is unusable
/// (undecodable, or private payloads that do not fit it). It never equals a batch's skeleton
/// bytes (Lean `skeletonBytes_ne_unusable`: its first byte, 117, would be the low byte of an
/// instruction count that its 14 bytes cannot hold).
pub const UNUSABLE: &[u8] = b"unusable batch";

/// A field element: 32 bytes little-endian, below p (Lean `F`).
pub type Felt = [u8; 32];

/// p = 2^255 - 19, little-endian.
pub const MODULUS: Felt = {
    let mut p = [0xffu8; 32];
    p[0] = 0xed;
    p[31] = 0x7f;
    p
};

/// Whether 32 little-endian bytes are a canonical element (below p).
pub fn canonical(v: &Felt) -> bool {
    for i in (0..32).rev() {
        if v[i] != MODULUS[i] {
            return v[i] < MODULUS[i];
        }
    }
    false
}

/// Lean `Party`: A is the leader (ABI party 0), B dials (ABI party 1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Party {
    A,
    B,
}

impl Party {
    /// The ABI's party number (0 or 1), also the pipe byte.
    pub fn index(self) -> u8 {
        match self {
            Party::A => 0,
            Party::B => 1,
        }
    }
}

/// Lean `FieldIn`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldIn {
    Coins,
    Elements,
}

/// Lean `Wire` (= `InstrP Bits (List F) Bytes Unit`): one instruction as the pipe carries it.
/// The private payloads (Lean's starred fields) are `bits` of the two inputs, `elements` of
/// `FieldInput` and `payload` of `Exchange`; everything else is the agreed skeleton.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Wire {
    BoolInput { out: u64, owner: Party, width: u64, once: bool, revealable: bool, bits: Vec<bool> },
    BoolInputBoth { out_a: u64, out_b: u64, width: u64, once: bool, revealable: bool, bits: Vec<bool> },
    BoolPublic { out: u64, bits: Vec<bool> },
    Run { out: u64, circuit: Vec<u8>, copies: u64, input: u64 },
    Concat { out: u64, parts: Vec<u64> },
    Slice { out: u64, h: u64, lo: u64, hi: u64 },
    Pick { out: u64, h: u64, indices: Vec<u64> },
    OpenBool { h: u64, label: u64 },
    OpenBoolTo { h: u64, recipient: Party, label: u64 },
    FreeBool { h: u64 },
    FieldInput { outs_a: Vec<u64>, outs_b: Vec<u64>, kind: FieldIn, revealable: bool, elements: Vec<Felt> },
    FieldPublic { out: u64, v: Felt },
    FieldAdd { out: u64, a: u64, b: u64 },
    FieldSub { out: u64, a: u64, b: u64 },
    FieldScale { out: u64, a: u64, c: u64 },
    FieldDivide { out: u64, a: u64, c: Felt },
    FieldMul { outs: Vec<u64>, pairs: Vec<(u64, u64)> },
    FieldCheck,
    OpenField { hs: Vec<u64>, label: u64 },
    FreeField { h: u64 },
    Exchange { len: u64, label: u64, payload: Vec<u8> },
    /// Opcode 22: `copies` instances of a V3 field program (program.rs).
    Program { name: Vec<u8>, copies: u64, ins: Vec<u64>, masks: Vec<u64>, outs: Vec<u64>, label: u64 },
}

impl Wire {
    /// Lean `w.skel.blank`: every private payload replaced by the empty list.
    pub fn blank(&self) -> Wire {
        let mut w = self.clone();
        match &mut w {
            Wire::BoolInput { bits, .. } | Wire::BoolInputBoth { bits, .. } => bits.clear(),
            Wire::FieldInput { elements, .. } => elements.clear(),
            Wire::Exchange { payload, .. } => payload.clear(),
            _ => {}
        }
        w
    }
    /// Lean `InstrP.releasesTo`.
    pub fn releases_to(&self, me: Party) -> bool {
        match self {
            Wire::OpenBool { .. } | Wire::OpenField { .. } | Wire::Exchange { .. } | Wire::Program { .. } => true,
            Wire::OpenBoolTo { recipient, .. } => *recipient == me,
            _ => false,
        }
    }
    /// Lean `InstrP.endsBatch` (decision D8): the releases whose data the script reads (not
    /// `program`, whose openings the script does not read; decision D14).
    pub fn ends_batch(&self) -> bool {
        matches!(self, Wire::OpenBool { .. } | Wire::OpenBoolTo { .. } | Wire::OpenField { .. } | Wire::Exchange { .. })
    }
}

/// Lean `Datum`: one reply item.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Datum {
    Bits(Vec<bool>),
    Elems(Vec<Felt>),
    Bytes(Vec<u8>),
}

// ---- encoding (Lean `Enc`, `encWire`, `encodeBatch`, `skeletonBytes`, `encDatum`, `encodeReplies`)

struct Out(Vec<u8>);

impl Out {
    fn u64(&mut self, n: u64) {
        self.0.extend_from_slice(&n.to_le_bytes());
    }
    fn byte(&mut self, b: u8) {
        self.0.push(b);
    }
    fn flag(&mut self, b: bool) {
        self.0.push(b as u8);
    }
    fn party(&mut self, p: Party) {
        self.0.push(p.index());
    }
    fn felt(&mut self, v: &Felt) {
        self.0.extend_from_slice(v);
    }
    fn len(&mut self, n: usize) {
        self.u64(n as u64);
    }
    fn u64s(&mut self, l: &[u64]) {
        self.len(l.len());
        for &x in l {
            self.u64(x);
        }
    }
    fn bits(&mut self, l: &[bool]) {
        self.len(l.len());
        for &b in l {
            self.flag(b);
        }
    }
    fn bytes(&mut self, l: &[u8]) {
        self.len(l.len());
        self.0.extend_from_slice(l);
    }
    fn felts(&mut self, l: &[Felt]) {
        self.len(l.len());
        for v in l {
            self.felt(v);
        }
    }
}

/// Lean `encWire`.
fn enc_wire(o: &mut Out, w: &Wire) {
    match w {
        Wire::BoolInput { out, owner, width, once, revealable, bits } => {
            o.byte(1);
            o.u64(*out);
            o.party(*owner);
            o.u64(*width);
            o.flag(*once);
            o.flag(*revealable);
            o.bits(bits);
        }
        Wire::BoolInputBoth { out_a, out_b, width, once, revealable, bits } => {
            o.byte(2);
            o.u64(*out_a);
            o.u64(*out_b);
            o.u64(*width);
            o.flag(*once);
            o.flag(*revealable);
            o.bits(bits);
        }
        Wire::BoolPublic { out, bits } => {
            o.byte(3);
            o.u64(*out);
            o.bits(bits);
        }
        Wire::Run { out, circuit, copies, input } => {
            o.byte(4);
            o.u64(*out);
            o.bytes(circuit);
            o.u64(*copies);
            o.u64(*input);
        }
        Wire::Concat { out, parts } => {
            o.byte(5);
            o.u64(*out);
            o.u64s(parts);
        }
        Wire::Slice { out, h, lo, hi } => {
            o.byte(6);
            o.u64(*out);
            o.u64(*h);
            o.u64(*lo);
            o.u64(*hi);
        }
        Wire::Pick { out, h, indices } => {
            o.byte(7);
            o.u64(*out);
            o.u64(*h);
            o.u64s(indices);
        }
        Wire::OpenBool { h, label } => {
            o.byte(8);
            o.u64(*h);
            o.u64(*label);
        }
        Wire::OpenBoolTo { h, recipient, label } => {
            o.byte(9);
            o.u64(*h);
            o.party(*recipient);
            o.u64(*label);
        }
        Wire::FreeBool { h } => {
            o.byte(10);
            o.u64(*h);
        }
        Wire::FieldInput { outs_a, outs_b, kind, revealable, elements } => {
            o.byte(11);
            o.u64s(outs_a);
            o.u64s(outs_b);
            o.byte(match kind {
                FieldIn::Coins => 0,
                FieldIn::Elements => 1,
            });
            o.flag(*revealable);
            o.felts(elements);
        }
        Wire::FieldPublic { out, v } => {
            o.byte(12);
            o.u64(*out);
            o.felt(v);
        }
        Wire::FieldAdd { out, a, b } => {
            o.byte(13);
            o.u64(*out);
            o.u64(*a);
            o.u64(*b);
        }
        Wire::FieldSub { out, a, b } => {
            o.byte(14);
            o.u64(*out);
            o.u64(*a);
            o.u64(*b);
        }
        Wire::FieldScale { out, a, c } => {
            o.byte(15);
            o.u64(*out);
            o.u64(*a);
            o.u64(*c);
        }
        Wire::FieldDivide { out, a, c } => {
            o.byte(16);
            o.u64(*out);
            o.u64(*a);
            o.felt(c);
        }
        Wire::FieldMul { outs, pairs } => {
            o.byte(17);
            o.u64s(outs);
            o.len(pairs.len());
            for &(a, b) in pairs {
                o.u64(a);
                o.u64(b);
            }
        }
        Wire::FieldCheck => o.byte(18),
        Wire::OpenField { hs, label } => {
            o.byte(19);
            o.u64s(hs);
            o.u64(*label);
        }
        Wire::FreeField { h } => {
            o.byte(20);
            o.u64(*h);
        }
        Wire::Exchange { len, label, payload } => {
            o.byte(21);
            o.u64(*len);
            o.u64(*label);
            o.bytes(payload);
        }
        Wire::Program { name, copies, ins, masks, outs, label } => {
            o.byte(22);
            o.bytes(name);
            o.u64(*copies);
            o.u64s(ins);
            o.u64s(masks);
            o.u64s(outs);
            o.u64(*label);
        }
    }
}

/// Lean `encodeBatch`.
pub fn encode_batch(batch: &[Wire]) -> Vec<u8> {
    let mut o = Out(Vec::new());
    o.len(batch.len());
    for w in batch {
        enc_wire(&mut o, w);
    }
    o.0
}

/// Lean `skeletonBytes`: the bytes the agreement hash covers.
pub fn skeleton_bytes(batch: &[Wire]) -> Vec<u8> {
    let mut o = Out(Vec::new());
    o.len(batch.len());
    for w in batch {
        enc_wire(&mut o, &w.blank());
    }
    o.0
}

/// Lean `encodeReplies`.
pub fn encode_replies(replies: &[Datum]) -> Vec<u8> {
    let mut o = Out(Vec::new());
    o.len(replies.len());
    for d in replies {
        match d {
            Datum::Bits(b) => {
                o.byte(1);
                o.bits(b);
            }
            Datum::Elems(v) => {
                o.byte(2);
                o.felts(v);
            }
            Datum::Bytes(b) => {
                o.byte(3);
                o.bytes(b);
            }
        }
    }
    o.0
}

// ---- decoding (Lean `Dec`, `decWire`, `decodeBatch`, `decDatum`, `decodeReplies`). `None` is
// Lean's `none`; each reader consumes from the front of `s` as Lean's decoders return the rest.

struct In<'a> {
    s: &'a [u8],
}

impl<'a> In<'a> {
    /// Lean `Dec.byte`.
    fn byte(&mut self) -> Option<u8> {
        let (&b, rest) = self.s.split_first()?;
        self.s = rest;
        Some(b)
    }
    /// Lean `Dec.take`.
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        if n > self.s.len() {
            return None;
        }
        let (a, b) = self.s.split_at(n);
        self.s = b;
        Some(a)
    }
    /// Lean `Dec.u64` (also `boolH`, `fieldH`, `label`).
    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    /// Lean `Dec.flag`.
    fn flag(&mut self) -> Option<bool> {
        match self.byte()? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }
    /// Lean `Dec.party`.
    fn party(&mut self) -> Option<Party> {
        match self.byte()? {
            0 => Some(Party::A),
            1 => Some(Party::B),
            _ => None,
        }
    }
    /// Lean `Dec.kind`.
    fn kind(&mut self) -> Option<FieldIn> {
        match self.byte()? {
            0 => Some(FieldIn::Coins),
            1 => Some(FieldIn::Elements),
            _ => None,
        }
    }
    /// Lean `Dec.felt`.
    fn felt(&mut self) -> Option<Felt> {
        let v: Felt = self.take(32)?.try_into().unwrap();
        canonical(&v).then_some(v)
    }
    /// Lean `Dec.list d` (`Dec.count d n` after the count). Every item decoder consumes at least
    /// one byte, so at most `s.len()` items are attempted whatever the count says; nothing is
    /// allocated from the count.
    fn list<T>(&mut self, mut d: impl FnMut(&mut Self) -> Option<T>) -> Option<Vec<T>> {
        let n = self.u64()?;
        let mut out = Vec::new();
        for _ in 0..n {
            out.push(d(self)?);
        }
        Some(out)
    }
    fn u64s(&mut self) -> Option<Vec<u64>> {
        self.list(|r| r.u64())
    }
    /// Lean `Dec.bytes`.
    fn bytes(&mut self) -> Option<Vec<u8>> {
        let n = self.u64()?;
        Some(self.take(usize::try_from(n).ok()?)?.to_vec())
    }
    /// Lean `Dec.bits`.
    fn bits(&mut self) -> Option<Vec<bool>> {
        self.list(|r| r.flag())
    }
    /// Lean `Dec.felts`.
    fn felts(&mut self) -> Option<Vec<Felt>> {
        self.list(|r| r.felt())
    }
    /// Lean `Dec.pair`.
    fn pair(&mut self) -> Option<(u64, u64)> {
        let x = self.u64()?;
        let y = self.u64()?;
        Some((x, y))
    }

    /// Lean `decWire`.
    fn wire(&mut self) -> Option<Wire> {
        let r = self;
        Some(match r.byte()? {
            1 => {
                let out = r.u64()?;
                let owner = r.party()?;
                let width = r.u64()?;
                let once = r.flag()?;
                let revealable = r.flag()?;
                let bits = r.bits()?;
                Wire::BoolInput { out, owner, width, once, revealable, bits }
            }
            2 => {
                let out_a = r.u64()?;
                let out_b = r.u64()?;
                let width = r.u64()?;
                let once = r.flag()?;
                let revealable = r.flag()?;
                let bits = r.bits()?;
                Wire::BoolInputBoth { out_a, out_b, width, once, revealable, bits }
            }
            3 => {
                let out = r.u64()?;
                let bits = r.bits()?;
                Wire::BoolPublic { out, bits }
            }
            4 => {
                let out = r.u64()?;
                let circuit = r.bytes()?;
                let copies = r.u64()?;
                let input = r.u64()?;
                Wire::Run { out, circuit, copies, input }
            }
            5 => {
                let out = r.u64()?;
                let parts = r.u64s()?;
                Wire::Concat { out, parts }
            }
            6 => {
                let out = r.u64()?;
                let h = r.u64()?;
                let lo = r.u64()?;
                let hi = r.u64()?;
                Wire::Slice { out, h, lo, hi }
            }
            7 => {
                let out = r.u64()?;
                let h = r.u64()?;
                let indices = r.u64s()?;
                Wire::Pick { out, h, indices }
            }
            8 => {
                let h = r.u64()?;
                let label = r.u64()?;
                Wire::OpenBool { h, label }
            }
            9 => {
                let h = r.u64()?;
                let recipient = r.party()?;
                let label = r.u64()?;
                Wire::OpenBoolTo { h, recipient, label }
            }
            10 => Wire::FreeBool { h: r.u64()? },
            11 => {
                let outs_a = r.u64s()?;
                let outs_b = r.u64s()?;
                let kind = r.kind()?;
                let revealable = r.flag()?;
                let elements = r.felts()?;
                Wire::FieldInput { outs_a, outs_b, kind, revealable, elements }
            }
            12 => {
                let out = r.u64()?;
                let v = r.felt()?;
                Wire::FieldPublic { out, v }
            }
            13 => {
                let out = r.u64()?;
                let a = r.u64()?;
                let b = r.u64()?;
                Wire::FieldAdd { out, a, b }
            }
            14 => {
                let out = r.u64()?;
                let a = r.u64()?;
                let b = r.u64()?;
                Wire::FieldSub { out, a, b }
            }
            15 => {
                let out = r.u64()?;
                let a = r.u64()?;
                let c = r.u64()?;
                Wire::FieldScale { out, a, c }
            }
            16 => {
                let out = r.u64()?;
                let a = r.u64()?;
                let c = r.felt()?;
                Wire::FieldDivide { out, a, c }
            }
            17 => {
                let outs = r.u64s()?;
                let pairs = r.list(|r| r.pair())?;
                Wire::FieldMul { outs, pairs }
            }
            18 => Wire::FieldCheck,
            19 => {
                let hs = r.u64s()?;
                let label = r.u64()?;
                Wire::OpenField { hs, label }
            }
            20 => Wire::FreeField { h: r.u64()? },
            21 => {
                let len = r.u64()?;
                let label = r.u64()?;
                let payload = r.bytes()?;
                Wire::Exchange { len, label, payload }
            }
            22 => {
                let name = r.bytes()?;
                let copies = r.u64()?;
                let ins = r.u64s()?;
                let masks = r.u64s()?;
                let outs = r.u64s()?;
                let label = r.u64()?;
                Wire::Program { name, copies, ins, masks, outs, label }
            }
            _ => return None,
        })
    }
}

/// Lean `decodeBatch`: the whole input, nothing after it.
pub fn decode_batch(s: &[u8]) -> Option<Vec<Wire>> {
    let mut r = In { s };
    let batch = r.list(|r| r.wire())?;
    r.s.is_empty().then_some(batch)
}

/// Lean `decodeReplies` (for the controller side and the tests).
pub fn decode_replies(s: &[u8]) -> Option<Vec<Datum>> {
    let mut r = In { s };
    let items = r.list(|r| match r.byte()? {
        1 => Some(Datum::Bits(r.bits()?)),
        2 => Some(Datum::Elems(r.felts()?)),
        3 => Some(Datum::Bytes(r.bytes()?)),
        _ => None,
    })?;
    r.s.is_empty().then_some(items)
}

/// Lean `Wire.payloadOk` on every instruction (design note item 5; `fill`'s conditions, checked
/// on what arrived): an input owner's bits and both parties' `boolInputBoth` bits number
/// `width`; the non-owner's `boolInput` payload is empty; a `fieldInput`'s elements number
/// `outsA`'s length, and coins are below 2^64; an exchange payload has exactly `len` bytes.
pub fn validate_payloads(me: Party, batch: &[Wire]) -> Result<(), String> {
    for (i, w) in batch.iter().enumerate() {
        let ok = match w {
            Wire::BoolInput { owner, width, bits, .. } => {
                if *owner == me { bits.len() as u64 == *width } else { bits.is_empty() }
            }
            Wire::BoolInputBoth { width, bits, .. } => bits.len() as u64 == *width,
            Wire::FieldInput { outs_a, kind, elements, .. } => {
                elements.len() == outs_a.len() && (*kind == FieldIn::Elements || elements.iter().all(|v| v[8..].iter().all(|&b| b == 0)))
            }
            Wire::Exchange { len, payload, .. } => payload.len() as u64 == *len,
            _ => true,
        };
        if !ok {
            return Err(format!("private payload of instruction {i} does not fit its skeleton"));
        }
    }
    Ok(())
}

/// Lean `usableBatch`: the batch this party can run from its request bytes (they decode, and
/// every private payload fits its skeleton), or why not.
pub fn usable_batch(me: Party, payload: &[u8]) -> Result<Vec<Wire>, String> {
    let batch = decode_batch(payload).ok_or_else(|| "batch encoding".to_string())?;
    validate_payloads(me, &batch)?;
    Ok(batch)
}

/// Lean `agreedBytes`: what this party puts into the agreement hash for a usable batch (its
/// skeleton bytes) or an unusable one ([`UNUSABLE`]).
pub fn agreed_bytes(usable: &Result<Vec<Wire>, String>) -> Vec<u8> {
    match usable {
        Ok(batch) => skeleton_bytes(batch),
        Err(_) => UNUSABLE.to_vec(),
    }
}

/// What [`Interp::execute`] needs from the check of one instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Step {
    pub shape: Shape,
    /// For `openBoolTo`: the handle's width (the bits the engine opens).
    pub width: u64,
}

fn bit_bytes(bits: &[bool]) -> Vec<u8> {
    bits.iter().map(|&b| b as u8).collect()
}

/// The interpreter's state, carried across batches for the whole session.
#[derive(Debug, Default)]
pub struct Interp {
    /// Lean `Ctx`, from the empty one at session start.
    pub ctx: Ctx,
    /// Lean Boolean handle id -> engine handle.
    bools: HashMap<u64, u64>,
    /// Lean field handle id -> engine handle.
    fields: HashMap<u64, u64>,
    /// Circuit name -> engine circuit handle (loaded at first use).
    circuits: HashMap<Vec<u8>, u64>,
}

impl Interp {
    /// Lean `checkBatch` over the whole batch from the carried context ([`handles::check_batch`],
    /// with the widths `openBoolTo` needs). On success the context moves past the batch; on a
    /// refusal nothing changes and the batch must not run.
    pub fn admit(&mut self, sigs: &dyn Fn(&[u8]) -> Option<Sig>, batch: &[Wire]) -> Result<Vec<Step>, String> {
        // Checked in place with an undo journal (a refusal rolls the context back), not on a copy:
        // the copy held every id the session ever used and grew with it.
        self.ctx.begin();
        let r = self.admit_in_place(sigs, batch);
        if r.is_ok() {
            self.ctx.commit();
        } else {
            self.ctx.rollback();
        }
        r
    }

    fn admit_in_place(&mut self, sigs: &dyn Fn(&[u8]) -> Option<Sig>, batch: &[Wire]) -> Result<Vec<Step>, String> {
        let work = &mut self.ctx;
        let mut steps = Vec::with_capacity(batch.len());
        for (i, w) in batch.iter().enumerate() {
            let width = match w {
                Wire::OpenBoolTo { h, .. } => work.bool(*h).map_or(0, |b| b.marks.len() as u64),
                _ => 0,
            };
            // The refusal names the instruction's skeleton (`blank`: no private payload; the
            // skeleton is what both workers agree on, public by construction), cut to 240 chars;
            // for `run`, also the circuit's signature width and the input handle's width (public).
            let widths = match w {
                Wire::Run { circuit, input, .. } => format!(
                    " [circuit in_width {:?}, out {:?}; input width {:?}]",
                    sigs(circuit).map(|s| s.in_width),
                    sigs(circuit).map(|s| s.out_marks.len()),
                    work.bool(*input).map(|b| b.marks.len())
                ),
                _ => String::new(),
            };
            let shape = handles::check(sigs, work, w).ok_or_else(|| {
                let skel = format!("{:?}", w.blank());
                format!("instruction {i} refused by check: {}{widths}", &skel[..skel.len().min(240)])
            })?;
            if w.ends_batch() && i + 1 < batch.len() {
                return Err(format!("instruction {i} releases data but does not end the batch"));
            }
            steps.push(Step { shape, width });
        }
        Ok(steps)
    }

    fn bool_handle(&self, id: u64) -> Result<u64, String> {
        self.bools.get(&id).copied().ok_or_else(|| format!("Boolean handle {id} has no engine value"))
    }
    fn field_handle(&self, id: u64) -> Result<u64, String> {
        self.fields.get(&id).copied().ok_or_else(|| format!("field handle {id} has no engine value"))
    }

    /// Runs an admitted batch (`steps` from [`Interp::admit`] on the same batch). `exchange`
    /// sends this party's bytes on the control link and returns the other party's.
    #[allow(clippy::too_many_arguments)]
    pub fn execute<E: Engines>(
        &mut self,
        engines: &mut E,
        kernels: &Kernels,
        programs: &Programs,
        me: Party,
        batch: &[Wire],
        steps: &[Step],
        exchange: &mut dyn FnMut(&[u8]) -> Result<Vec<u8>, String>,
    ) -> Result<Vec<Datum>, String> {
        if steps.len() != batch.len() {
            return Err("batch not admitted".into());
        }
        let mut replies = Vec::new();
        for (w, step) in batch.iter().zip(steps) {
            match w {
                Wire::BoolInput { out, owner, width, bits, .. } => {
                    // The non-owner passes `width` placeholder bits (engine_abi.h).
                    let data = if *owner == me { bit_bytes(bits) } else { vec![0u8; *width as usize] };
                    let h = engines.bool_input_private(owner.index(), &data)?;
                    self.bools.insert(*out, h);
                }
                Wire::BoolInputBoth { out_a, out_b, bits, .. } => {
                    let (a, b) = engines.bool_input_both(&bit_bytes(bits))?;
                    self.bools.insert(*out_a, a);
                    self.bools.insert(*out_b, b);
                }
                Wire::BoolPublic { out, bits } => {
                    let h = engines.bool_public(&bit_bytes(bits))?;
                    self.bools.insert(*out, h);
                }
                Wire::Run { out, circuit, copies, input } => {
                    let c = match self.circuits.get(circuit) {
                        Some(&c) => c,
                        None => {
                            let k = kernels.get(circuit).ok_or("circuit not in the manifest")?;
                            let flat = k.flat.to_str().ok_or("circuit path")?;
                            let (c, inputs, outputs) = engines.circuit_load(flat, &k.sha256)?;
                            if inputs as u64 != k.sig.in_width || outputs as usize != k.sig.out_marks.len() {
                                return Err("circuit shape differs from its layout".into());
                            }
                            self.circuits.insert(circuit.clone(), c);
                            c
                        }
                    };
                    let copies = u32::try_from(*copies).map_err(|_| "copies")?;
                    let h = engines.bool_run(c, copies, self.bool_handle(*input)?)?;
                    self.bools.insert(*out, h);
                }
                Wire::Concat { out, parts } => {
                    let hs = parts.iter().map(|&p| self.bool_handle(p)).collect::<Result<Vec<_>, _>>()?;
                    let h = engines.bool_concat(&hs)?;
                    self.bools.insert(*out, h);
                }
                Wire::Slice { out, h, lo, hi } => {
                    let r = engines.bool_slice(self.bool_handle(*h)?, *lo as usize, *hi as usize)?;
                    self.bools.insert(*out, r);
                }
                Wire::Pick { out, h, indices } => {
                    let r = engines.bool_pick(self.bool_handle(*h)?, indices)?;
                    self.bools.insert(*out, r);
                }
                Wire::OpenBool { h, .. } => {
                    let Shape::Bits(n) = step.shape else { return Err("open shape".into()) };
                    let bits = engines.bool_open(self.bool_handle(*h)?, n as usize)?;
                    replies.push(Datum::Bits(bits_of(&bits, n)?));
                }
                Wire::OpenBoolTo { h, recipient, .. } => {
                    let bits = engines.bool_open_to(self.bool_handle(*h)?, recipient.index(), step.width as usize)?;
                    if *recipient == me {
                        replies.push(Datum::Bits(bits_of(&bits, step.width)?));
                    }
                }
                Wire::FreeBool { h } => {
                    engines.bool_free(self.bool_handle(*h)?)?;
                    self.bools.remove(h);
                }
                Wire::FieldInput { outs_a, outs_b, kind, elements, .. } => {
                    let (a, b) = match kind {
                        FieldIn::Coins => {
                            let coins: Vec<u64> = elements.iter().map(|v| u64::from_le_bytes(v[..8].try_into().unwrap())).collect();
                            engines.field_input_coins(&coins)?
                        }
                        FieldIn::Elements => engines.field_input_elements(elements)?,
                    };
                    if a.len() != outs_a.len() || b.len() != outs_b.len() {
                        return Err("field input count".into());
                    }
                    for (id, h) in outs_a.iter().zip(a).chain(outs_b.iter().zip(b)) {
                        self.fields.insert(*id, h);
                    }
                }
                Wire::FieldPublic { out, v } => {
                    // ea_field_constant for values below 2^64 (the same value), else ea_field_public.
                    let h = if v[8..].iter().all(|&b| b == 0) {
                        engines.field_constant(u64::from_le_bytes(v[..8].try_into().unwrap()))?
                    } else {
                        engines.field_public(v)?
                    };
                    self.fields.insert(*out, h);
                }
                Wire::FieldAdd { out, a, b } => {
                    let h = engines.field_add(self.field_handle(*a)?, self.field_handle(*b)?)?;
                    self.fields.insert(*out, h);
                }
                Wire::FieldSub { out, a, b } => {
                    let h = engines.field_sub(self.field_handle(*a)?, self.field_handle(*b)?)?;
                    self.fields.insert(*out, h);
                }
                Wire::FieldScale { out, a, c } => {
                    let h = engines.field_scale(self.field_handle(*a)?, *c)?;
                    self.fields.insert(*out, h);
                }
                Wire::FieldDivide { out, a, c } => {
                    let h = engines.field_divide_public(self.field_handle(*a)?, c)?;
                    self.fields.insert(*out, h);
                }
                Wire::FieldMul { outs, pairs } => {
                    let a = pairs.iter().map(|p| self.field_handle(p.0)).collect::<Result<Vec<_>, _>>()?;
                    let b = pairs.iter().map(|p| self.field_handle(p.1)).collect::<Result<Vec<_>, _>>()?;
                    let hs = engines.field_mul(&a, &b)?;
                    if hs.len() != outs.len() {
                        return Err("field product count".into());
                    }
                    for (id, h) in outs.iter().zip(hs) {
                        self.fields.insert(*id, h);
                    }
                }
                Wire::FieldCheck => engines.field_check()?,
                Wire::OpenField { hs, .. } => {
                    let handles = hs.iter().map(|&h| self.field_handle(h)).collect::<Result<Vec<_>, _>>()?;
                    let values = engines.field_checked_open(&handles)?;
                    if values.len() != hs.len() || !values.iter().all(canonical) {
                        return Err("opened field elements".into());
                    }
                    replies.push(Datum::Elems(values));
                }
                Wire::FreeField { h } => {
                    engines.field_free(self.field_handle(*h)?)?;
                    self.fields.remove(h);
                }
                Wire::Exchange { len, payload, .. } => {
                    let peer = exchange(payload)?;
                    if peer.len() as u64 != *len {
                        return Err("exchange size".into());
                    }
                    replies.push(Datum::Bytes(peer));
                }
                Wire::Program { name, copies, ins, masks, outs, .. } => {
                    let p = programs.get(name).ok_or("field program not loaded")?;
                    let hi = ins.iter().map(|&h| self.field_handle(h)).collect::<Result<Vec<_>, _>>()?;
                    let hm = masks.iter().map(|&h| self.field_handle(h)).collect::<Result<Vec<_>, _>>()?;
                    let (ho, opened) = program::evaluate(engines, p, *copies as usize, &hi, &hm)?;
                    if ho.len() != outs.len() {
                        for h in ho {
                            engines.field_free(h)?;
                        }
                        return Err("field program output count".into());
                    }
                    for (id, h) in outs.iter().zip(ho) {
                        self.fields.insert(*id, h);
                    }
                    // Both parties get the openings (Lean releasesTo); the script reads none.
                    replies.push(Datum::Elems(opened));
                }
            }
        }
        // Engine values whose Lean handles are no longer live (consumed `once` handles, and the
        // masks a program consumed). Only a handle the batch names can have changed (`check`
        // defines, uses and drops only the handles an instruction names), and before the batch
        // every engine value's handle was live: so the batch's own handles are the only
        // candidates (scanning every engine value cost a lookup per live handle per batch).
        let (mut nb, mut nf) = (Vec::new(), Vec::new());
        for w in batch {
            named_handles(w, &mut nb, &mut nf);
        }
        for id in nb {
            if !self.ctx.bools.contains_key(&id) {
                if let Some(h) = self.bools.remove(&id) {
                    engines.bool_free(h)?;
                }
            }
        }
        for id in nf {
            if !self.ctx.fields.contains_key(&id) {
                if let Some(h) = self.fields.remove(&id) {
                    engines.field_free(h)?;
                }
            }
        }
        Ok(replies)
    }
}

/// Every Boolean and field handle an instruction names (defined, read or dropped).
fn named_handles(w: &Wire, b: &mut Vec<u64>, f: &mut Vec<u64>) {
    match w {
        Wire::BoolInput { out, .. } | Wire::BoolPublic { out, .. } => b.push(*out),
        Wire::BoolInputBoth { out_a, out_b, .. } => b.extend([*out_a, *out_b]),
        Wire::Run { out, input, .. } => b.extend([*out, *input]),
        Wire::Concat { out, parts } => {
            b.push(*out);
            b.extend(parts.iter().copied());
        }
        Wire::Slice { out, h, .. } | Wire::Pick { out, h, .. } => b.extend([*out, *h]),
        Wire::OpenBool { h, .. } | Wire::OpenBoolTo { h, .. } | Wire::FreeBool { h } => b.push(*h),
        Wire::FieldInput { outs_a, outs_b, .. } => f.extend(outs_a.iter().chain(outs_b).copied()),
        Wire::FieldPublic { out, .. } => f.push(*out),
        Wire::FieldAdd { out, a, b: c } | Wire::FieldSub { out, a, b: c } => f.extend([*out, *a, *c]),
        Wire::FieldScale { out, a, .. } | Wire::FieldDivide { out, a, .. } => f.extend([*out, *a]),
        Wire::FieldMul { outs, pairs } => {
            f.extend(outs.iter().copied());
            for p in pairs {
                f.extend([p.0, p.1]);
            }
        }
        Wire::FieldCheck | Wire::Exchange { .. } => {}
        Wire::OpenField { hs, .. } => f.extend(hs.iter().copied()),
        Wire::FreeField { h } => f.push(*h),
        Wire::Program { ins, masks, outs, .. } => f.extend(ins.iter().chain(masks).chain(outs).copied()),
    }
}

/// Opened bits from the engine (one byte each, 0 or 1), exactly `n` of them.
fn bits_of(bytes: &[u8], n: u64) -> Result<Vec<bool>, String> {
    if bytes.len() as u64 != n || bytes.iter().any(|&b| b > 1) {
        return Err("opened bits".into());
    }
    Ok(bytes.iter().map(|&b| b == 1).collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn felt(n: u64) -> Felt {
        let mut v = [0u8; 32];
        v[..8].copy_from_slice(&n.to_le_bytes());
        v
    }

    fn sample() -> Vec<Wire> {
        vec![
            Wire::BoolInput { out: 1, owner: Party::A, width: 2, once: false, revealable: true, bits: vec![true, false] },
            Wire::FieldPublic { out: 2, v: felt(9) },
            Wire::Exchange { len: 2, label: 1, payload: vec![7, 8] },
        ]
    }

    #[test]
    fn round_trip_and_skeleton() {
        let b = sample();
        let bytes = encode_batch(&b);
        assert_eq!(decode_batch(&bytes), Some(b.clone()));
        let skel = skeleton_bytes(&b);
        let blank: Vec<Wire> = b.iter().map(Wire::blank).collect();
        assert_eq!(skel, encode_batch(&blank));
        assert_eq!(decode_batch(&skel), Some(blank));
    }

    #[test]
    fn decode_failures() {
        let bytes = encode_batch(&sample());
        // truncated anywhere
        for cut in 0..bytes.len() {
            assert_eq!(decode_batch(&bytes[..cut]), None, "cut {cut}");
        }
        // trailing bytes
        assert_eq!(decode_batch(&[bytes.clone(), vec![0]].concat()), None);
        // element >= p, = p, and the largest canonical one
        let public = |v: Felt| encode_batch(&[Wire::FieldPublic { out: 1, v }]);
        let mut p = public(MODULUS);
        assert_eq!(decode_batch(&p), None);
        *p.last_mut().unwrap() = 0xff;
        assert_eq!(decode_batch(&p), None);
        let mut below = MODULUS;
        below[0] -= 1;
        assert!(decode_batch(&public(below)).is_some());
        // bit not 0/1
        let mut bits = encode_batch(&[Wire::BoolPublic { out: 1, bits: vec![true] }]);
        *bits.last_mut().unwrap() = 2;
        assert_eq!(decode_batch(&bits), None);
        // flag, party and kind bytes not 0/1
        let input = encode_batch(&[sample()[0].clone()]);
        for at in [17usize, 26, 27] {
            let mut x = input.clone();
            x[at] = 2;
            assert_eq!(decode_batch(&x), None, "byte {at}");
        }
        let mut kind = encode_batch(&[Wire::FieldInput { outs_a: vec![], outs_b: vec![], kind: FieldIn::Coins, revealable: false, elements: vec![] }]);
        kind[25] = 2;
        assert_eq!(decode_batch(&kind), None);
        // unknown opcodes
        for op in [0u8, 23, 93, 255] {
            assert_eq!(decode_batch(&[1, 0, 0, 0, 0, 0, 0, 0, op]), None, "opcode {op}");
        }
        assert_eq!(decode_batch(&[1, 0, 0, 0, 0, 0, 0, 0, 18]), Some(vec![Wire::FieldCheck]));
        // a count far beyond the input allocates nothing and fails
        let mut huge = u64::MAX.to_le_bytes().to_vec();
        huge.push(18);
        assert_eq!(decode_batch(&huge), None);
        let mut huge_bytes = vec![1, 0, 0, 0, 0, 0, 0, 0, 21];
        huge_bytes.extend_from_slice(&1u64.to_le_bytes());
        huge_bytes.extend_from_slice(&1u64.to_le_bytes());
        huge_bytes.extend_from_slice(&u64::MAX.to_le_bytes());
        assert_eq!(decode_batch(&huge_bytes), None);
        assert_eq!(decode_batch(&[]), None);
        assert_eq!(decode_batch(&0u64.to_le_bytes()), Some(vec![]));
    }

    #[test]
    fn unusable_is_not_a_batch() {
        assert_eq!(decode_batch(UNUSABLE), None);
        // Lean `unusable`, byte for byte.
        assert_eq!(UNUSABLE, [117, 110, 117, 115, 97, 98, 108, 101, 32, 98, 97, 116, 99, 104]);
        assert_eq!(agreed_bytes(&usable_batch(Party::A, UNUSABLE)), UNUSABLE);
        let ok = encode_batch(&[Wire::FieldCheck]);
        assert_eq!(agreed_bytes(&usable_batch(Party::A, &ok)), skeleton_bytes(&[Wire::FieldCheck]));
    }

    #[test]
    fn admit_enforces_d8() {
        let none = |_: &[u8]| None;
        let mut i = Interp::default();
        let open = Wire::BoolPublic { out: 1, bits: vec![true] };
        let batch = [open, Wire::OpenBool { h: 1, label: 3 }, Wire::FreeBool { h: 1 }];
        assert!(i.admit(&none, &batch).is_err());
        assert_eq!(i.ctx, Ctx::default(), "a refused batch leaves the context");
        assert!(i.admit(&none, &batch[..2]).is_ok());
    }

    #[test]
    fn refused_batch_rolls_back_drops_and_definitions() {
        let none = |_: &[u8]| None;
        let mut i = Interp::default();
        let def = [
            Wire::BoolInput { out: 1, owner: Party::A, width: 2, once: true, revealable: false, bits: vec![] },
            Wire::FieldPublic { out: 5, v: felt(3) },
        ];
        assert!(i.admit(&none, &def).is_ok());
        let before = i.ctx.clone();
        // Uses (consumes) 1, frees 5, defines 6 and 7, then names an unknown handle: refused.
        let bad = [
            Wire::Slice { out: 6, h: 1, lo: 0, hi: 1 },
            Wire::FreeField { h: 5 },
            Wire::FieldPublic { out: 7, v: felt(4) },
            Wire::FreeBool { h: 99 },
        ];
        assert!(i.admit(&none, &bad).is_err());
        assert_eq!(i.ctx, before, "every change of the refused batch is undone");
        assert!(i.ctx.journal.is_none());
        // The same handles can still be used, and 6, 7 were never seen.
        assert!(i.admit(&none, &bad[..3]).is_ok());
    }

    #[test]
    fn payload_validation() {
        let input = |owner, bits: Vec<bool>| Wire::BoolInput { out: 1, owner, width: 2, once: false, revealable: false, bits };
        assert!(validate_payloads(Party::A, &[input(Party::A, vec![true, false])]).is_ok());
        assert!(validate_payloads(Party::A, &[input(Party::A, vec![true])]).is_err());
        assert!(validate_payloads(Party::B, &[input(Party::A, vec![])]).is_ok());
        assert!(validate_payloads(Party::B, &[input(Party::A, vec![true, false])]).is_err());
        let both = |bits: Vec<bool>| Wire::BoolInputBoth { out_a: 1, out_b: 2, width: 1, once: false, revealable: false, bits };
        assert!(validate_payloads(Party::B, &[both(vec![true])]).is_ok());
        assert!(validate_payloads(Party::B, &[both(vec![])]).is_err());
        let field = |kind, elements: Vec<Felt>| Wire::FieldInput { outs_a: vec![1], outs_b: vec![2], kind, revealable: false, elements };
        assert!(validate_payloads(Party::A, &[field(FieldIn::Coins, vec![felt(u64::MAX)])]).is_ok());
        let mut big = felt(0);
        big[8] = 1;
        assert!(validate_payloads(Party::A, &[field(FieldIn::Coins, vec![big])]).is_err());
        assert!(validate_payloads(Party::A, &[field(FieldIn::Elements, vec![big])]).is_ok());
        assert!(validate_payloads(Party::A, &[field(FieldIn::Elements, vec![])]).is_err());
        let ex = |payload: Vec<u8>| Wire::Exchange { len: 3, label: 1, payload };
        assert!(validate_payloads(Party::A, &[ex(vec![1, 2, 3])]).is_ok());
        assert!(validate_payloads(Party::A, &[ex(vec![1, 2])]).is_err());
    }

    #[test]
    fn replies_round_trip() {
        let r = vec![Datum::Bits(vec![true, false]), Datum::Elems(vec![felt(3)]), Datum::Bytes(vec![1, 2])];
        assert_eq!(decode_replies(&encode_replies(&r)), Some(r));
        assert_eq!(decode_replies(&[0, 0, 0, 0, 0, 0, 0, 0, 1]), None);
    }
}
