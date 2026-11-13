//! The handle table and the open rule (REORGANIZATION_PLAN.md 5.4): a transcription of the Lean
//! judgement `check` (`TlsMpc/Node/Engine.lean`, section "Well-formedness"), line by line. Each
//! Rust check carries the Lean name it transcribes, so the two can be read side by side.
//!
//! `check` reads only the agreed skeleton of an instruction (the payload fields of
//! [`Wire`] are never looked at here). The shell runs it over a whole batch after the agreement
//! and before the first engine call ([`check_batch`], Lean `checkBatch`: `check` per instruction
//! and decision D8, a release must be its batch's last instruction); the context is carried
//! across batches from the empty one at session start.
//!
//! Representation (the same function, another data structure):
//! - Lean's association lists `bools`, `fields` hold at most one entry per id (`defBool` /
//!   `defField` refuse an id already in `seenB` / `seenF`, and every live id is in them), so
//!   `List.lookup` is a map lookup and `filter (·.1 != id)` is a map removal.
//! - Lean's `check` is pure; here it mutates a working context in place. On a refusal the
//!   working context is garbage and is discarded ([`check_batch`] works on a copy and returns the
//!   original unchanged), exactly as Lean's `none` discards everything computed before it.
//! - Lean's `defBool` refuses a handle wider than `maxWidth` ([`MAX_WIDTH`]). Where building the
//!   marks would allocate (`concat`), the same condition is tested before they are built; a
//!   refusal either way is the same `none`.
use crate::interp::{Party, Wire};
use std::collections::{BTreeMap, BTreeSet};

/// Lean `Mark`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mark {
    Never,
    Pub,
    ToA,
    ToB,
    Revealable,
}

impl Mark {
    /// Lean `Mark.ofInput`.
    pub fn of_input(revealable: bool) -> Mark {
        if revealable { Mark::Revealable } else { Mark::Never }
    }
    /// Lean `Mark.openable`.
    pub fn openable(self) -> bool {
        matches!(self, Mark::Pub | Mark::Revealable)
    }
    /// Lean `Mark.to`.
    pub fn to(p: Party) -> Mark {
        match p {
            Party::A => Mark::ToA,
            Party::B => Mark::ToB,
        }
    }
    /// Lean `Mark.join`.
    pub fn join(self, other: Mark) -> Mark {
        match (self, other) {
            (Mark::Pub, Mark::Pub) => Mark::Pub,
            (Mark::Pub, Mark::Revealable) => Mark::Revealable,
            (Mark::Revealable, Mark::Pub) => Mark::Revealable,
            (Mark::Revealable, Mark::Revealable) => Mark::Revealable,
            _ => Mark::Never,
        }
    }
    /// A circuit layout's output mark (`kernel.h:25`: 0 private, 1 public, 2 garbling party =
    /// party A, 3 evaluating party = party B), as Lean `Sig` documents it.
    pub fn of_layout(opened: u8) -> Option<Mark> {
        match opened {
            0 => Some(Mark::Never),
            1 => Some(Mark::Pub),
            2 => Some(Mark::ToA),
            3 => Some(Mark::ToB),
            _ => None,
        }
    }
    /// The digit the test vectors use (node_worker/tests/lean/EngineVectors.lean `markCode`).
    pub fn code(self) -> char {
        match self {
            Mark::Never => '0',
            Mark::Pub => '1',
            Mark::ToA => '2',
            Mark::ToB => '3',
            Mark::Revealable => '4',
        }
    }
}

/// Lean `BoolInfo`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoolInfo {
    pub marks: Vec<Mark>,
    pub once: bool,
}

/// Lean `Sig`: a circuit's input width of one copy and output marks of one copy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sig {
    pub in_width: u64,
    pub out_marks: Vec<Mark>,
}

/// Lean `ProgSig`: a V3 field program's data inputs, masks, and the marks of one instance's
/// outputs (program.rs `Program::sig`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProgSig {
    pub inputs: u64,
    pub masks: u64,
    pub out_marks: Vec<Mark>,
}

/// Lean `Shape`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    Unit,
    Bits(u64),
    Elems(u64),
    Bytes(u64),
}

/// Lean `maxExchange` (= link.rs MAX_EXCHANGE).
pub const MAX_EXCHANGE: u64 = 65536;

/// Lean `maxWidth`: the widest Boolean handle (bits), and the most copies of a run.
pub const MAX_WIDTH: u64 = 1 << 26;

/// Lean `Ctx`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Ctx {
    pub bools: BTreeMap<u64, BoolInfo>,
    pub fields: BTreeMap<u64, Mark>,
    /// Every Boolean handle id ever defined (ids are never reused).
    pub seen_b: BTreeSet<u64>,
    pub seen_f: BTreeSet<u64>,
    /// Lean `Ctx.progs`: the V3 programs the worker loaded, by name (fixed at session start,
    /// [`crate::shell::Shell::set_programs`]; not part of [`Ctx::canonical`]).
    pub progs: BTreeMap<Vec<u8>, ProgSig>,
}

/// Lean `guard`.
fn guard(ok: bool) -> Option<()> {
    if ok { Some(()) } else { None }
}

impl Ctx {
    /// Lean `Ctx.bool?`.
    pub fn bool(&self, h: u64) -> Option<&BoolInfo> {
        self.bools.get(&h)
    }
    /// Lean `Ctx.field?`.
    pub fn field(&self, h: u64) -> Option<Mark> {
        self.fields.get(&h).copied()
    }
    /// Lean `Ctx.defBool`: `if h.id ∈ c.seenB ∨ maxWidth < i.marks.length then none`.
    fn def_bool(&mut self, h: u64, i: BoolInfo) -> Option<()> {
        if self.seen_b.contains(&h) || MAX_WIDTH < i.marks.len() as u64 {
            return None;
        }
        self.bools.insert(h, i);
        self.seen_b.insert(h);
        Some(())
    }
    /// Lean `Ctx.defField`.
    fn def_field(&mut self, h: u64, m: Mark) -> Option<()> {
        if self.seen_f.contains(&h) {
            return None;
        }
        self.fields.insert(h, m);
        self.seen_f.insert(h);
        Some(())
    }
    /// Lean `Ctx.dropBool`.
    fn drop_bool(&mut self, h: u64) {
        self.bools.remove(&h);
    }
    /// Lean `Ctx.dropField`.
    fn drop_field(&mut self, h: u64) {
        self.fields.remove(&h);
    }
    /// Lean `Ctx.useBool`: read a Boolean operand; a `once` handle is consumed.
    fn use_bool(&mut self, h: u64) -> Option<BoolInfo> {
        let i = self.bool(h)?.clone();
        if i.once {
            self.drop_bool(h);
        }
        Some(i)
    }
    /// Lean `Ctx.useBools`.
    fn use_bools(&mut self, hs: &[u64]) -> Option<Vec<BoolInfo>> {
        let mut is = Vec::with_capacity(hs.len());
        for &h in hs {
            is.push(self.use_bool(h)?);
        }
        Some(is)
    }
    /// Lean `Ctx.defFields`.
    fn def_fields(&mut self, hs: &[u64], ms: &[Mark]) -> Option<()> {
        guard(hs.len() == ms.len())?;
        for (&h, &m) in hs.iter().zip(ms) {
            self.def_field(h, m)?;
        }
        Some(())
    }
    /// Lean `Ctx.useMasks`: each mask, in order, live with mark `never`, then dropped.
    fn use_masks(&mut self, hs: &[u64]) -> Option<()> {
        for &h in hs {
            guard(self.field(h) == Some(Mark::Never))?;
            self.drop_field(h);
        }
        Some(())
    }

    /// The canonical text of a context (node_worker/tests/lean/EngineVectors.lean `showCtx`).
    pub fn canonical(&self) -> String {
        let join = |v: Vec<String>, sep: &str| v.join(sep);
        let bools = join(
            self.bools
                .iter()
                .map(|(id, i)| format!("{id}:{}:{}", i.marks.iter().map(|m| m.code()).collect::<String>(), i.once as u8))
                .collect(),
            ";",
        );
        let fields = join(self.fields.iter().map(|(id, m)| format!("{id}:{}", m.code())).collect(), ";");
        let sb = join(self.seen_b.iter().map(|x| x.to_string()).collect(), ",");
        let sf = join(self.seen_f.iter().map(|x| x.to_string()).collect(), ",");
        format!("B[{bools}]F[{fields}]SB[{sb}]SF[{sf}]")
    }
}

/// Lean `check`, for one agreed instruction, mutating `c` in place (see the module note: on
/// `None` the caller discards `c`). `sigs` is Lean's `sigs : Bytes → Option Sig`.
pub fn check(sigs: &dyn Fn(&[u8]) -> Option<Sig>, c: &mut Ctx, s: &Wire) -> Option<Shape> {
    match s {
        // | .boolInput out _ w once rev _
        Wire::BoolInput { out, width, once, revealable, .. } => {
            guard(*width <= MAX_WIDTH)?; // guard (w ≤ maxWidth), before the marks are built
            c.def_bool(*out, BoolInfo { marks: vec![Mark::of_input(*revealable); *width as usize], once: *once })?;
            Some(Shape::Unit)
        }
        // | .boolInputBoth outA outB w once rev _
        Wire::BoolInputBoth { out_a, out_b, width, once, revealable, .. } => {
            guard(*width <= MAX_WIDTH)?; // guard (w ≤ maxWidth)
            c.def_bool(*out_a, BoolInfo { marks: vec![Mark::of_input(*revealable); *width as usize], once: *once })?;
            c.def_bool(*out_b, BoolInfo { marks: vec![Mark::of_input(*revealable); *width as usize], once: *once })?;
            Some(Shape::Unit)
        }
        // | .boolPublic out bits
        Wire::BoolPublic { out, bits } => {
            c.def_bool(*out, BoolInfo { marks: vec![Mark::Pub; bits.len()], once: false })?;
            Some(Shape::Unit)
        }
        // | .run out name copies input
        Wire::Run { out, circuit, copies, input } => {
            let s = sigs(circuit)?; // let s ← sigs name
            guard(0 < *copies && *copies <= MAX_WIDTH)?; // guard (0 < copies ∧ copies ≤ maxWidth)
            let i = c.use_bool(*input)?; // let (i, c) ← c.useBool input
            // guard (i.marks.length = copies * s.inWidth); an overflowing product exceeds any width
            guard(copies.checked_mul(s.in_width) == Some(i.marks.len() as u64))?;
            // guard (copies * s.outMarks.length ≤ maxWidth), before the marks are built
            guard(copies.checked_mul(s.out_marks.len() as u64).is_some_and(|w| w <= MAX_WIDTH))?;
            let marks: Vec<Mark> = (0..*copies).flat_map(|_| s.out_marks.iter().copied()).collect();
            c.def_bool(*out, BoolInfo { marks, once: false })?; // (List.replicate copies s.outMarks).flatten
            Some(Shape::Unit)
        }
        // | .concat out parts
        Wire::Concat { out, parts } => {
            let is = c.use_bools(parts)?; // let (is, c) ← c.useBools parts
            // defBool's width condition, tested before the concatenation is built
            guard(is.iter().map(|i| i.marks.len() as u64).sum::<u64>() <= MAX_WIDTH)?;
            let marks: Vec<Mark> = is.iter().flat_map(|i| i.marks.iter().copied()).collect();
            c.def_bool(*out, BoolInfo { marks, once: is.iter().any(|i| i.once) })?;
            Some(Shape::Unit)
        }
        // | .slice out h lo hi
        Wire::Slice { out, h, lo, hi } => {
            let i = c.use_bool(*h)?; // let (i, c) ← c.useBool h
            guard(lo <= hi && *hi <= i.marks.len() as u64)?; // guard (lo ≤ hi ∧ hi ≤ i.marks.length)
            // (i.marks.drop lo).take (hi - lo)
            c.def_bool(*out, BoolInfo { marks: i.marks[*lo as usize..*hi as usize].to_vec(), once: i.once })?;
            Some(Shape::Unit)
        }
        // | .pick out h idx
        Wire::Pick { out, h, indices } => {
            let i = c.use_bool(*h)?; // let (i, c) ← c.useBool h
            guard(indices.iter().all(|&j| j < i.marks.len() as u64))?; // guard (idx.all (· < i.marks.length))
            // idx.map (fun j => i.marks.getD j .never)
            let marks = indices.iter().map(|&j| i.marks.get(j as usize).copied().unwrap_or(Mark::Never)).collect();
            c.def_bool(*out, BoolInfo { marks, once: i.once })?;
            Some(Shape::Unit)
        }
        // | .openBool h l
        Wire::OpenBool { h, label } => {
            guard(*label != 0)?; // guard (l.code ≠ 0)
            let i = c.use_bool(*h)?; // let (i, c) ← c.useBool h
            guard(i.marks.iter().all(|m| m.openable()))?; // guard (i.marks.all Mark.openable)
            Some(Shape::Bits(i.marks.len() as u64))
        }
        // | .openBoolTo h r l _
        Wire::OpenBoolTo { h, recipient, label } => {
            guard(*label != 0)?; // guard (l.code ≠ 0)
            let i = c.use_bool(*h)?; // let (i, c) ← c.useBool h
            guard(i.marks.iter().all(|&m| m == Mark::to(*recipient)))?; // guard (i.marks.all (· == Mark.to r))
            Some(Shape::Unit)
        }
        // | .freeBool h
        Wire::FreeBool { h } => {
            c.bool(*h)?; // let _ ← c.bool? h
            c.drop_bool(*h);
            Some(Shape::Unit)
        }
        // | .fieldInput outsA outsB _ rev _
        Wire::FieldInput { outs_a, outs_b, revealable, .. } => {
            guard(outs_a.len() == outs_b.len())?; // guard (outsA.length = outsB.length)
            let all: Vec<u64> = outs_a.iter().chain(outs_b).copied().collect();
            let marks = vec![Mark::of_input(*revealable); all.len()];
            c.def_fields(&all, &marks)?; // c.defFields (outsA ++ outsB) (List.replicate ... (Mark.ofInput rev))
            Some(Shape::Unit)
        }
        // | .fieldPublic out _
        Wire::FieldPublic { out, .. } => {
            c.def_field(*out, Mark::Pub)?;
            Some(Shape::Unit)
        }
        // | .fieldAdd out a b  and  | .fieldSub out a b
        Wire::FieldAdd { out, a, b } | Wire::FieldSub { out, a, b } => {
            let ma = c.field(*a)?; // let ma ← c.field? a
            let mb = c.field(*b)?; // let mb ← c.field? b
            c.def_field(*out, ma.join(mb))?;
            Some(Shape::Unit)
        }
        // | .fieldScale out a k
        Wire::FieldScale { out, a, .. } => {
            let m = c.field(*a)?; // let m ← c.field? a
            c.def_field(*out, m.join(Mark::Pub))?;
            Some(Shape::Unit)
        }
        // | .fieldDivide out a k
        Wire::FieldDivide { out, a, c: k } => {
            guard(*k != [0u8; 32])?; // guard (k ≠ 0): elements are canonical, so zero is all-zero bytes
            let m = c.field(*a)?; // let m ← c.field? a
            c.def_field(*out, m.join(Mark::Pub))?;
            Some(Shape::Unit)
        }
        // | .fieldMul outs pairs
        Wire::FieldMul { outs, pairs } => {
            guard(outs.len() == pairs.len())?; // guard (outs.length = pairs.length)
            // let ms ← pairs.mapM (fun p => do let x ← c.field? p.1; let y ← c.field? p.2; pure (x.join y))
            let mut ms = Vec::with_capacity(pairs.len());
            for &(x, y) in pairs {
                let x = c.field(x)?;
                let y = c.field(y)?;
                ms.push(x.join(y));
            }
            c.def_fields(outs, &ms)?; // let c ← c.defFields outs ms
            Some(Shape::Unit)
        }
        // | .fieldCheck
        Wire::FieldCheck => Some(Shape::Unit),
        // | .openField hs l
        Wire::OpenField { hs, label } => {
            guard(*label != 0)?; // guard (l.code ≠ 0)
            let mut ms = Vec::with_capacity(hs.len()); // let ms ← hs.mapM c.field?
            for &h in hs {
                ms.push(c.field(h)?);
            }
            guard(ms.iter().all(|m| m.openable()))?; // guard (ms.all Mark.openable)
            Some(Shape::Elems(hs.len() as u64))
        }
        // | .freeField h
        Wire::FreeField { h } => {
            c.field(*h)?; // let _ ← c.field? h
            c.drop_field(*h);
            Some(Shape::Unit)
        }
        // | .exchange len l _
        Wire::Exchange { len, label, .. } => {
            guard(*label != 0 && 0 < *len && *len <= MAX_EXCHANGE)?; // guard (l.code ≠ 0 ∧ 0 < len ∧ len ≤ maxExchange)
            Some(Shape::Bytes(*len))
        }
        // | .program name copies ins masks outs l
        Wire::Program { name, copies, ins, masks, outs, label } => {
            guard(*label != 0)?; // guard (l.code ≠ 0)
            let s = c.progs.get(name)?.clone(); // let s ← c.progs name
            guard(0 < *copies && *copies <= MAX_WIDTH)?; // guard (0 < copies ∧ copies ≤ maxWidth)
            // guard (ins.length = copies * s.inputs ∧ masks.length = copies * s.masks ∧
            //   outs.length = copies * s.outMarks.length); an overflowing product fits no list
            guard(
                copies.checked_mul(s.inputs) == Some(ins.len() as u64)
                    && copies.checked_mul(s.masks) == Some(masks.len() as u64)
                    && copies.checked_mul(s.out_marks.len() as u64) == Some(outs.len() as u64),
            )?;
            c.use_masks(masks)?; // let c ← c.useMasks masks
            guard(ins.iter().all(|&h| c.field(h).is_some()))?; // guard (ins.all fun h => (c.field? h).isSome)
            // let c ← c.defFields outs (List.replicate copies s.outMarks).flatten (as long as outs)
            let marks: Vec<Mark> = (0..*copies).flat_map(|_| s.out_marks.iter().copied()).collect();
            c.def_fields(outs, &marks)?;
            Some(Shape::Unit)
        }
    }
}

/// Lean `checkBatch` (`checkBatchFrom` from index 0): `check` on every instruction in order from
/// `c`, and decision D8: an instruction that ends a batch ([`Wire::ends_batch`]) must be the last.
/// The context after the batch and every instruction's shape, or the index of the first refused
/// instruction (then `c` is unchanged).
pub fn check_batch(sigs: &dyn Fn(&[u8]) -> Option<Sig>, c: &Ctx, batch: &[Wire]) -> Result<(Ctx, Vec<Shape>), usize> {
    let mut work = c.clone();
    let mut shapes = Vec::with_capacity(batch.len());
    for (index, w) in batch.iter().enumerate() {
        match check(sigs, &mut work, w) {
            // if s.endsBatch && !ss.isEmpty then .error i
            Some(_) if w.ends_batch() && index + 1 < batch.len() => return Err(index),
            Some(shape) => shapes.push(shape),
            None => return Err(index),
        }
    }
    Ok((work, shapes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn join_table() {
        use Mark::*;
        let all = [Never, Pub, ToA, ToB, Revealable];
        for a in all {
            for b in all {
                let want = match (a, b) {
                    (Pub, Pub) => Pub,
                    (Pub | Revealable, Pub | Revealable) => Revealable,
                    _ => Never,
                };
                assert_eq!(a.join(b), want, "{a:?} {b:?}");
            }
        }
    }

    #[test]
    fn resource_bounds_refuse_before_allocating() {
        let none = |_: &[u8]| None;
        let mut c = Ctx::default();
        let wide = Wire::BoolInput { out: 1, owner: Party::B, width: u64::MAX, once: false, revealable: false, bits: vec![] };
        assert_eq!(check(&none, &mut c, &wide), None);
        let ok = Wire::BoolInput { out: 1, owner: Party::B, width: MAX_WIDTH, once: false, revealable: false, bits: vec![] };
        let mut c = Ctx::default();
        assert_eq!(check(&none, &mut c, &ok), Some(Shape::Unit));
        // Doubling by concatenation stops at the bound.
        let twice = Wire::Concat { out: 2, parts: vec![1, 1] };
        assert_eq!(check(&none, &mut c, &twice), None);
        // A circuit without inputs cannot be replicated past the bound, nor past u32 copies.
        let noin = |n: &[u8]| (n == b"noin").then(|| Sig { in_width: 0, out_marks: vec![Mark::Pub] });
        let mut c = Ctx::default();
        assert_eq!(check(&noin, &mut c, &Wire::Concat { out: 1, parts: vec![] }), Some(Shape::Unit));
        let many = Wire::Run { out: 2, circuit: b"noin".to_vec(), copies: MAX_WIDTH + 1, input: 1 };
        assert_eq!(check(&noin, &mut c.clone(), &many), None);
        let fits = Wire::Run { out: 2, circuit: b"noin".to_vec(), copies: MAX_WIDTH, input: 1 };
        assert_eq!(check(&noin, &mut c, &fits), Some(Shape::Unit));
        // A circuit without inputs or outputs: copies alone are bounded (Lean's copies ≤ maxWidth).
        let nothing = |n: &[u8]| (n == b"nothing").then(|| Sig { in_width: 0, out_marks: vec![] });
        let mut c = Ctx::default();
        assert_eq!(check(&nothing, &mut c, &Wire::Concat { out: 1, parts: vec![] }), Some(Shape::Unit));
        let at = Wire::Run { out: 2, circuit: b"nothing".to_vec(), copies: MAX_WIDTH, input: 1 };
        assert_eq!(check(&nothing, &mut c.clone(), &at), Some(Shape::Unit));
        let over = Wire::Run { out: 2, circuit: b"nothing".to_vec(), copies: MAX_WIDTH + 1, input: 1 };
        assert_eq!(check(&nothing, &mut c, &over), None);
    }

    #[test]
    fn releases_end_batches() {
        let none = |_: &[u8]| None;
        let input = Wire::BoolPublic { out: 1, bits: vec![true] };
        let open = Wire::OpenBool { h: 1, label: 3 };
        let ok = check_batch(&none, &Ctx::default(), &[input.clone(), open.clone()]);
        assert!(ok.is_ok());
        assert_eq!(check_batch(&none, &Ctx::default(), &[input.clone(), open.clone(), open.clone()]), Err(1));
        let free = Wire::FreeBool { h: 1 };
        assert_eq!(check_batch(&none, &Ctx::default(), &[input, open, free]), Err(1));
    }
}
