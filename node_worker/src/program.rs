//! V3 field programs (REORGANIZATION_PLAN.md 5.5, stage S9): the parser and the evaluator of the
//! engine instruction `program` (opcode 22, `TlsMpc/Node/Engine.lean`). The format and its
//! semantics are `TlsMpc/FieldDagV3.lean`; Lean names are given next to each part here.
//!
//! This replaces the C++ `field_program.h` for the script flows only. The legacy library keeps
//! the C++ evaluator, which reads the V2 files kept beside the V3 ones, until S11.
//!
//! [`parse`] accepts exactly the texts Lean's `FieldDagV3.parse` accepts (the canonical text of a
//! valid program, `parse_render` / `render_parse` / `parse_valid`), with one limit of its own:
//! every number but a constant must fit in a u64 (and the file is at most [`MAX_FILE`] bytes).
//!
//! [`evaluate`] runs `copies` instances together, so their products share rounds, level by
//! level as `field_program.h` does: a round of `ea_field_mul` (secret products, and `a·m`, `b·m`
//! of every `D`/`Z` row of the level), one `ea_field_checked_open` of the level's `b·m` (all
//! instances), then `ea_field_divide_public` (or the constant 0 for a `Z` row whose opening is 0;
//! a `D` row whose opening is 0 aborts), then the level's linear rows in row order. It opens
//! exactly one value per `D`/`Z` row per instance and nothing else (Lean `eval_lengths`), and
//! returns the openings in Lean's order (`runProgram`: instance by instance, rows in order).
//!
//! Engine values: inputs and masks belong to the caller (the masks are consumed by `check`, and
//! the interpreter frees them at the end of the batch); every value the evaluator makes is freed
//! before it returns except the outputs, and every output is a value of its own (an output that
//! names an input row, or a row another output already names, is copied with `scale(·, 1)`).
use crate::engines::Engines;
use crate::handles::{Mark, ProgSig};
use crate::interp::{Felt, canonical};
#[cfg(test)]
use crate::interp::MODULUS;

/// The largest V3 file (`field_program.h` reads at most 4,000,000 bytes of a V2 file).
pub const MAX_FILE: usize = 4_000_000;

/// Lean `magic`.
pub const MAGIC: &[u8] = b"EMP_HYBRID_FIELD_DAG_V3";

/// p = 2^255 - 19 in decimal (Lean `decimal modulus`).
pub const MODULUS_DECIMAL: &[u8] = b"57896044618658097711785492504343953926634992332820282019728792003956564819949";

/// Lean `OMark`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OMark {
    Never,
    Pub,
}

impl OMark {
    /// Lean `Mark.ofOMark`.
    pub fn mark(self) -> Mark {
        match self {
            OMark::Never => Mark::Never,
            OMark::Pub => Mark::Pub,
        }
    }
}

/// Lean `Row`. Operands are row indices; `Input` a data input; `m` a mask.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Row {
    Input(usize),
    /// The element, and its value when it is below 2^64 (a product with such a row is a scaling).
    Const(Felt, Option<u64>),
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Div(usize, usize, usize),
    Zdiv(usize, usize, usize),
    Flag(usize),
}

/// Lean `Program`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub inputs: usize,
    pub masks: usize,
    pub rows: Vec<Row>,
    pub outputs: Vec<(usize, OMark)>,
}

impl Program {
    /// Lean `ProgSig.ofProgram`: what `check` knows of the program.
    pub fn sig(&self) -> ProgSig {
        ProgSig { inputs: self.inputs as u64, masks: self.masks as u64, out_marks: self.outputs.iter().map(|o| o.1.mark()).collect() }
    }
    /// Lean `Program.openings`: the `D`/`Z` rows.
    pub fn openings(&self) -> usize {
        self.rows.iter().filter(|r| matches!(r, Row::Div(..) | Row::Zdiv(..))).count()
    }
}

// ---- parsing (Lean `P`, `rowP`, `outP`, `programP`, `parseChars`, `Program.valid`)

struct Cursor<'a> {
    s: &'a [u8],
}

impl<'a> Cursor<'a> {
    /// Lean `expect`.
    fn expect(&mut self, lit: &[u8]) -> Option<()> {
        let rest = self.s.strip_prefix(lit)?;
        self.s = rest;
        Some(())
    }
    /// Lean `anyChar`.
    fn any(&mut self) -> Option<u8> {
        let (&c, rest) = self.s.split_first()?;
        self.s = rest;
        Some(c)
    }
    /// Lean `nat`: the longest run of digits, canonical (no leading zero), as its digits.
    fn digits(&mut self) -> Option<&'a [u8]> {
        let n = self.s.iter().take_while(|c| c.is_ascii_digit()).count();
        if n == 0 || (n > 1 && self.s[0] == b'0') {
            return None;
        }
        let (d, rest) = self.s.split_at(n);
        self.s = rest;
        Some(d)
    }
    /// Lean `nat`, limited to a u64.
    fn num(&mut self) -> Option<usize> {
        let d = self.digits()?;
        let mut v: u64 = 0;
        for &c in d {
            v = v.checked_mul(10)?.checked_add((c - b'0') as u64)?;
        }
        usize::try_from(v).ok()
    }
}

/// A canonical decimal (no leading zero) below p, as an element.
fn decimal_felt(d: &[u8]) -> Option<Felt> {
    if d.len() > MODULUS_DECIMAL.len() {
        return None;
    }
    // value = Σ digit · 10^k, computed in four 64-bit limbs (the value is below 10^77 < 2^256).
    let mut limbs = [0u64; 4];
    for &c in d {
        let mut carry = (c - b'0') as u128;
        for limb in limbs.iter_mut() {
            let x = (*limb as u128) * 10 + carry;
            *limb = x as u64;
            carry = x >> 64;
        }
        if carry != 0 {
            return None;
        }
    }
    let mut v = [0u8; 32];
    for (i, limb) in limbs.iter().enumerate() {
        v[8 * i..8 * i + 8].copy_from_slice(&limb.to_le_bytes());
    }
    canonical(&v).then_some(v)
}

fn small(v: &Felt) -> Option<u64> {
    v[8..].iter().all(|&b| b == 0).then(|| u64::from_le_bytes(v[..8].try_into().unwrap()))
}

/// Lean `rowP`, then `Row.valid` at `index` (masks and the `F` target are checked by the caller).
fn row(r: &mut Cursor, index: usize, inputs: usize) -> Option<Row> {
    let c = r.any()?;
    r.expect(b" ")?;
    let two = |r: &mut Cursor| -> Option<(usize, usize)> {
        let a = r.num()?;
        r.expect(b" ")?;
        let b = r.num()?;
        (a < index && b < index).then_some((a, b))
    };
    let row = match c {
        b'I' => {
            let i = r.num()?;
            (i < inputs).then_some(Row::Input(i))?
        }
        b'C' => {
            let v = decimal_felt(r.digits()?)?;
            Row::Const(v, small(&v))
        }
        b'A' => {
            let (a, b) = two(r)?;
            Row::Add(a, b)
        }
        b'S' => {
            let (a, b) = two(r)?;
            Row::Sub(a, b)
        }
        b'M' => {
            let (a, b) = two(r)?;
            Row::Mul(a, b)
        }
        b'D' | b'Z' => {
            let (a, b) = two(r)?;
            r.expect(b" ")?;
            let m = r.num()?;
            if c == b'D' { Row::Div(a, b, m) } else { Row::Zdiv(a, b, m) }
        }
        b'F' => {
            let k = r.num()?;
            (k < index).then_some(Row::Flag(k))?
        }
        _ => return None,
    };
    r.expect(b"\n")?;
    Some(row)
}

/// Lean `parse`: the program of a V3 text, or why not.
pub fn parse(text: &[u8]) -> Result<Program, String> {
    if text.len() > MAX_FILE {
        return Err("field program size".into());
    }
    let mut r = Cursor { s: text };
    let bad = |what: &str| format!("field program V3: {what}");
    r.expect(MAGIC).and_then(|_| r.expect(b"\n")).ok_or_else(|| bad("format"))?;
    let header = (|| {
        let inputs = r.num()?;
        r.expect(b" ")?;
        let masks = r.num()?;
        r.expect(b" ")?;
        let rows = r.num()?;
        r.expect(b" ")?;
        let outputs = r.num()?;
        r.expect(b"\n")?;
        r.expect(MODULUS_DECIMAL)?;
        r.expect(b"\n")?;
        Some((inputs, masks, rows, outputs))
    })();
    let (inputs, masks, count, outputs) = header.ok_or_else(|| bad("header"))?;
    // Every row and output line has at least 4 bytes: the counts cannot exceed the text.
    if count > text.len() / 4 || outputs > text.len() / 4 {
        return Err(bad("counts"));
    }
    let mut rows = Vec::with_capacity(count);
    let mut uses = 0usize;
    for index in 0..count {
        let row = row(&mut r, index, inputs).ok_or_else(|| bad(&format!("row {index}")))?;
        match row {
            // Lean `masksOk`: the D/Z rows name 0, 1, …, masks − 1 in order.
            Row::Div(_, _, m) | Row::Zdiv(_, _, m) => {
                if m != uses {
                    return Err(bad(&format!("row {index}: mask {m}, expected {uses}")));
                }
                uses += 1;
            }
            Row::Flag(k) if !matches!(rows[k], Row::Zdiv(..)) => return Err(bad(&format!("row {index}: flag of a row that is not Z"))),
            _ => {}
        }
        rows.push(row);
    }
    if uses != masks {
        return Err(bad("masks"));
    }
    let mut outs = Vec::with_capacity(outputs);
    for j in 0..outputs {
        let out = (|| {
            r.expect(b"O ")?;
            let o = r.num()?;
            r.expect(b" ")?;
            let m = match r.any()? {
                b'0' => OMark::Never,
                b'1' => OMark::Pub,
                _ => return None,
            };
            r.expect(b"\n")?;
            (o < count).then_some((o, m))
        })();
        outs.push(out.ok_or_else(|| bad(&format!("output {j}")))?);
    }
    if !r.s.is_empty() {
        return Err(bad("trailing data"));
    }
    Ok(Program { inputs, masks, rows, outputs: outs })
}

// ---- evaluation (Lean `FieldDagV3.eval`, per instance; `Model.runProgram`, over instances)

/// How a row is computed.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// Inputs, constants, sums, differences, products with a small constant, flags.
    Linear,
    /// A product of two values, one triple.
    Product,
    /// `D` / `Z`: two products (`a·m`, `b·m`), one opening, one division.
    Division,
}

fn kind(rows: &[Row], r: &Row) -> Kind {
    let small_const = |i: usize| matches!(rows[i], Row::Const(_, Some(_)));
    match r {
        Row::Mul(a, b) if !small_const(*a) && !small_const(*b) => Kind::Product,
        Row::Div(..) | Row::Zdiv(..) => Kind::Division,
        _ => Kind::Linear,
    }
}

/// Runs `copies` instances of `p`: instance `k` reads `ins[k·inputs ..]` and `masks[k·masks ..]`.
/// Returns every instance's outputs (instance by instance) and every instance's openings
/// (instance by instance, rows in order), or an error (a `D` row's opening was 0, or an engine
/// call failed).
pub fn evaluate<E: Engines>(engines: &mut E, p: &Program, copies: usize, ins: &[u64], masks: &[u64]) -> Result<(Vec<u64>, Vec<Felt>), String> {
    if ins.len() != copies * p.inputs || masks.len() != copies * p.masks {
        return Err("field program arity".into());
    }
    let n = p.rows.len();
    // Levels: a product or a division is one level above its operands (a mask is at level 0);
    // a flag is at its Z row's level.
    let mut level = vec![0usize; n];
    let mut kinds = Vec::with_capacity(n);
    let mut mask_of = vec![0usize; n];
    for (i, r) in p.rows.iter().enumerate() {
        let k = kind(&p.rows, r);
        kinds.push(k);
        level[i] = match *r {
            Row::Input(_) | Row::Const(..) => 0,
            Row::Add(a, b) | Row::Sub(a, b) => level[a].max(level[b]),
            Row::Mul(a, b) => level[a].max(level[b]) + (k == Kind::Product) as usize,
            Row::Div(a, b, m) | Row::Zdiv(a, b, m) => {
                mask_of[i] = m;
                level[a].max(level[b]) + 1
            }
            Row::Flag(z) => level[z],
        };
    }
    let top = level.iter().copied().max().unwrap_or(0);
    let mut by_level: Vec<Vec<usize>> = vec![Vec::new(); top + 1];
    for i in 0..n {
        by_level[level[i]].push(i);
    }
    // values[k][i]: the engine handle of row i of instance k; owned: made here (not an input).
    let mut values = vec![vec![0u64; n]; copies];
    let mut owned = vec![vec![false; n]; copies];
    // The opening of each D/Z row of each instance, and whether it was zero (for F rows).
    let mut opened: Vec<Vec<Option<Felt>>> = vec![vec![None; n]; copies];
    let result = run_levels(engines, p, copies, ins, masks, &by_level, &kinds, &mask_of, &mut values, &mut owned, &mut opened);
    // Outputs: a value of its own each.
    let mut outs = Vec::with_capacity(copies * p.outputs.len());
    let mut failed = result.err();
    if failed.is_none() {
        for k in 0..copies {
            let mut taken = vec![false; n];
            for &(o, _) in &p.outputs {
                if owned[k][o] && !taken[o] {
                    taken[o] = true;
                    outs.push(values[k][o]);
                } else {
                    match engines.field_scale(values[k][o], 1) {
                        Ok(h) => outs.push(h),
                        Err(e) => {
                            failed = Some(e);
                            break;
                        }
                    }
                }
            }
            for (i, &t) in taken.iter().enumerate() {
                if t {
                    owned[k][i] = false;
                }
            }
        }
    }
    // Free every value made here that is not an output (also after a failure).
    for k in 0..copies {
        for i in 0..n {
            if owned[k][i] {
                let _ = engines.field_free(values[k][i]);
            }
        }
    }
    if let Some(e) = failed {
        for h in outs {
            let _ = engines.field_free(h);
        }
        return Err(e);
    }
    let openings = opened.iter().flat_map(|row| row.iter().flatten().copied()).collect::<Vec<_>>();
    // Lean `eval_lengths`: one opening per D/Z row per instance.
    debug_assert_eq!(openings.len(), copies * p.openings());
    Ok((outs, openings))
}

#[allow(clippy::too_many_arguments)]
fn run_levels<E: Engines>(
    engines: &mut E,
    p: &Program,
    copies: usize,
    ins: &[u64],
    masks: &[u64],
    by_level: &[Vec<usize>],
    kinds: &[Kind],
    mask_of: &[usize],
    values: &mut [Vec<u64>],
    owned: &mut [Vec<bool>],
    opened: &mut [Vec<Option<Felt>>],
) -> Result<(), String> {
    for rows in by_level {
        // The round: secret products, then a·m and b·m of every division, all instances.
        let products: Vec<usize> = rows.iter().copied().filter(|&i| kinds[i] == Kind::Product).collect();
        let divisions: Vec<usize> = rows.iter().copied().filter(|&i| kinds[i] == Kind::Division).collect();
        if !products.is_empty() || !divisions.is_empty() {
            let (mut a, mut b) = (Vec::new(), Vec::new());
            for k in 0..copies {
                for &i in &products {
                    let Row::Mul(x, y) = p.rows[i] else { unreachable!() };
                    a.push(values[k][x]);
                    b.push(values[k][y]);
                }
                for &i in &divisions {
                    let (Row::Div(x, y, _) | Row::Zdiv(x, y, _)) = p.rows[i] else { unreachable!() };
                    let m = masks[k * p.masks + mask_of[i]];
                    a.push(values[k][x]);
                    b.push(m);
                    a.push(values[k][y]);
                    b.push(m);
                }
            }
            let out = engines.field_mul(&a, &b)?;
            if out.len() != a.len() {
                return Err("field product count".into());
            }
            let mut q = 0;
            // (instance, row, a·m, b·m) of every division, to open the b·m together.
            let mut pending = Vec::new();
            for k in 0..copies {
                for &i in &products {
                    values[k][i] = out[q];
                    owned[k][i] = true;
                    q += 1;
                }
                for &i in &divisions {
                    pending.push((k, i, out[q], out[q + 1]));
                    q += 2;
                }
            }
            if !pending.is_empty() {
                let denominators: Vec<u64> = pending.iter().map(|d| d.3).collect();
                let values_opened = engines.field_checked_open(&denominators);
                for d in &pending {
                    let _ = engines.field_free(d.3);
                }
                let values_opened = match values_opened {
                    Ok(v) if v.len() == pending.len() && v.iter().all(canonical) => v,
                    Ok(_) => {
                        for d in &pending {
                            let _ = engines.field_free(d.2);
                        }
                        return Err("opened field elements".into());
                    }
                    Err(e) => {
                        for d in &pending {
                            let _ = engines.field_free(d.2);
                        }
                        return Err(e);
                    }
                };
                let mut error = None;
                for (d, o) in pending.iter().zip(values_opened) {
                    let (k, i, am, _) = *d;
                    opened[k][i] = Some(o);
                    if error.is_some() {
                        let _ = engines.field_free(am);
                        continue;
                    }
                    let zero = o == [0u8; 32];
                    let v = if !zero {
                        engines.field_divide_public(am, &o)
                    } else if matches!(p.rows[i], Row::Zdiv(..)) {
                        engines.field_constant(0)
                    } else {
                        Err("field program division by zero".to_string())
                    };
                    let _ = engines.field_free(am);
                    match v {
                        Ok(h) => {
                            values[k][i] = h;
                            owned[k][i] = true;
                        }
                        Err(e) => error = Some(e),
                    }
                }
                if let Some(e) = error {
                    return Err(e);
                }
            }
        }
        // The level's linear rows, in row order.
        for k in 0..copies {
            for &i in rows {
                if kinds[i] != Kind::Linear {
                    continue;
                }
                let v = &values[k];
                let h = match p.rows[i] {
                    Row::Input(j) => {
                        values[k][i] = ins[k * p.inputs + j];
                        continue;
                    }
                    Row::Const(_, Some(small)) => engines.field_constant(small)?,
                    Row::Const(c, None) => engines.field_public(&c)?,
                    Row::Add(a, b) => engines.field_add(v[a], v[b])?,
                    Row::Sub(a, b) => engines.field_sub(v[a], v[b])?,
                    // A product with a small constant row (the left one if both are).
                    Row::Mul(a, b) => match (&p.rows[a], &p.rows[b]) {
                        (Row::Const(_, Some(c)), _) => engines.field_scale(v[b], *c)?,
                        (_, Row::Const(_, Some(c))) => engines.field_scale(v[a], *c)?,
                        _ => unreachable!(),
                    },
                    Row::Flag(z) => {
                        let zero = opened[k][z].is_some_and(|o| o == [0u8; 32]);
                        engines.field_constant(zero as u64)?
                    }
                    Row::Div(..) | Row::Zdiv(..) => unreachable!(),
                };
                values[k][i] = h;
                owned[k][i] = true;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text(rows: &str, header: &str, outs: &str) -> Vec<u8> {
        format!("EMP_HYBRID_FIELD_DAG_V3\n{header}\n{}\n{rows}{outs}", std::str::from_utf8(MODULUS_DECIMAL).unwrap()).into_bytes()
    }

    #[test]
    fn parses_the_quotient_program() {
        let t = text("I 0\nI 1\nZ 0 1 0\nF 2\n", "2 1 4 2", "O 2 0\nO 3 1\n");
        let p = parse(&t).unwrap();
        assert_eq!(p.rows, vec![Row::Input(0), Row::Input(1), Row::Zdiv(0, 1, 0), Row::Flag(2)]);
        assert_eq!(p.outputs, vec![(2, OMark::Never), (3, OMark::Pub)]);
        assert_eq!(p.openings(), 1);
        assert_eq!(p.sig(), ProgSig { inputs: 2, masks: 1, out_marks: vec![Mark::Never, Mark::Pub] });
    }

    #[test]
    fn refuses_what_lean_refuses() {
        let ok = text("I 0\nI 1\nZ 0 1 0\nF 2\n", "2 1 4 2", "O 2 0\nO 3 1\n");
        assert!(parse(&ok).is_ok());
        let bad = [
            text("I 0\nI 1\nZ 0 1 0\nF 2\n", "2 1 4 2", "O 2 0\nO 3 1\nx"),  // trailing data
            text("I 0\nI 1\nZ 0 1 0\nF 2\n", "2 1 4 2", "O 2 0\nO 3 2\n"),   // mark 2
            text("I 0\nI 1\nZ 0 1 0\nF 1\n", "2 1 4 2", "O 2 0\nO 3 1\n"),   // flag of an input row
            text("I 0\nI 1\nZ 0 1 1\nF 2\n", "2 1 4 2", "O 2 0\nO 3 1\n"),   // mask 1 of 1
            text("I 0\nI 1\nZ 0 1 0\nF 2\n", "2 2 4 2", "O 2 0\nO 3 1\n"),   // a mask never used
            text("I 0\nI 2\nZ 0 1 0\nF 2\n", "2 1 4 2", "O 2 0\nO 3 1\n"),   // input 2 of 2
            text("I 0\nI 1\nZ 0 2 0\nF 2\n", "2 1 4 2", "O 2 0\nO 3 1\n"),   // forward reference
            text("I 0\nI 01\nZ 0 1 0\nF 2\n", "2 1 4 2", "O 2 0\nO 3 1\n"),  // leading zero
            text("I 0\nI  1\nZ 0 1 0\nF 2\n", "2 1 4 2", "O 2 0\nO 3 1\n"),  // two spaces
            text("I 0\nI 1\nZ 0 1 0\nF 2\n", "2 1 4 2", "O 4 0\nO 3 1\n"),   // output out of range
            text("C 57896044618658097711785492504343953926634992332820282019728792003956564819949\n", "0 0 1 0", ""), // C p
            text("I 0\nI 1\nZ 0 1 0\nF 2", "2 1 4 2", ""),                   // no final newline
        ];
        for t in bad {
            assert!(parse(&t).is_err(), "{}", String::from_utf8_lossy(&t));
        }
        let below = text("C 57896044618658097711785492504343953926634992332820282019728792003956564819948\n", "0 0 1 1", "O 0 1\n");
        let p = parse(&below).unwrap();
        let mut want = MODULUS;
        want[0] -= 1;
        assert_eq!(p.rows[0], Row::Const(want, None));
    }
}
