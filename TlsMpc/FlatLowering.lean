import Std
import Std.Tactic.BVDecide.Bitblast.BVExpr
import TlsMpc.AigExport

/-!
# Lowering of the bit-vector compiler's AIG to the flat gate list, in Lean

`AigExport.compile` turns a `BVExpr` into an and-inverter graph (the standard library's
verified bitblaster). The MPC engine reads a flat list of `A a b` / `X a b` / `N a` gates
(`EMP_HYBRID_BOOL_V1`). This module is the step between the two. It replaces the Python
adapter (`hybrid_lowering.py`, `backend_adapter/aig.py`) and produces the same gates in the
same order:

* an AND node whose two operands are the complemented halves of an exclusive-or becomes one
  free `X` gate (`xorSources`);
* the full-adder carry `(a AND b) OR (c AND (a XOR b))`, three AND nodes in the graph, becomes
  `a XOR ((a XOR b) AND (a XOR c))`, one AND gate (`carrySources`);
* nodes no output depends on are skipped (`plan`);
* complemented edges become `N` gates, one per complemented wire.

## What is proved

`lower_sound`: whenever `lower` returns a gate list, every output wire of that list evaluates
(`Flat.eval`) to the value of the corresponding graph reference (`nodeVal`), for every input
assignment. `lower_correct` restates this against the standard library's `AIG.denote`, and
`lowerExpr_correct` composes it with the bitblaster's theorem: output `k` of the gate list
is bit `sel[k]` of `expr.eval assign`, whenever input wire `offsets[v] + b` carries bit `b`
of variable `v`. `Flat.run_eq_eval` shows that for a list accepted by `Flat.wellFormed`
(which `lower` checks before returning), the one-pass evaluation a loader performs computes
`Flat.eval` on every wire. `offsets_getElem?` identifies the offset table with the sums of
the preceding widths.

The exclusive-or and carry rewrites are covered by these theorems (`xorSources_sound`,
`carrySources_sound`); nothing is tested on random inputs. The reachability plan is *not*
trusted: it is a hint. A node the plan skips gets no wire, and a later reference to it makes
`lower` fail rather than emit a wrong gate. That the plan never causes such a failure is
not proved (it would be a completeness statement); neither is any gate-count bound.

The printed text (T2, proof track P3, added in the emitter batch): `printWith_render` (what the
printer hands to `write`, concatenated, is `Flat.render`), `parseFlat_render` (a loader's parse of
that text, `parseFlat`, gives back the gate list, for every well-formed list), `lowerExpr_loaded`
(both composed with `lowerExpr_correct`). The printer's expressions are unchanged
(`appendGate`/`appendOutput` are the `++` chains it always used), so it prints the same bytes;
`gateOk` now also requires a NOT gate's unused operand to be 0 (true of every `lower` result).
The layout file: `TlsMpc/FlatKernelLayout.lean`.

## What is not proved

* That the engines' loaders (C++ `kernel.h`, Rust `loader.rs`) read the text as `parseFlat` does.
* Which output bit belongs to which named field (`selection`, computed by the emitter).
* `lower` terminating without an error.
* The runtime: compiled code and, as everywhere in this project, `ShareCommon`; that
  `Flat.print` in `IO` performs the same `write`s as `printWith` in `Writer` (one definition,
  run in two monads).

No `sorry`, no `native_decide`, no `bv_decide`, no axioms beyond `propext`, `Classical.choice`
and `Quot.sound` (see the `#print axioms` lines at the end).
-/

namespace TlsMpc.FlatLowering

open Std.Sat Std.Tactic.BVDecide
open scoped AIG

abbrev Decls := Array (AIG.Decl BVBit)

/-! ## Source semantics -/

/-- Value of graph node `i`. Agrees with `AIG.denote` on every graph (`nodeVal_eq_denote`). -/
def nodeVal (decls : Decls) (asg : BVBit → Bool) (i : Nat) : Bool :=
  match decls[i]? with
  | some (.atom bit) => asg bit
  | some (.gate l r) =>
      if _h : l.gate < i ∧ r.gate < i then
        (nodeVal decls asg l.gate ^^ l.invert) && (nodeVal decls asg r.gate ^^ r.invert)
      else false
  | _ => false
termination_by i

theorem nodeVal_eq_denote (aig : AIG BVBit) (asg : BVBit → Bool) (i : Nat)
    (hi : i < aig.decls.size) :
    nodeVal aig.decls asg i = ⟦aig, ⟨i, false, hi⟩, asg⟧ := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
      have get : aig.decls[i]? = some aig.decls[i] := Array.getElem?_eq_getElem hi
      cases hd : aig.decls[i] with
      | false =>
          rw [AIG.denote_idx_false hd, nodeVal, get, hd]
      | atom bit =>
          rw [AIG.denote_idx_atom hd, nodeVal, get, hd]
          simp
      | gate lhs rhs =>
          have bounds := aig.hdag hi hd
          rw [AIG.denote_idx_gate hd, nodeVal, get, hd]
          simp only [dif_pos bounds, Bool.xor_false]
          rw [ih lhs.gate bounds.1 (by omega), ih rhs.gate bounds.2 (by omega)]
          simp [AIG.denote]

theorem nodeVal_false {decls : Decls} (asg : BVBit → Bool) {i : Nat}
    (h : decls[i]? = some .false) : nodeVal decls asg i = false := by
  rw [nodeVal, h]

theorem nodeVal_atom {decls : Decls} (asg : BVBit → Bool) {i : Nat} {bit : BVBit}
    (h : decls[i]? = some (.atom bit)) : nodeVal decls asg i = asg bit := by
  rw [nodeVal, h]

theorem nodeVal_gate {decls : Decls} (dag : AIG.IsDAG BVBit decls) (asg : BVBit → Bool)
    {i : Nat} {l r : AIG.Fanin} (h : decls[i]? = some (.gate l r)) :
    nodeVal decls asg i =
      ((nodeVal decls asg l.gate ^^ l.invert) && (nodeVal decls asg r.gate ^^ r.invert)) := by
  obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.mp h
  have bounds := dag hi he
  rw [nodeVal.eq_1 decls asg i, h]
  simp only [dif_pos bounds]

/-! ## Flat gate lists -/

/-- Gate `k` is wire `inputs + k`. `opa[k] = 4 * a + op` with `op` 0 for AND, 1 for XOR,
2 for NOT; `opb[k]` is the second operand (0 for NOT). Two arrays of small numbers keep a
gate at sixteen bytes. -/
structure Flat where
  inputs : Nat
  opa : Array Nat
  opb : Array Nat
  outputs : Array Nat

def opVal (op : Nat) (x y : Bool) : Bool :=
  match op with
  | 0 => x && y
  | 1 => x ^^ y
  | _ => !x

/-- Value of wire `w`. A gate that refers to itself or to a later wire evaluates to false;
`Flat.wellFormed` rules such gates out. -/
def wireVal (n : Nat) (opa opb : Array Nat) (inp : Nat → Bool) (w : Nat) : Bool :=
  if w < n then inp w else
    match opa[w - n]? with
    | none => false
    | some c =>
        if _h : c / 4 < w ∧ opb[w - n]?.getD 0 < w then
          opVal (c % 4) (wireVal n opa opb inp (c / 4)) (wireVal n opa opb inp (opb[w - n]?.getD 0))
        else false
termination_by w

def Flat.eval (f : Flat) (inp : Nat → Bool) (w : Nat) : Bool := wireVal f.inputs f.opa f.opb inp w

theorem wireVal_prefix {n m : Nat} {opa opb opa' opb' : Array Nat} {inp : Nat → Bool}
    (ha : ∀ k, k < m → opa'[k]? = opa[k]?) (hb : ∀ k, k < m → opb'[k]? = opb[k]?) :
    ∀ w, w < n + m → wireVal n opa' opb' inp w = wireVal n opa opb inp w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
      intro hw
      rw [wireVal.eq_1 n opa' opb' inp w, wireVal.eq_1 n opa opb inp w]
      by_cases hn : w < n
      · simp only [hn, if_true]
      · simp only [hn, if_false]
        rw [ha (w - n) (by omega), hb (w - n) (by omega)]
        cases opa[w - n]? with
        | none => rfl
        | some c =>
            simp only
            by_cases h : c / 4 < w ∧ opb[w - n]?.getD 0 < w
            · simp only [dif_pos h]
              rw [ih _ h.1 (by omega), ih _ h.2 (by omega)]
            · simp only [dif_neg h]

theorem wireVal_push {n : Nat} {opa opb : Array Nat} {inp : Nat → Bool} {op a b : Nat}
    (hsz : opb.size = opa.size) (hop : op < 4) (ha : a < n + opa.size) (hb : b < n + opa.size) :
    wireVal n (opa.push (4 * a + op)) (opb.push b) inp (n + opa.size) =
      opVal op (wireVal n opa opb inp a) (wireVal n opa opb inp b) := by
  rw [wireVal.eq_1 n (opa.push (4 * a + op)) (opb.push b) inp (n + opa.size)]
  have h1 : ¬ (n + opa.size < n) := by omega
  have h2 : n + opa.size - n = opa.size := by omega
  have h3 : (opa.push (4 * a + op))[opa.size]? = some (4 * a + op) := by simp
  have h4 : (opb.push b)[opa.size]? = some b := by rw [← hsz]; simp
  have h5 : (4 * a + op) / 4 = a := by omega
  have h6 : (4 * a + op) % 4 = op := by omega
  simp only [h1, if_false, h2, h3, h4, Option.getD_some, h5, h6]
  rw [dif_pos ⟨ha, hb⟩]
  have pa : ∀ k, k < opa.size → (opa.push (4 * a + op))[k]? = opa[k]? := by
    intro k hk; rw [Array.getElem?_push, if_neg (by omega)]
  have pb : ∀ k, k < opa.size → (opb.push b)[k]? = opb[k]? := by
    intro k hk; rw [Array.getElem?_push, if_neg (by omega)]
  rw [wireVal_prefix pa pb a ha, wireVal_prefix pa pb b hb]

/-- The constant-false gate `X 0 0`, also when there is no wire 0 to read. -/
theorem wireVal_push_zero {n : Nat} {opa opb : Array Nat} {inp : Nat → Bool}
    (hsz : opb.size = opa.size) :
    wireVal n (opa.push (4 * 0 + 1)) (opb.push 0) inp (n + opa.size) = false := by
  rw [wireVal.eq_1 n (opa.push (4 * 0 + 1)) (opb.push 0) inp (n + opa.size)]
  have h1 : ¬ (n + opa.size < n) := by omega
  have h2 : n + opa.size - n = opa.size := by omega
  have h3 : (opa.push (4 * 0 + 1))[opa.size]? = some 1 := by simp
  have h4 : (opb.push 0)[opa.size]? = some 0 := by rw [← hsz]; simp
  simp only [h1, if_false, h2, h3, h4, Option.getD_some]
  split
  · simp [opVal]
  · rfl

/-! ## Pattern recognition -/

/-- `l`, `r` are the operands of an AND node. When both are complemented and point at AND
nodes over the same two nodes with opposite complements, the node is the exclusive-or of
the returned literals. -/
def xorSources (decls : Decls) (l r : AIG.Fanin) : Option (Nat × Bool × Nat × Bool) :=
  if l.invert && r.invert then
    match decls[l.gate]?, decls[r.gate]? with
    | some (.gate a b), some (.gate c d) =>
        if (a.gate == c.gate && b.gate == d.gate && a.invert != c.invert && b.invert != d.invert) ||
            (a.gate == d.gate && b.gate == c.gate && a.invert != d.invert && b.invert != c.invert)
        then some (a.gate, a.invert, b.gate, b.invert) else none
    | _, _ => none
  else none

def xorOf (decls : Decls) (x : Nat) : Option (Nat × Bool × Nat × Bool) :=
  match decls[x]? with
  | some (.gate l r) => xorSources decls l r
  | _ => none

/-- `pa`, `pb`: operands of `P = a' AND b'`. `x`, `c`: operands of `Q`, where `x` should be
the literal `a' XOR b'`. Returns `(a, a inverted, x, x inverted, c, c inverted)`. -/
def carryPick (decls : Decls) (pa pb x c : AIG.Fanin) : Option (Nat × Bool × Nat × Bool × Nat × Bool) :=
  match xorOf decls x.gate with
  | some (xa, xai, xb, xbi) =>
      if ((xa == pa.gate && xb == pb.gate) || (xa == pb.gate && xb == pa.gate)) &&
          (((xai ^^ xbi) ^^ x.invert) == (pa.invert ^^ pb.invert))
      then some (pa.gate, pa.invert, x.gate, x.invert, c.gate, c.invert) else none
  | none => none

def carryTry (decls : Decls) (p q : Nat) : Option (Nat × Bool × Nat × Bool × Nat × Bool) :=
  match decls[p]?, decls[q]? with
  | some (.gate pa pb), some (.gate q1 q2) =>
      if pa.gate == pb.gate then none else
        match carryPick decls pa pb q1 q2 with
        | some s => some s
        | none => carryPick decls pa pb q2 q1
  | _, _ => none

/-- The full-adder carry: node `= AND(NOT P, NOT Q)`, `P = a' AND b'`, `Q = c' AND (a' XOR b')`. -/
def carrySources (decls : Decls) (l r : AIG.Fanin) : Option (Nat × Bool × Nat × Bool × Nat × Bool) :=
  if l.invert && r.invert then
    match carryTry decls l.gate r.gate with
    | some s => some s
    | none => carryTry decls r.gate l.gate
  else none

private theorem xor_bool (A B ai bi ci di : Bool) (h1 : ai ≠ ci) (h2 : bi ≠ di) :
    ((((A ^^ ai) && (B ^^ bi)) ^^ true) && (((A ^^ ci) && (B ^^ di)) ^^ true)) =
      ((A ^^ ai) ^^ (B ^^ bi)) := by
  cases A <;> cases B <;> cases ai <;> cases bi <;> cases ci <;> cases di <;> simp_all

private theorem xor_bool' (A B ai bi ci di : Bool) (h1 : ai ≠ di) (h2 : bi ≠ ci) :
    ((((A ^^ ai) && (B ^^ bi)) ^^ true) && (((B ^^ ci) && (A ^^ di)) ^^ true)) =
      ((A ^^ ai) ^^ (B ^^ bi)) := by
  cases A <;> cases B <;> cases ai <;> cases bi <;> cases ci <;> cases di <;> simp_all

theorem xorSources_sound {decls : Decls} (dag : AIG.IsDAG BVBit decls) (asg : BVBit → Bool)
    {i : Nat} {l r : AIG.Fanin} {a b : Nat} {ai bi : Bool}
    (hi : decls[i]? = some (.gate l r)) (h : xorSources decls l r = some (a, ai, b, bi)) :
    nodeVal decls asg i = ((nodeVal decls asg a ^^ ai) ^^ (nodeVal decls asg b ^^ bi)) := by
  rw [nodeVal_gate dag asg hi]
  unfold xorSources at h
  split at h
  · rename_i hinv
    simp only [Bool.and_eq_true] at hinv
    split at h
    · rename_i fa fb fc fd hl hr
      rw [nodeVal_gate dag asg hl, nodeVal_gate dag asg hr, hinv.1, hinv.2]
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
        rcases hc with ⟨⟨⟨g1, g2⟩, i1⟩, i2⟩ | ⟨⟨⟨g1, g2⟩, i1⟩, i2⟩
        · rw [← g1, ← g2]; exact xor_bool _ _ _ _ _ _ i1 i2
        · rw [← g1, ← g2]; exact xor_bool' _ _ _ _ _ _ i1 i2
      · cases h
    · cases h
  · cases h

theorem xorOf_sound {decls : Decls} (dag : AIG.IsDAG BVBit decls) (asg : BVBit → Bool)
    {x a b : Nat} {ai bi : Bool} (h : xorOf decls x = some (a, ai, b, bi)) :
    nodeVal decls asg x = ((nodeVal decls asg a ^^ ai) ^^ (nodeVal decls asg b ^^ bi)) := by
  unfold xorOf at h
  split at h
  · rename_i l r hx
    exact xorSources_sound dag asg hx h
  · cases h

private theorem pick_bool (A B xai xbi xi pai pbi : Bool)
    (h : ((xai ^^ xbi) ^^ xi) = (pai ^^ pbi)) :
    (((A ^^ xai) ^^ (B ^^ xbi)) ^^ xi) = ((A ^^ pai) ^^ (B ^^ pbi)) := by
  cases A <;> cases B <;> cases xai <;> cases xbi <;> cases xi <;> cases pai <;> cases pbi <;> simp_all

private theorem pick_bool' (A B xai xbi xi pai pbi : Bool)
    (h : ((xai ^^ xbi) ^^ xi) = (pai ^^ pbi)) :
    (((B ^^ xai) ^^ (A ^^ xbi)) ^^ xi) = ((A ^^ pai) ^^ (B ^^ pbi)) := by
  cases A <;> cases B <;> cases xai <;> cases xbi <;> cases xi <;> cases pai <;> cases pbi <;> simp_all

theorem carryPick_sound {decls : Decls} (dag : AIG.IsDAG BVBit decls) (asg : BVBit → Bool)
    {pa pb x c : AIG.Fanin} {a xg cg : Nat} {ai xi ci : Bool}
    (h : carryPick decls pa pb x c = some (a, ai, xg, xi, cg, ci)) :
    a = pa.gate ∧ ai = pa.invert ∧ xg = x.gate ∧ xi = x.invert ∧ cg = c.gate ∧ ci = c.invert ∧
      (nodeVal decls asg x.gate ^^ x.invert) =
        ((nodeVal decls asg pa.gate ^^ pa.invert) ^^ (nodeVal decls asg pb.gate ^^ pb.invert)) := by
  unfold carryPick at h
  split at h
  · rename_i xa xai xb xbi hx
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      rw [xorOf_sound dag asg hx]
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
      rcases hc with ⟨⟨g1, g2⟩ | ⟨g1, g2⟩, hp⟩
      · rw [g1, g2]; exact pick_bool _ _ _ _ _ _ _ hp
      · rw [g1, g2]; exact pick_bool' _ _ _ _ _ _ _ hp
    · cases h
  · cases h

private theorem carry_bool (A B C X : Bool) (hX : X = (A ^^ B)) :
    (((A && B) ^^ true) && ((X && C) ^^ true)) = !(A ^^ (X && (A ^^ C))) := by
  subst hX; cases A <;> cases B <;> cases C <;> rfl

private theorem carry_bool' (A B C X : Bool) (hX : X = (A ^^ B)) :
    (((A && B) ^^ true) && ((C && X) ^^ true)) = !(A ^^ (X && (A ^^ C))) := by
  subst hX; cases A <;> cases B <;> cases C <;> rfl

theorem carryTry_sound {decls : Decls} (dag : AIG.IsDAG BVBit decls) (asg : BVBit → Bool)
    {p q a x c : Nat} {ai xi ci : Bool}
    (h : carryTry decls p q = some (a, ai, x, xi, c, ci)) :
    ((nodeVal decls asg p ^^ true) && (nodeVal decls asg q ^^ true)) =
      !((nodeVal decls asg a ^^ ai) ^^
        ((nodeVal decls asg x ^^ xi) && ((nodeVal decls asg a ^^ ai) ^^ (nodeVal decls asg c ^^ ci)))) := by
  unfold carryTry at h
  split at h
  · rename_i pa pb q1 q2 hp hq
    rw [nodeVal_gate dag asg hp, nodeVal_gate dag asg hq]
    split at h
    · cases h
    · split at h
      · rename_i s hs
        cases h
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, hx⟩ := carryPick_sound dag asg hs
        exact carry_bool _ _ _ _ hx
      · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, hx⟩ := carryPick_sound dag asg h
        exact carry_bool' _ _ _ _ hx
  · cases h

theorem carrySources_sound {decls : Decls} (dag : AIG.IsDAG BVBit decls) (asg : BVBit → Bool)
    {i : Nat} {l r : AIG.Fanin} {a x c : Nat} {ai xi ci : Bool}
    (hi : decls[i]? = some (.gate l r)) (h : carrySources decls l r = some (a, ai, x, xi, c, ci)) :
    nodeVal decls asg i =
      !((nodeVal decls asg a ^^ ai) ^^
        ((nodeVal decls asg x ^^ xi) && ((nodeVal decls asg a ^^ ai) ^^ (nodeVal decls asg c ^^ ci)))) := by
  rw [nodeVal_gate dag asg hi]
  unfold carrySources at h
  split at h
  · rename_i hinv
    simp only [Bool.and_eq_true] at hinv
    rw [hinv.1, hinv.2]
    split at h
    · rename_i s hs
      cases h
      exact carryTry_sound dag asg hs
    · rw [Bool.and_comm]
      exact carryTry_sound dag asg h
  · cases h

/-! ## Emission -/

/-- `wires[j]` is one more than the wire of node `j` (0: no wire). `neg[w]` is one more than
the wire carrying the complement of wire `w` (0: none yet). `zero` likewise for the
constant-false wire. -/
structure St where
  opa : Array Nat := #[]
  opb : Array Nat := #[]
  neg : Array Nat := #[]
  wires : Array Nat := #[]
  zero : Nat := 0

def pushGate (n : Nat) (st : St) (op a b : Nat) : Nat × St :=
  (n + st.opa.size,
    { st with opa := st.opa.push (4 * a + op), opb := st.opb.push b, neg := st.neg.push 0 })

/-- The wire carrying the complement of wire `w`: an `N` gate, emitted once per wire. -/
def negate (n : Nat) (st : St) (w : Nat) : Nat × St :=
  match st.neg.getD w 0 with
  | v + 1 => (v, st)
  | 0 =>
      let r := pushGate n st 2 w 0
      (r.1, { r.2 with neg := r.2.neg.setIfInBounds w (r.1 + 1) })

/-- Wire of the literal (node `j`, complemented when `flip`). -/
def lit (n : Nat) (st : St) (j : Nat) (flip : Bool) : Except String (Nat × St) :=
  match st.wires.getD j 0 with
  | w + 1 => if flip then .ok (negate n st w) else .ok (w, st)
  | 0 => .error "flat lowering: operand has no wire"

/-- One gate over two literals. -/
def emit2 (n : Nat) (st : St) (op a : Nat) (ai : Bool) (b : Nat) (bi : Bool) : Except String (Nat × St) :=
  match lit n st a ai with
  | .error e => .error e
  | .ok r1 =>
      match lit n r1.2 b bi with
      | .error e => .error e
      | .ok r2 => .ok (pushGate n r2.2 op r1.1 r2.1)

/-- `NOT (a XOR (x AND (a XOR c)))`: the node stores the complement of the carry. -/
def emitCarry (n : Nat) (st : St) (a : Nat) (ai : Bool) (x : Nat) (xi : Bool) (c : Nat) (ci : Bool) :
    Except String (Nat × St) :=
  match lit n st a ai with
  | .error e => .error e
  | .ok r1 =>
      match lit n r1.2 x xi with
      | .error e => .error e
      | .ok r2 =>
          match lit n r2.2 c ci with
          | .error e => .error e
          | .ok r3 =>
              let t := pushGate n r3.2 1 r1.1 r3.1
              let u := pushGate n t.2 0 r2.1 t.1
              let v := pushGate n u.2 1 r1.1 u.1
              .ok (negate n v.2 v.1)

def emitGate (decls : Decls) (kind : UInt8) (n : Nat) (st : St) (l r : AIG.Fanin) :
    Except String (Nat × St) :=
  if kind == 3 then
    match carrySources decls l r with
    | some (a, ai, x, xi, c, ci) => emitCarry n st a ai x xi c ci
    | none => .error "flat lowering: carry plan"
  else if kind == 2 then
    match xorSources decls l r with
    | some (a, ai, b, bi) => emit2 n st 1 a ai b bi
    | none => .error "flat lowering: exclusive-or plan"
  else emit2 n st 0 l.gate l.invert r.gate r.invert

def emitNode (decls : Decls) (kinds : ByteArray) (widths offs : Array Nat) (n i : Nat) (st : St) :
    Except String St :=
  if kinds.get! i == 0 then .ok { st with wires := st.wires.push 0 } else
    match decls[i]? with
    | none => .error "flat lowering: node index"
    | some .false =>
        match st.zero with
        | z + 1 => .ok { st with wires := st.wires.push (z + 1) }
        | 0 =>
            let r := pushGate n st 1 0 0
            .ok { r.2 with zero := r.1 + 1, wires := r.2.wires.push (r.1 + 1) }
    | some (.atom bit) =>
        match widths[bit.var]?, offs[bit.var]? with
        | some width, some off =>
            if bit.w = width ∧ off + bit.idx.val < n then
              .ok { st with wires := st.wires.push (off + bit.idx.val + 1) }
            else .error "flat lowering: input reference"
        | _, _ => .error "flat lowering: input variable"
    | some (.gate l r) =>
        match emitGate decls (kinds.get! i) n st l r with
        | .error e => .error e
        | .ok res => .ok { res.2 with wires := res.2.wires.push (res.1 + 1) }

def emitAll (decls : Decls) (kinds : ByteArray) (widths offs : Array Nat) (n i : Nat) (st : St) :
    Except String St :=
  if i < decls.size then
    match emitNode decls kinds widths offs n i st with
    | .error e => .error e
    | .ok st' => emitAll decls kinds widths offs n (i + 1) st'
  else .ok st
termination_by decls.size - i

def emitOutputs (n : Nat) (outs : Array (Nat × Bool)) (k : Nat) (st : St) (acc : Array Nat) :
    Except String (St × Array Nat) :=
  if h : k < outs.size then
    match lit n st outs[k].1 outs[k].2 with
    | .error e => .error e
    | .ok r => emitOutputs n outs (k + 1) r.2 (acc.push r.1)
  else .ok (st, acc)
termination_by outs.size - k

/-! ## The plan: which nodes get a wire, and in which form (a hint; not trusted) -/

def mark (kinds : ByteArray) (j : Nat) : ByteArray :=
  if kinds.get! j == 0 then kinds.set! j 1 else kinds

/-- 0: unreachable, 1: as is, 2: exclusive-or, 3: one-AND carry. Operands precede their
node, so one sweep from the last node to the first sees every reachable node after all of
its users. -/
def planFrom (decls : Decls) : Nat → ByteArray → ByteArray
  | 0, kinds => kinds
  | i + 1, kinds =>
      if kinds.get! i == 0 then planFrom decls i kinds else
        match decls[i]? with
        | some (.gate l r) =>
            match xorSources decls l r with
            | some (a, _, b, _) => planFrom decls i (mark (mark (kinds.set! i 2) a) b)
            | none =>
                match carrySources decls l r with
                | some (a, _, x, _, c, _) => planFrom decls i (mark (mark (mark (kinds.set! i 3) a) x) c)
                | none => planFrom decls i (mark (mark (kinds.set! i 1) l.gate) r.gate)
        | _ => planFrom decls i (kinds.set! i 1)

def plan (decls : Decls) (outs : Array (Nat × Bool)) : ByteArray :=
  let blank := Nat.fold decls.size (fun _ _ kinds => kinds.push 0) (ByteArray.emptyWithCapacity decls.size)
  planFrom decls decls.size (outs.foldl (fun kinds o => mark kinds o.1) blank)

/-! ## Input layout -/

/-- `offsets[v]`: first wire of variable `v` (bit `b` of the variable is wire `offsets[v] + b`). -/
def offsets (widths : Array Nat) : Array Nat :=
  (widths.foldl (fun (acc : Array Nat × Nat) w => (acc.1.push acc.2, acc.2 + w)) (#[], 0)).1

def totalBits (widths : Array Nat) : Nat := widths.foldl (· + ·) 0

/-! ## Well-formedness and one-pass evaluation -/

/-- Gate `k` reads earlier wires, is an AND, XOR or NOT, and a NOT has second operand 0 (the
printer does not print it; the parser reads it back as 0). -/
def gateOk (f : Flat) (k : Nat) : Bool :=
  match f.opa[k]?, f.opb[k]? with
  | some c, some b => c / 4 < f.inputs + k && b < f.inputs + k && c % 4 < 3 && (c % 4 != 2 || b == 0)
  | _, _ => false

def gatesOk (f : Flat) : Nat → Bool
  | 0 => true
  | k + 1 => gateOk f k && gatesOk f k

/-- Every gate reads earlier wires only and every output is a wire. -/
def Flat.wellFormed (f : Flat) : Bool :=
  f.opb.size == f.opa.size && gatesOk f f.opa.size && f.outputs.all (· < f.inputs + f.opa.size)

/-- What a loader does with gate `k`: append its value, read from the values so far. -/
def Flat.stepRun (f : Flat) (k : Nat) (vals : Array Bool) : Array Bool :=
  vals.push (opVal (f.opa[k]?.getD 0 % 4) (vals[f.opa[k]?.getD 0 / 4]?.getD false)
    (vals[f.opb[k]?.getD 0]?.getD false))

/-- The values of all wires after the first `k` gates, computed in one pass. A specification
of the loader's evaluation order (not meant to be executed: it recurses once per gate). -/
def Flat.runTo (f : Flat) (inp : Nat → Bool) : Nat → Array Bool
  | 0 => Array.ofFn (n := f.inputs) fun i => inp i.val
  | k + 1 => f.stepRun k (f.runTo inp k)

def Flat.run (f : Flat) (inp : Nat → Bool) : Array Bool := f.runTo inp f.opa.size

theorem Flat.runTo_spec (f : Flat) (inp : Nat → Bool) :
    ∀ m, gatesOk f m = true → (f.runTo inp m).size = f.inputs + m ∧
      ∀ w, w < f.inputs + m → (f.runTo inp m)[w]? = some (wireVal f.inputs f.opa f.opb inp w) := by
  intro m
  induction m with
  | zero =>
      intro _
      refine ⟨by simp [Flat.runTo], fun w hw => ?_⟩
      have hw' : w < f.inputs := by omega
      rw [wireVal.eq_1]
      simp [Flat.runTo, hw']
  | succ m ih =>
      intro hok
      simp only [gatesOk, Bool.and_eq_true] at hok
      obtain ⟨hsize, hvals⟩ := ih hok.2
      have hg := hok.1
      unfold gateOk at hg
      split at hg
      · rename_i c b hc hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
        refine ⟨by simp [Flat.runTo, Flat.stepRun, hsize]; omega, fun w hw => ?_⟩
        show (f.stepRun m (f.runTo inp m))[w]? = _
        unfold Flat.stepRun
        rw [Array.getElem?_push, hsize]
        by_cases hlast : w = f.inputs + m
        · rw [if_pos hlast, hc, hb, hlast, wireVal.eq_1 f.inputs f.opa f.opb inp (f.inputs + m)]
          have h1 : ¬ (f.inputs + m < f.inputs) := by omega
          have h2 : f.inputs + m - f.inputs = m := by omega
          simp only [h1, if_false, h2, hc, hb, Option.getD_some]
          rw [dif_pos ⟨hg.1.1.1, hg.1.1.2⟩, hvals _ hg.1.1.1, hvals _ hg.1.1.2]
          simp
        · rw [if_neg hlast]
          exact hvals w (by omega)
      · cases hg

/-- On a well-formed gate list the one-pass evaluation and `Flat.eval` agree on every wire. -/
theorem Flat.run_eq_eval (f : Flat) (inp : Nat → Bool) (hwf : f.wellFormed = true) (w : Nat)
    (hw : w < f.inputs + f.opa.size) : (f.run inp)[w]? = some (f.eval inp w) := by
  simp only [Flat.wellFormed, Bool.and_eq_true] at hwf
  exact (f.runTo_spec inp f.opa.size hwf.1.2).2 w hw

theorem offsets_spec (widths : Array Nat) :
    (offsets widths).size = widths.size ∧
      ∀ v, v < widths.size → (offsets widths)[v]? = some (widths.toList.take v).sum := by
  unfold offsets
  have key := Array.foldl_induction (as := widths)
    (motive := fun i (acc : Array Nat × Nat) => acc.2 = (widths.toList.take i).sum ∧ acc.1.size = i ∧
      ∀ v, v < i → acc.1[v]? = some (widths.toList.take v).sum)
    (init := (#[], 0)) (f := fun acc w => (acc.1.push acc.2, acc.2 + w))
    ⟨by simp, by simp, fun v hv => by omega⟩
    (fun i acc ⟨hsum, hsize, hget⟩ => by
      refine ⟨?_, by simp [hsize], fun v hv => ?_⟩
      · simp [List.take_add_one, hsum]
      · show (acc.1.push acc.2)[v]? = _
        rw [Array.getElem?_push, hsize]
        by_cases hvi : v = i.val
        · rw [if_pos hvi, hsum, hvi]
        · rw [if_neg hvi]; exact hget v (by omega))
  exact ⟨key.2.1, fun v hv => by
    have := key.2.2 v hv
    exact this⟩

/-- `offsets[v]` is the sum of the widths of the variables before `v`. -/
theorem offsets_getElem? (widths : Array Nat) (v : Nat) (hv : v < widths.size) :
    (offsets widths)[v]? = some (widths.toList.take v).sum := (offsets_spec widths).2 v hv

/-- Number of AND gates: the only gates with a cost in the Boolean engine. -/
def Flat.andCount (f : Flat) : Nat := f.opa.foldl (fun count c => if c % 4 == 0 then count + 1 else count) 0

/-! ## The printer (`EMP_HYBRID_BOOL_V1`)

The text the engines load. The pieces below are the expressions the printer has always used
(`appendGate`, `appendOutput`: the same `++` chains, the same flushes), so the printed bytes are
unchanged; what is new is that they are named, the printer is written once for any monad
(`printWith`), and `Flat.render` is the whole text as one string, with `printWith_render` (what the
printer writes, concatenated, is `render`) and `parseFlat_render` (parsing `render` gives back the
gate list) below. -/

/-- `buffer` followed by gate `(c, b)`'s line, exactly as the printer appends it. -/
@[inline] def appendGate (buffer : String) (c b : Nat) : String :=
  match c % 4 with
  | 0 => buffer ++ "A " ++ toString (c / 4) ++ " " ++ toString b ++ "\n"
  | 1 => buffer ++ "X " ++ toString (c / 4) ++ " " ++ toString b ++ "\n"
  | _ => buffer ++ "N " ++ toString (c / 4) ++ "\n"

/-- `buffer` followed by output `k` (wire `o`), exactly as the printer appends it. -/
@[inline] def appendOutput (buffer : String) (k o : Nat) : String :=
  if k == 0 then buffer ++ toString o else buffer ++ " " ++ toString o

/-- Gate `(c, b)`'s line. -/
def gateLine (c b : Nat) : String := appendGate "" c b

/-- Output `k`'s text (preceded by a space unless it is the first). -/
def outputPiece (k o : Nat) : String := appendOutput "" k o

def Flat.header (f : Flat) : String :=
  "EMP_HYBRID_BOOL_V1\n" ++ toString f.inputs ++ " " ++ toString f.opa.size ++ " " ++ toString f.outputs.size ++ "\n"

/-- Append a piece; hand the buffer to `write` once it reaches 64 kB. -/
@[inline] def Flat.flushPiece [Monad m] (write : String → m Unit) (buffer : String) : m (ForInStep String) :=
  if buffer.utf8ByteSize ≥ 65536 then do write buffer; pure (.yield "") else pure (.yield buffer)

/-- The printer, for any monad: the header, the gate lines, `O` and the output wires, handed to
`write` in pieces of about 64 kB so that a large circuit is never held as one string. -/
@[inline] def Flat.printWith [Monad m] (f : Flat) (write : String → m Unit) : m Unit := do
  write f.header
  let buffer ← forIn [0:f.opa.size] "" fun k buffer =>
    Flat.flushPiece write (appendGate buffer f.opa[k]! f.opb[k]!)
  let buffer ← forIn [0:f.outputs.size] (buffer ++ "O ") fun k buffer =>
    Flat.flushPiece write (appendOutput buffer k f.outputs[k]!)
  write (buffer ++ "\n")

/-- `EMP_HYBRID_BOOL_V1` text, handed to `write` in pieces (what the emitters call). -/
def Flat.print (f : Flat) (write : String → IO Unit) : IO Unit := f.printWith write

/-- The whole text as one string (for the theorems; the printer never builds it). -/
def Flat.render (f : Flat) : String :=
  f.header ++ String.join ((List.range' 0 f.opa.size).map fun k => gateLine f.opa[k]! f.opb[k]!) ++ "O " ++
    String.join ((List.range' 0 f.outputs.size).map fun k => outputPiece k f.outputs[k]!) ++ "\n"

/-! ## The lowering -/

def lower (decls : Decls) (widths : Array Nat) (outs : Array (Nat × Bool)) : Except String Flat :=
  let n := totalBits widths
  match emitAll decls (plan decls outs) widths (offsets widths) n 0 { neg := Array.replicate n 0 } with
  | .error e => .error e
  | .ok st =>
      match emitOutputs n outs 0 st #[] with
      | .error e => .error e
      | .ok r =>
          let flat : Flat := ⟨n, r.1.opa, r.1.opb, r.2⟩
          if flat.wellFormed then .ok flat else .error "flat lowering: gate list is not well formed"

/-! ## Soundness -/

section Sound

variable (n : Nat) (inp : Nat → Bool)

def Good (st : St) (w : Nat) (b : Bool) : Prop :=
  w < n + st.opa.size ∧ wireVal n st.opa st.opb inp w = b

/-- `st'` has the gates of `st`, possibly more, and the same node wires. -/
structure Ext (st st' : St) : Prop where
  size : st.opa.size ≤ st'.opa.size
  opa : ∀ k, k < st.opa.size → st'.opa[k]? = st.opa[k]?
  opb : ∀ k, k < st.opa.size → st'.opb[k]? = st.opb[k]?
  wires : st'.wires = st.wires

theorem Ext.refl (st : St) : Ext st st := ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem Ext.trans {a b c : St} (h1 : Ext a b) (h2 : Ext b c) : Ext a c :=
  ⟨Nat.le_trans h1.size h2.size,
    fun k hk => by rw [h2.opa k (Nat.lt_of_lt_of_le hk h1.size), h1.opa k hk],
    fun k hk => by rw [h2.opb k (Nat.lt_of_lt_of_le hk h1.size), h1.opb k hk],
    by rw [h2.wires, h1.wires]⟩

variable {n inp}

theorem Ext.val {st st' : St} (e : Ext st st') {w : Nat} (hw : w < n + st.opa.size) :
    wireVal n st'.opa st'.opb inp w = wireVal n st.opa st.opb inp w :=
  wireVal_prefix e.opa e.opb w hw

theorem Good.mono {st st' : St} {w : Nat} {b : Bool} (g : Good n inp st w b) (e : Ext st st') :
    Good n inp st' w b :=
  ⟨Nat.lt_of_lt_of_le g.1 (Nat.add_le_add_left e.size n), by rw [e.val g.1]; exact g.2⟩

variable (n inp) in
structure Inv (decls : Decls) (asg : BVBit → Bool) (st : St) : Prop where
  sz : st.opb.size = st.opa.size
  wires : ∀ (j w : Nat), st.wires[j]? = some (w + 1) → Good n inp st w (nodeVal decls asg j)
  neg : ∀ (w v : Nat), st.neg[w]? = some (v + 1) →
    w < n + st.opa.size ∧ Good n inp st v (!wireVal n st.opa st.opb inp w)
  zero : ∀ z, st.zero = z + 1 → Good n inp st z false

variable {decls : Decls} {asg : BVBit → Bool}

theorem Inv.mono {st st' : St} (h : Inv n inp decls asg st) (e : Ext st st')
    (hsz : st'.opb.size = st'.opa.size)
    (hneg : ∀ (w v : Nat), st'.neg[w]? = some (v + 1) → st.neg[w]? = some (v + 1))
    (hzero : st'.zero = st.zero) : Inv n inp decls asg st' where
  sz := hsz
  wires := fun j w hj => (h.wires j w (by rw [← e.wires]; exact hj)).mono e
  neg := fun w v hw => by
    have old := h.neg w v (hneg w v hw)
    refine ⟨Nat.lt_of_lt_of_le old.1 (Nat.add_le_add_left e.size n), ?_⟩
    rw [e.val old.1]
    exact old.2.mono e
  zero := fun z hz => (h.zero z (by rw [← hzero]; exact hz)).mono e

theorem pushGate_ext {st : St} (hsz : st.opb.size = st.opa.size) (op a b : Nat) :
    Ext st (pushGate n st op a b).2 where
  size := by simp [pushGate]
  opa := fun k hk => by
    show (st.opa.push _)[k]? = _
    rw [Array.getElem?_push, if_neg (by omega)]
  opb := fun k hk => by
    show (st.opb.push _)[k]? = _
    rw [Array.getElem?_push, if_neg (by omega)]
  wires := rfl

theorem pushGate_inv {st : St} (h : Inv n inp decls asg st) (op a b : Nat) :
    Inv n inp decls asg (pushGate n st op a b).2 := by
  refine h.mono (pushGate_ext h.sz op a b) ?_ ?_ rfl
  · show (st.opb.push _).size = (st.opa.push _).size
    simp [h.sz]
  · intro w v hw
    have hw' : (st.neg.push 0)[w]? = some (v + 1) := hw
    rw [Array.getElem?_push] at hw'
    split at hw'
    · simp at hw'
    · exact hw'

theorem pushGate_good {st : St} (h : Inv n inp decls asg st) {op a b : Nat} {x y : Bool}
    (hop : op < 4) (ga : Good n inp st a x) (gb : Good n inp st b y) :
    Good n inp (pushGate n st op a b).2 (pushGate n st op a b).1 (opVal op x y) := by
  refine ⟨?_, ?_⟩
  · show n + st.opa.size < n + (st.opa.push _).size
    simp
  · show wireVal n (st.opa.push (4 * a + op)) (st.opb.push b) inp (n + st.opa.size) = _
    rw [wireVal_push h.sz hop ga.1 gb.1, ga.2, gb.2]

theorem negate_spec {st : St} (h : Inv n inp decls asg st) {w : Nat} {x : Bool}
    (g : Good n inp st w x) :
    Inv n inp decls asg (negate n st w).2 ∧ Ext st (negate n st w).2 ∧
      Good n inp (negate n st w).2 (negate n st w).1 (!x) := by
  unfold negate
  split
  · rename_i v hv
    have hv' : st.neg[w]? = some (v + 1) := by
      rw [Array.getD_eq_getD_getElem?] at hv
      cases hx : st.neg[w]? with
      | none => rw [hx] at hv; simp at hv
      | some y => rw [hx] at hv; simp at hv; rw [hv]
    have := (h.neg w v hv').2
    rw [g.2] at this
    exact ⟨h, Ext.refl st, this⟩
  · have e := pushGate_ext (n := n) h.sz 2 w 0
    have hi := pushGate_inv h 2 w 0
    have g0 : Good n inp st 0 (wireVal n st.opa st.opb inp 0) := ⟨by have := g.1; omega, rfl⟩
    have gv : Good n inp (pushGate n st 2 w 0).2 (pushGate n st 2 w 0).1 (!x) :=
      pushGate_good h (by omega) g g0
    refine ⟨⟨hi.sz, hi.wires, ?_, hi.zero⟩, ⟨e.size, e.opa, e.opb, e.wires⟩, gv⟩
    intro w' v' hh
    have hh' : ((pushGate n st 2 w 0).2.neg.setIfInBounds w ((pushGate n st 2 w 0).1 + 1))[w']? =
        some (v' + 1) := hh
    rw [Array.getElem?_setIfInBounds] at hh'
    split at hh'
    · rename_i hw
      subst hw
      split at hh'
      · simp only [Option.some.injEq, Nat.add_right_cancel_iff] at hh'
        subst hh'
        have gw := g.mono e
        refine ⟨gw.1, ?_⟩
        show Good n inp (pushGate n st 2 w 0).2 _ (!wireVal n (pushGate n st 2 w 0).2.opa (pushGate n st 2 w 0).2.opb inp w)
        rw [gw.2]
        exact gv
      · cases hh'
    · exact hi.neg w' v' hh'

theorem lit_spec {st st' : St} (h : Inv n inp decls asg st) {j w : Nat} {flip : Bool}
    (hl : lit n st j flip = .ok (w, st')) :
    Inv n inp decls asg st' ∧ Ext st st' ∧ Good n inp st' w (nodeVal decls asg j ^^ flip) := by
  unfold lit at hl
  split at hl
  · rename_i w0 hw
    have hw' : st.wires[j]? = some (w0 + 1) := by
      rw [Array.getD_eq_getD_getElem?] at hw
      cases hx : st.wires[j]? with
      | none => rw [hx] at hw; simp at hw
      | some y => rw [hx] at hw; simp at hw; rw [hw]
    have g := h.wires j w0 hw'
    cases flip with
    | false =>
        simp only [Bool.false_eq_true, if_false, Except.ok.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        exact ⟨h, Ext.refl _, by simpa using g⟩
    | true =>
        simp only [if_true, Except.ok.injEq] at hl
        have s := negate_spec h g
        rw [hl] at s
        exact ⟨s.1, s.2.1, by simpa using s.2.2⟩
  · cases hl

theorem emit2_spec {st st' : St} (h : Inv n inp decls asg st) {op a b w : Nat} {ai bi : Bool}
    (hop : op < 4) (he : emit2 n st op a ai b bi = .ok (w, st')) :
    Inv n inp decls asg st' ∧ Ext st st' ∧
      Good n inp st' w (opVal op (nodeVal decls asg a ^^ ai) (nodeVal decls asg b ^^ bi)) := by
  unfold emit2 at he
  split at he
  · cases he
  · rename_i r1 h1
    obtain ⟨i1, e1, g1⟩ := lit_spec h (show lit n st a ai = .ok (r1.1, r1.2) from h1)
    split at he
    · cases he
    · rename_i r2 h2
      obtain ⟨i2, e2, g2⟩ := lit_spec i1 (show lit n r1.2 b bi = .ok (r2.1, r2.2) from h2)
      simp only [Except.ok.injEq] at he
      have gp := pushGate_good i2 hop (g1.mono e2) g2
      have ip := pushGate_inv i2 op r1.1 r2.1
      have ep := pushGate_ext (n := n) i2.sz op r1.1 r2.1
      rw [he] at gp ip ep
      exact ⟨ip, (e1.trans e2).trans ep, gp⟩

theorem emitCarry_spec {st st' : St} (h : Inv n inp decls asg st) {a x c w : Nat} {ai xi ci : Bool}
    (he : emitCarry n st a ai x xi c ci = .ok (w, st')) :
    Inv n inp decls asg st' ∧ Ext st st' ∧
      Good n inp st' w (!((nodeVal decls asg a ^^ ai) ^^
        ((nodeVal decls asg x ^^ xi) && ((nodeVal decls asg a ^^ ai) ^^ (nodeVal decls asg c ^^ ci))))) := by
  unfold emitCarry at he
  split at he
  · cases he
  · rename_i r1 h1
    obtain ⟨i1, e1, g1⟩ := lit_spec h (show lit n st a ai = .ok (r1.1, r1.2) from h1)
    split at he
    · cases he
    · rename_i r2 h2
      obtain ⟨i2, e2, g2⟩ := lit_spec i1 (show lit n r1.2 x xi = .ok (r2.1, r2.2) from h2)
      split at he
      · cases he
      · rename_i r3 h3
        obtain ⟨i3, e3, g3⟩ := lit_spec i2 (show lit n r2.2 c ci = .ok (r3.1, r3.2) from h3)
        simp only [Except.ok.injEq] at he
        -- t = a XOR c
        have ga3 := (g1.mono e2).mono e3
        have gx3 := g2.mono e3
        have gt := pushGate_good i3 (op := 1) (by omega) ga3 g3
        have it := pushGate_inv i3 1 r1.1 r3.1
        have et := pushGate_ext (n := n) i3.sz 1 r1.1 r3.1
        -- u = x AND t
        have gu := pushGate_good it (op := 0) (by omega) (gx3.mono et) gt
        have iu := pushGate_inv it 0 r2.1 (pushGate n r3.2 1 r1.1 r3.1).1
        have eu := pushGate_ext (n := n) it.sz 0 r2.1 (pushGate n r3.2 1 r1.1 r3.1).1
        -- v = a XOR u
        have gv := pushGate_good iu (op := 1) (by omega) ((ga3.mono et).mono eu) gu
        have iv := pushGate_inv iu 1 r1.1
          (pushGate n (pushGate n r3.2 1 r1.1 r3.1).2 0 r2.1 (pushGate n r3.2 1 r1.1 r3.1).1).1
        have ev := pushGate_ext (n := n) iu.sz 1 r1.1
          (pushGate n (pushGate n r3.2 1 r1.1 r3.1).2 0 r2.1 (pushGate n r3.2 1 r1.1 r3.1).1).1
        have s := negate_spec iv gv
        rw [he] at s
        exact ⟨s.1, (((((e1.trans e2).trans e3).trans et).trans eu).trans ev).trans s.2.1, s.2.2⟩

theorem emitGate_spec {st st' : St} (dag : AIG.IsDAG BVBit decls) (h : Inv n inp decls asg st)
    {kind : UInt8} {i w : Nat} {l r : AIG.Fanin} (hi : decls[i]? = some (.gate l r))
    (he : emitGate decls kind n st l r = .ok (w, st')) :
    Inv n inp decls asg st' ∧ Ext st st' ∧ Good n inp st' w (nodeVal decls asg i) := by
  unfold emitGate at he
  split at he
  · split at he
    · rename_i a ai x xi c ci hc
      rw [carrySources_sound dag asg hi hc]
      exact emitCarry_spec h he
    · cases he
  · split at he
    · split at he
      · rename_i a ai b bi hx
        rw [xorSources_sound dag asg hi hx]
        exact emit2_spec h (op := 1) (by omega) he
      · cases he
    · rw [nodeVal_gate dag asg hi]
      exact emit2_spec h (op := 0) (by omega) he

theorem Inv.pushWire {st : St} (h : Inv n inp decls asg st) {e : Nat}
    (hg : ∀ w, e = w + 1 → Good n inp st w (nodeVal decls asg st.wires.size)) :
    Inv n inp decls asg { st with wires := st.wires.push e } where
  sz := h.sz
  wires := fun j w hj => by
    have hj' : (st.wires.push e)[j]? = some (w + 1) := hj
    rw [Array.getElem?_push] at hj'
    split at hj'
    · rename_i hjs
      simp only [Option.some.injEq] at hj'
      rw [hjs]
      exact hg w hj'
    · exact h.wires j w hj'
  neg := h.neg
  zero := h.zero

/-- What the lowering assumes about the inputs: an input bit of the graph, when its variable
and width are the declared ones, is carried by the input wire the layout assigns to it. -/
def InputsAgree (widths offs : Array Nat) (inp : Nat → Bool) (asg : BVBit → Bool) : Prop :=
  ∀ (bit : BVBit) (off : Nat), widths[bit.var]? = some bit.w → offs[bit.var]? = some off →
    asg bit = inp (off + bit.idx.val)

theorem emitNode_spec {st st' : St} {kinds : ByteArray} {widths offs : Array Nat} {i : Nat}
    (dag : AIG.IsDAG BVBit decls) (hin : InputsAgree widths offs inp asg)
    (h : Inv n inp decls asg st) (hs : st.wires.size = i)
    (he : emitNode decls kinds widths offs n i st = .ok st') :
    Inv n inp decls asg st' ∧ st'.wires.size = i + 1 := by
  unfold emitNode at he
  split at he
  · cases he
    exact ⟨h.pushWire (fun w hw => by cases hw), by simp [hs]⟩
  · split at he
    · cases he
    · rename_i hd
      split at he
      · rename_i z hz
        cases he
        refine ⟨h.pushWire (fun w hw => ?_), by simp [hs]⟩
        simp only [Nat.add_right_cancel_iff] at hw
        subst hw
        rw [hs, nodeVal_false asg hd]
        exact h.zero z hz
      · rename_i hz
        cases he
        have ip := pushGate_inv h 1 0 0
        have gz : Good n inp (pushGate n st 1 0 0).2 (pushGate n st 1 0 0).1 false :=
          ⟨by show n + st.opa.size < n + (st.opa.push _).size; simp, wireVal_push_zero h.sz⟩
        have iz : Inv n inp decls asg { (pushGate n st 1 0 0).2 with zero := (pushGate n st 1 0 0).1 + 1 } :=
          ⟨ip.sz, ip.wires, ip.neg, fun z hz' => by
            have hz'' : (pushGate n st 1 0 0).1 + 1 = z + 1 := hz'
            simp only [Nat.add_right_cancel_iff] at hz''
            rw [← hz'']; exact gz⟩
        refine ⟨iz.pushWire (fun w hw => ?_), ?_⟩
        · simp only [Nat.add_right_cancel_iff] at hw
          subst hw
          show Good n inp (pushGate n st 1 0 0).2 _ (nodeVal decls asg st.wires.size)
          rw [hs, nodeVal_false asg hd]
          exact gz
        · show (st.wires.push _).size = i + 1
          simp [hs]
    · rename_i bit hd
      split at he
      · rename_i width off hwd hoff
        split at he
        · rename_i hc
          cases he
          refine ⟨h.pushWire (fun w hw => ?_), by simp [hs]⟩
          simp only [Nat.add_right_cancel_iff] at hw
          subst hw
          rw [hs, nodeVal_atom asg hd, hin bit off (by rw [hwd, hc.1]) hoff]
          exact ⟨Nat.lt_of_lt_of_le hc.2 (Nat.le_add_right _ _), by
            rw [wireVal.eq_1]; simp only [hc.2, if_true]⟩
        · cases he
      · cases he
    · rename_i l r hd
      split at he
      · cases he
      · rename_i res hres
        cases he
        obtain ⟨ig, eg, gg⟩ := emitGate_spec dag h hd (show emitGate decls _ n st l r = .ok (res.1, res.2) from hres)
        refine ⟨ig.pushWire (fun w hw => ?_), ?_⟩
        · simp only [Nat.add_right_cancel_iff] at hw
          subst hw
          rw [eg.wires, hs]
          exact gg
        · show (res.2.wires.push _).size = i + 1
          rw [eg.wires]; simp [hs]

theorem emitAll_spec {kinds : ByteArray} {widths offs : Array Nat}
    (dag : AIG.IsDAG BVBit decls) (hin : InputsAgree widths offs inp asg) :
    ∀ (m i : Nat) (st st' : St), decls.size - i = m → Inv n inp decls asg st → st.wires.size = i →
      emitAll decls kinds widths offs n i st = .ok st' → Inv n inp decls asg st' := by
  intro m
  induction m with
  | zero =>
      intro i st st' hm h _ he
      rw [emitAll, if_neg (by omega)] at he
      cases he
      exact h
  | succ m ih =>
      intro i st st' hm h hs he
      rw [emitAll, if_pos (by omega)] at he
      split at he
      · cases he
      · rename_i st1 h1
        obtain ⟨i1, s1⟩ := emitNode_spec dag hin h hs h1
        exact ih (i + 1) st1 st' (by omega) i1 s1 he

/-- Wires collected so far are those of the first outputs. -/
def OutsGood (decls : Decls) (asg : BVBit → Bool) (outs : Array (Nat × Bool)) (st : St) (acc : Array Nat) : Prop :=
  ∀ (j w : Nat) (o : Nat × Bool), acc[j]? = some w → outs[j]? = some o →
    Good n inp st w (nodeVal decls asg o.1 ^^ o.2)

theorem emitOutputs_spec (outs : Array (Nat × Bool)) :
    ∀ (m k : Nat) (st st' : St) (acc acc' : Array Nat), outs.size - k = m → k ≤ outs.size →
      Inv n inp decls asg st → acc.size = k → OutsGood (n := n) (inp := inp) decls asg outs st acc →
      emitOutputs n outs k st acc = .ok (st', acc') →
      acc'.size = outs.size ∧ OutsGood (n := n) (inp := inp) decls asg outs st' acc' := by
  intro m
  induction m with
  | zero =>
      intro k st st' acc acc' hm hk _ hs hg he
      rw [emitOutputs, dif_neg (by omega)] at he
      simp only [Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨by omega, hg⟩
  | succ m ih =>
      intro k st st' acc acc' hm hk h hs hg he
      have hlt : k < outs.size := by omega
      rw [emitOutputs, dif_pos hlt] at he
      split at he
      · cases he
      · rename_i r hr
        obtain ⟨i1, e1, g1⟩ := lit_spec h (show lit n st outs[k].1 outs[k].2 = .ok (r.1, r.2) from hr)
        refine ih (k + 1) r.2 st' (acc.push r.1) acc' (by omega) (by omega) i1 (by simp [hs]) ?_ he
        unfold OutsGood at hg ⊢
        intro j w o hj ho
        rw [Array.getElem?_push] at hj
        split at hj
        · rename_i hjs
          simp only [Option.some.injEq] at hj
          have : outs[j]? = some outs[k] := by
            rw [hjs, hs]; exact Array.getElem?_eq_getElem hlt
          rw [this] at ho
          simp only [Option.some.injEq] at ho
          rw [← hj, ← ho]
          exact g1
        · exact (hg j w o hj ho).mono e1

end Sound

/-- Every output wire of a lowered circuit carries the value of its graph reference, for
every assignment of the inputs. -/
theorem lower_sound {decls : Decls} {widths : Array Nat} {outs : Array (Nat × Bool)} {flat : Flat}
    (dag : AIG.IsDAG BVBit decls) (h : lower decls widths outs = .ok flat)
    (inp : Nat → Bool) (asg : BVBit → Bool) (hin : InputsAgree widths (offsets widths) inp asg) :
    flat.wellFormed = true ∧ flat.inputs = totalBits widths ∧ flat.outputs.size = outs.size ∧
      ∀ (k w : Nat) (o : Nat × Bool), flat.outputs[k]? = some w → outs[k]? = some o →
        flat.eval inp w = (nodeVal decls asg o.1 ^^ o.2) := by
  unfold lower at h
  simp only at h
  split at h
  · cases h
  · rename_i st hst
    split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i hwf
        cases h
        have init : Inv (totalBits widths) inp decls asg { neg := Array.replicate (totalBits widths) 0 } :=
          ⟨rfl, fun j w hj => by simp at hj, fun w v hw => by
            have hw' : (Array.replicate (totalBits widths) 0)[w]? = some (v + 1) := hw
            rw [Array.getElem?_replicate] at hw'
            split at hw' <;> simp at hw', fun z hz => by cases hz⟩
        have i1 := emitAll_spec dag hin _ 0 _ st rfl init rfl hst
        have s := emitOutputs_spec (n := totalBits widths) (inp := inp) outs _ 0 st r.1 #[] r.2 rfl
          (Nat.zero_le _) i1 rfl (by unfold OutsGood; intro j w o hj _; simp at hj)
          (show emitOutputs _ outs 0 st #[] = .ok (r.1, r.2) from hr)
        have s2 := s.2
        unfold OutsGood at s2
        exact ⟨hwf, rfl, s.1, fun k w o hk ho => (s2 k w o hk ho).2⟩
      · cases h

/-- The same against the standard library's semantics of the graph. -/
theorem lower_correct (aig : AIG BVBit) {widths : Array Nat} (refs : Array (AIG.Ref aig)) {flat : Flat}
    (h : lower aig.decls widths (refs.map fun r => (r.gate, r.invert)) = .ok flat)
    (inp : Nat → Bool) (asg : BVBit → Bool) (hin : InputsAgree widths (offsets widths) inp asg) :
    flat.outputs.size = refs.size ∧
      ∀ (k w : Nat) (hk : k < refs.size), flat.outputs[k]? = some w →
        flat.eval inp w = ⟦aig, refs[k], asg⟧ := by
  obtain ⟨_, _, hsize, hval⟩ := lower_sound aig.hdag h inp asg hin
  refine ⟨by simpa using hsize, fun k w hk hw => ?_⟩
  rw [hval k w (refs[k].gate, refs[k].invert) hw (by simp [Array.getElem?_eq_getElem hk]),
    nodeVal_eq_denote aig asg refs[k].gate refs[k].hgate]
  simp [AIG.denote]

/-- Lower a bit-vector expression; output `k` of the gate list is bit `sel[k]` of the value. -/
def lowerExpr (expr : BVExpr w) (widths : Array Nat) (sel : Array (Fin w)) : Except String Flat :=
  let circuit := AigExport.compile expr
  let outs := sel.map fun i => ((circuit.vec.get i.val i.isLt).gate, (circuit.vec.get i.val i.isLt).invert)
  lower circuit.aig.decls widths outs

/-- From the bit-vector expression to the gate list: if input wire `offsets[v] + b` carries
bit `b` of variable `v` for every declared variable, output `k` carries bit `sel[k]` of the
expression's value. -/
theorem lowerExpr_correct (expr : BVExpr w) (widths : Array Nat) (sel : Array (Fin w)) (flat : Flat)
    (h : lowerExpr expr widths sel = .ok flat) (assign : BVExpr.Assignment) (inp : Nat → Bool)
    (hin : ∀ (v off b : Nat) (width : Nat), widths[v]? = some width → (offsets widths)[v]? = some off →
      b < width → inp (off + b) = (assign.get v).bv.getLsbD b) :
    flat.outputs.size = sel.size ∧
      ∀ (k out : Nat) (hk : k < sel.size), flat.outputs[k]? = some out →
        flat.eval inp out = (expr.eval assign).getLsbD sel[k].val := by
  let circuit := AigExport.compile expr
  let refs : Array (AIG.Ref circuit.aig) := sel.map fun i => circuit.vec.get i.val i.isLt
  have h' : lower circuit.aig.decls widths (refs.map fun r => (r.gate, r.invert)) = .ok flat := by
    rw [← h]; simp [lowerExpr, refs, circuit, Array.map_map, Function.comp_def]
  have agree : InputsAgree widths (offsets widths) inp (fun bit => (assign.get bit.var).bv.getLsbD bit.idx.val) := by
    intro bit off hw ho
    exact (hin bit.var off bit.idx.val bit.w hw ho bit.idx.isLt).symm
  obtain ⟨hsize, hval⟩ := lower_correct circuit.aig refs h' inp _ agree
  refine ⟨by simpa [refs] using hsize, fun k out hk hout => ?_⟩
  rw [hval k out (by simpa [refs] using hk) hout]
  have : refs[k]'(by simpa [refs] using hk) = circuit.vec.get sel[k].val sel[k].isLt := by simp [refs]
  rw [this]
  exact BVExpr.denote_bitblast AIG.empty ⟨expr, BVExpr.Cache.empty⟩ assign
    (BVExpr.Cache.Inv_empty AIG.empty) sel[k].val sel[k].isLt

/-! ## The printed text: what the printer writes, and parsing it back (T2, proof track P3)

`printWith_render`: running the printer with a `write` that appends to a string gives
`Flat.render`. `parseFlat_render`: the parser below (the specification of a loader of
`EMP_HYBRID_BOOL_V1`: header, one `A a b` / `X a b` / `N a` line per gate, `O` and the output
wires) reads `render f` back as `f`, for every well-formed `f` (every `lower` result is one).
`lowerExpr_loaded` composes this with `lowerExpr_correct`. -/

theorem appendGate_eq (buffer : String) (c b : Nat) : appendGate buffer c b = buffer ++ gateLine c b := by
  unfold gateLine appendGate
  split <;> simp only [String.append_assoc, String.empty_append]

theorem appendOutput_eq (buffer : String) (k o : Nat) : appendOutput buffer k o = buffer ++ outputPiece k o := by
  unfold outputPiece appendOutput
  split <;> simp only [String.append_assoc, String.empty_append]

/-- The monad the theorems run the printer in: `write` appends to the state. -/
abbrev Writer := StateM String

/-- `write` for `Writer`. -/
def appendOut (s : String) : Writer Unit := modify (· ++ s)

theorem run_bind' {α β : Type} (x : Writer α) (f : α → Writer β) (s : String) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl
theorem run_pure' {α : Type} (a : α) (s : String) : (pure a : Writer α).run s = (a, s) := rfl
theorem run_appendOut (t s : String) : (appendOut t).run s = ((), s ++ t) := rfl

theorem flushPiece_run (buffer W : String) :
    (Flat.flushPiece appendOut buffer).run W =
      if buffer.utf8ByteSize ≥ 65536 then (.yield "", W ++ buffer) else (.yield buffer, W) := by
  unfold Flat.flushPiece
  split <;> rfl

theorem flushLoop (piece : Nat → String) (app : String → Nat → String) (happ : ∀ b k, app b k = b ++ piece k) :
    ∀ (L : List Nat) (b W : String),
      ((forIn (m := Writer) L b (fun k buffer => Flat.flushPiece appendOut (app buffer k))).run W).2 ++
        ((forIn (m := Writer) L b (fun k buffer => Flat.flushPiece appendOut (app buffer k))).run W).1 =
      W ++ b ++ String.join (L.map piece) := by
  intro L
  induction L with
  | nil => intro b W; simp only [List.forIn_nil, run_pure', List.map_nil, String.join, List.foldl_nil,
      String.append_empty]
  | cons k L ih =>
      intro b W
      simp only [List.forIn_cons, run_bind', List.map_cons, String.join_cons, flushPiece_run]
      by_cases hf : (app b k).utf8ByteSize ≥ 65536
      · simp only [hf, if_true]
        rw [ih, happ]
        simp only [String.append_assoc, String.empty_append]
      · simp only [hf, if_false]
        rw [ih, happ]
        simp only [String.append_assoc]

theorem range_size (n : Nat) : ([0:n] : Std.Legacy.Range).size = n := by
  simp [Std.Legacy.Range.size]

/-- **What the printer writes is `render`**: run with a `write` that appends to a string, the
printer leaves exactly `Flat.render f`. The engines' file is the concatenation of the pieces the
printer hands to `write`, in order (`Flat.print` is `printWith` in `IO`). -/
theorem printWith_render (f : Flat) : ((f.printWith appendOut).run "").2 = f.render := by
  unfold Flat.printWith Flat.render
  simp only [run_bind', run_appendOut, Std.Legacy.Range.forIn_eq_forIn_range', range_size]
  generalize hr1 : (forIn (m := Writer) (List.range' 0 f.opa.size 1) "" fun k buffer =>
    Flat.flushPiece appendOut (appendGate buffer f.opa[k]! f.opb[k]!)).run ("" ++ f.header) = r1
  have g := flushLoop (fun k => gateLine f.opa[k]! f.opb[k]!) (fun buffer k => appendGate buffer f.opa[k]! f.opb[k]!)
    (fun b k => appendGate_eq b _ _) (List.range' 0 f.opa.size) "" ("" ++ f.header)
  have o := flushLoop (fun k => outputPiece k f.outputs[k]!) (fun buffer k => appendOutput buffer k f.outputs[k]!)
    (fun b k => appendOutput_eq b _ _) (List.range' 0 f.outputs.size) (r1.1 ++ "O ") r1.2
  rw [hr1] at g
  generalize (forIn (m := Writer) (List.range' 0 f.outputs.size 1) (r1.1 ++ "O ") fun k buffer =>
    Flat.flushPiece appendOut (appendOutput buffer k f.outputs[k]!)).run r1.2 = r2 at o ⊢
  generalize String.join ((List.range' 0 f.opa.size).map fun k => gateLine f.opa[k]! f.opb[k]!) = G at g ⊢
  generalize String.join ((List.range' 0 f.outputs.size).map fun k => outputPiece k f.outputs[k]!) = O at o ⊢
  have e : r2.2 ++ (r2.1 ++ "\n") = (r2.2 ++ r2.1) ++ "\n" := by rw [String.append_assoc]
  have e2 : r1.2 ++ (r1.1 ++ "O ") = (r1.2 ++ r1.1) ++ "O " := by rw [String.append_assoc]
  rw [e, o, e2, g]
  simp only [String.empty_append, String.append_empty, String.append_assoc]

/-! ### Reading the text back -/

/-- The digits at the head of a list of characters, and the rest. -/
def splitDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if c.isDigit then (c :: (splitDigits cs).1, (splitDigits cs).2) else ([], c :: cs)

/-- A decimal number (at least one digit) at the head, and the rest. -/
def parseNat (cs : List Char) : Option (Nat × List Char) :=
  match splitDigits cs with
  | ([], _) => none
  | (ds, rest) => some (Nat.ofDigitChars 10 ds 0, rest)

/-- The characters `lit` at the head; the rest. -/
def expectLit : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | l :: ls, c :: cs => if l = c then expectLit ls cs else none
  | _ :: _, [] => none

/-- `n` gate lines: the operand arrays (`opa`, `opb`) and the rest. `N a` gives `opb = 0`. -/
def parseGates : Nat → List Char → Option (List Nat × List Nat × List Char)
  | 0, cs => some ([], [], cs)
  | n + 1, c :: ' ' :: cs =>
      if c = 'A' ∨ c = 'X' then
        match parseNat cs with
        | some (a, cs) =>
            match expectLit [' '] cs with
            | some cs =>
                match parseNat cs with
                | some (b, cs) =>
                    match expectLit ['\n'] cs with
                    | some cs =>
                        match parseGates n cs with
                        | some (as, bs, rest) => some ((4 * a + (if c = 'A' then 0 else 1)) :: as, b :: bs, rest)
                        | none => none
                    | none => none
                | none => none
            | none => none
        | none => none
      else if c = 'N' then
        match parseNat cs with
        | some (a, cs) =>
            match expectLit ['\n'] cs with
            | some cs =>
                match parseGates n cs with
                | some (as, bs, rest) => some ((4 * a + 2) :: as, 0 :: bs, rest)
                | none => none
            | none => none
        | none => none
      else none
  | _ + 1, _ => none

/-- `n` output wires, the first being output `k` (a space before each one but output 0). -/
def parseOutputs : Nat → Nat → List Char → Option (List Nat × List Char)
  | _, 0, cs => some ([], cs)
  | k, n + 1, cs =>
      match (if k = 0 then some cs else expectLit [' '] cs) with
      | some cs =>
          match parseNat cs with
          | some (o, cs) =>
              match parseOutputs (k + 1) n cs with
              | some (os, rest) => some (o :: os, rest)
              | none => none
          | none => none
      | none => none

/-- **A loader's reading of an `EMP_HYBRID_BOOL_V1` text** (as characters): the header line,
`INPUTS GATES OUTPUTS`, that many gate lines, `O` and that many output wires, end of text. -/
def parseFlat (cs : List Char) : Option Flat :=
  match expectLit "EMP_HYBRID_BOOL_V1\n".toList cs with
  | none => none
  | some cs =>
    match parseNat cs with
    | none => none
    | some (inputs, cs) =>
      match expectLit [' '] cs with
      | none => none
      | some cs =>
        match parseNat cs with
        | none => none
        | some (gates, cs) =>
          match expectLit [' '] cs with
          | none => none
          | some cs =>
            match parseNat cs with
            | none => none
            | some (outputs, cs) =>
              match expectLit ['\n'] cs with
              | none => none
              | some cs =>
                match parseGates gates cs with
                | none => none
                | some (as, bs, cs) =>
                  match expectLit ['O', ' '] cs with
                  | none => none
                  | some cs =>
                    match parseOutputs 0 outputs cs with
                    | none => none
                    | some (os, cs) =>
                      if cs = ['\n'] then some ⟨inputs, as.toArray, bs.toArray, os.toArray⟩ else none

/-- The list does not start with a digit. -/
def NoDigit (cs : List Char) : Prop := ∀ c, cs.head? = some c → c.isDigit = false

theorem splitDigits_append (ds rest : List Char) (hd : ∀ c ∈ ds, c.isDigit = true) (hr : NoDigit rest) :
    splitDigits (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil =>
      cases rest with
      | nil => rfl
      | cons c cs =>
          have := hr c rfl
          simp [splitDigits, this]
  | cons d ds ih =>
      have h1 : d.isDigit = true := hd d (by simp)
      have ih' := ih (fun c hc => hd c (by simp [hc]))
      simp only [List.cons_append, splitDigits, h1, if_true, ih']

theorem toList_toString (n : Nat) : (toString n).toList = Nat.toDigits 10 n := by
  rw [Nat.toString_eq_repr, Nat.toList_repr]

theorem parseNat_digits (n : Nat) (rest : List Char) (hr : NoDigit rest) :
    parseNat (Nat.toDigits 10 n ++ rest) = some (n, rest) := by
  unfold parseNat
  rw [splitDigits_append _ _ (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc) hr]
  cases h : Nat.toDigits 10 n with
  | nil => exact absurd h Nat.toDigits_ne_nil
  | cons d ds =>
      simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      rw [← h, Nat.ofDigitChars_ten_toDigits]

theorem expectLit_append (l rest : List Char) : expectLit l (l ++ rest) = some rest := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [expectLit, ih]

theorem noDigit_space (cs : List Char) : NoDigit (' ' :: cs) := by
  intro c h; simp only [List.head?_cons, Option.some.injEq] at h; subst h; rfl

theorem noDigit_newline (cs : List Char) : NoDigit ('\n' :: cs) := by
  intro c h; simp only [List.head?_cons, Option.some.injEq] at h; subst h; rfl

theorem lit_A : "A ".toList = ['A', ' '] := rfl
theorem lit_X : "X ".toList = ['X', ' '] := rfl
theorem lit_N : "N ".toList = ['N', ' '] := rfl
theorem lit_sp : " ".toList = [' '] := rfl
theorem lit_nl : "\n".toList = ['\n'] := rfl
theorem lit_O : "O ".toList = ['O', ' '] := rfl
theorem lit_empty : "".toList = [] := rfl

/-- A gate the printer prints and the parser reads back: AND, XOR or NOT, a NOT with operand 0. -/
def Printable (c b : Nat) : Prop := c % 4 < 3 ∧ (c % 4 = 2 → b = 0)

theorem gateLine_A (c b : Nat) (h : c % 4 = 0) :
    (gateLine c b).toList = 'A' :: ' ' :: (Nat.toDigits 10 (c / 4) ++ ' ' :: (Nat.toDigits 10 b ++ ['\n'])) := by
  unfold gateLine appendGate
  rw [h]
  simp only [String.toList_append, toList_toString, lit_A, lit_sp, lit_nl, lit_empty, List.nil_append,
    List.append_assoc, List.cons_append]

theorem gateLine_X (c b : Nat) (h : c % 4 = 1) :
    (gateLine c b).toList = 'X' :: ' ' :: (Nat.toDigits 10 (c / 4) ++ ' ' :: (Nat.toDigits 10 b ++ ['\n'])) := by
  unfold gateLine appendGate
  rw [h]
  simp only [String.toList_append, toList_toString, lit_X, lit_sp, lit_nl, lit_empty, List.nil_append,
    List.append_assoc, List.cons_append]

theorem gateLine_N (c b : Nat) (h : c % 4 = 2) :
    (gateLine c b).toList = 'N' :: ' ' :: (Nat.toDigits 10 (c / 4) ++ ['\n']) := by
  unfold gateLine appendGate
  rw [h]
  simp only [String.toList_append, toList_toString, lit_N, lit_nl, lit_empty, List.nil_append,
    List.append_assoc, List.cons_append]

theorem parseGates_lines (A B : Nat → Nat) (rest : List Char) :
    ∀ (n s : Nat), (∀ k, s ≤ k → k < s + n → Printable (A k) (B k)) →
      parseGates n ((String.join ((List.range' s n).map fun k => gateLine (A k) (B k))).toList ++ rest) =
        some ((List.range' s n).map A, (List.range' s n).map B, rest) := by
  intro n
  induction n with
  | zero => intro s _; rfl
  | succ n ih =>
      intro s hp
      have hs := hp s (Nat.le_refl _) (by omega)
      have ih' := ih (s + 1) (fun k h1 h2 => hp k (by omega) (by omega))
      rw [List.range'_succ, List.map_cons, String.join_cons, String.toList_append, List.map_cons, List.map_cons]
      generalize (String.join ((List.range' (s + 1) n).map fun k => gateLine (A k) (B k))).toList = T at ih' ⊢
      have h3 := hs.1
      by_cases e0 : A s % 4 = 0
      · rw [gateLine_A _ _ e0]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        simp only [parseGates, true_or, if_true]
        rw [parseNat_digits _ _ (noDigit_space _)]
        simp only [expectLit, if_true]
        rw [parseNat_digits _ _ (noDigit_newline _)]
        simp only [expectLit, if_true]
        rw [ih']
        simp only [if_true, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true]
        omega
      · by_cases e1 : A s % 4 = 1
        · rw [gateLine_X _ _ e1]
          simp only [List.append_assoc, List.cons_append, List.nil_append]
          simp only [parseGates, or_true, if_true]
          rw [parseNat_digits _ _ (noDigit_space _)]
          simp only [expectLit, if_true]
          rw [parseNat_digits _ _ (noDigit_newline _)]
          simp only [expectLit, if_true]
          rw [ih']
          simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true]
          simp only [show ('X' = 'A') = False from by decide, if_false]
          omega
        · have e2 : A s % 4 = 2 := by omega
          rw [gateLine_N _ _ e2]
          simp only [List.append_assoc, List.cons_append, List.nil_append]
          simp only [parseGates, show ('N' = 'A') = False from by decide, show ('N' = 'X') = False from by decide,
            or_self, if_false, if_true]
          rw [parseNat_digits _ _ (noDigit_newline _)]
          simp only [expectLit, if_true]
          rw [ih']
          simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true]
          exact ⟨by omega, (hs.2 e2).symm⟩

theorem outputPiece_chars (k o : Nat) :
    (outputPiece k o).toList = (if k = 0 then [] else [' ']) ++ Nat.toDigits 10 o := by
  unfold outputPiece appendOutput
  by_cases hk : k = 0
  · simp only [hk, beq_self_eq_true, if_true, String.toList_append, toList_toString, lit_empty, List.nil_append]
  · simp only [hk, beq_iff_eq, if_false, String.toList_append, toList_toString, lit_empty, lit_sp, List.nil_append]

theorem noDigit_pieces (O : Nat → Nat) (rest : List Char) (n s : Nat) (hs : s ≠ 0) :
    NoDigit ((String.join ((List.range' s n).map fun k => outputPiece k (O k))).toList ++ '\n' :: rest) := by
  cases n with
  | zero => exact noDigit_newline rest
  | succ n =>
      rw [List.range'_succ, List.map_cons, String.join_cons, String.toList_append, outputPiece_chars, if_neg hs]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      exact noDigit_space _

theorem parseOutputs_pieces (O : Nat → Nat) (rest : List Char) :
    ∀ (n s : Nat), parseOutputs s n
        ((String.join ((List.range' s n).map fun k => outputPiece k (O k))).toList ++ '\n' :: rest) =
      some ((List.range' s n).map O, '\n' :: rest) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      have hnd := noDigit_pieces O rest n (s + 1) (by omega)
      have tail := ih (s + 1)
      rw [List.range'_succ, List.map_cons, String.join_cons, String.toList_append, outputPiece_chars, List.map_cons]
      generalize (String.join ((List.range' (s + 1) n).map fun k => outputPiece k (O k))).toList = T at hnd tail ⊢
      by_cases hs : s = 0
      · simp only [parseOutputs, hs, if_true, List.nil_append, List.append_assoc]
        rw [parseNat_digits _ _ hnd]
        simp only
        rw [← hs, tail]
      · simp only [parseOutputs, hs, if_false, List.append_assoc, List.cons_append, List.nil_append, expectLit,
          if_true]
        rw [parseNat_digits _ _ hnd]
        simp only
        rw [tail]

theorem map_range_getElem! (a : Array Nat) : (List.range' 0 a.size).map (fun k => a[k]!) = a.toList := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul, Array.getElem_toList]
    simp only [List.length_map, List.length_range'] at h1
    exact getElem!_pos a i h1

/-- **The parser reads the printed text back.** For every well-formed gate list (every result of
`lower` is one: `lower_sound`), parsing `render f` gives `f`. -/
theorem parseFlat_render (f : Flat) (hwf : f.wellFormed = true) : parseFlat f.render.toList = some f := by
  simp only [Flat.wellFormed, Bool.and_eq_true, beq_iff_eq] at hwf
  obtain ⟨⟨hsz, hok⟩, _⟩ := hwf
  have gates_ok : ∀ m, gatesOk f m = true → ∀ k, k < m → gateOk f k = true := by
    intro m
    induction m with
    | zero => intro _ k hk; omega
    | succ m ih =>
        intro h k hk
        simp only [gatesOk, Bool.and_eq_true] at h
        rcases Nat.lt_or_ge k m with lt | ge
        · exact ih h.2 k lt
        · have : k = m := by omega
          subst this; exact h.1
  have hp : ∀ k, 0 ≤ k → k < 0 + f.opa.size → Printable f.opa[k]! f.opb[k]! := by
    intro k _ hk
    have g := gates_ok _ hok k (by omega)
    unfold gateOk at g
    rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)] at g
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at g
    rw [getElem!_pos f.opa k (by omega), getElem!_pos f.opb k (by omega)]
    refine ⟨g.1.2, fun h2 => ?_⟩
    rcases g.2 with h | h
    · exact absurd h2 h
    · exact h
  have hg := parseGates_lines (fun k => f.opa[k]!) (fun k => f.opb[k]!)
    ('O' :: ' ' :: ((String.join ((List.range' 0 f.outputs.size).map fun k => outputPiece k f.outputs[k]!)).toList ++
      ['\n'])) f.opa.size 0 hp
  have ho := parseOutputs_pieces (fun k => f.outputs[k]!) [] f.outputs.size 0
  unfold Flat.render Flat.header parseFlat
  simp only [String.toList_append, toList_toString, lit_sp, lit_nl, lit_O, List.append_assoc,
    List.cons_append, List.nil_append]
  rw [expectLit_append]
  simp only
  rw [parseNat_digits _ _ (noDigit_space _)]
  simp only [expectLit, if_true]
  rw [parseNat_digits _ _ (noDigit_space _)]
  simp only [expectLit, if_true]
  rw [parseNat_digits _ _ (noDigit_newline _)]
  simp only [expectLit, if_true]
  rw [hg]
  simp only [expectLit, if_true]
  rw [ho]
  simp only [if_true, Option.some.injEq]
  rw [map_range_getElem!, ← hsz, map_range_getElem!, map_range_getElem!]

/-- A sample: the text of a three-gate list is the `EMP_HYBRID_BOOL_V1` format as the engines
have always read it (`A`/`X` lines with two operands, `N` with one, `O` and the outputs). -/
theorem render_sample :
    Flat.render ⟨2, #[0, 5, 10], #[1, 2, 0], #[3, 4]⟩ = "EMP_HYBRID_BOOL_V1\n2 3 2\nA 0 1\nX 1 2\nN 2\nO 3 4\n" := by
  decide

theorem render_sample_empty :
    Flat.render ⟨0, #[], #[], #[]⟩ = "EMP_HYBRID_BOOL_V1\n0 0 0\nO \n" := by
  decide

/-- **What the engines load is the lowered circuit.** If `lowerExpr` returns `flat`, the text the
printer writes (`printWith`, which `Flat.print` runs in `IO`) parses back to exactly `flat`, and
output `k` of that gate list carries bit `sel[k]` of the expression's value on every input
assignment (`lowerExpr_correct`). What stays trusted: that the engine's loader reads the text as
`parseFlat` does and evaluates gates as `Flat.eval` does (`Flat.run_eq_eval` for one-pass
evaluation), and the binding of input wires to variables (`hin`). -/
theorem lowerExpr_loaded (expr : BVExpr w) (widths : Array Nat) (sel : Array (Fin w)) (flat : Flat)
    (h : lowerExpr expr widths sel = .ok flat) :
    parseFlat ((flat.printWith appendOut).run "").2.toList = some flat ∧ flat.outputs.size = sel.size ∧
      ∀ (assign : BVExpr.Assignment) (inp : Nat → Bool),
        (∀ (v off b : Nat) (width : Nat), widths[v]? = some width → (offsets widths)[v]? = some off →
          b < width → inp (off + b) = (assign.get v).bv.getLsbD b) →
        ∀ (k out : Nat) (hk : k < sel.size), flat.outputs[k]? = some out →
          flat.eval inp out = (expr.eval assign).getLsbD sel[k].val := by
  have ls := lower_sound (AigExport.compile expr).aig.hdag h (fun _ => false) (fun _ => false)
    (fun _ _ _ _ => rfl)
  refine ⟨by rw [printWith_render]; exact parseFlat_render flat ls.1, by simpa using ls.2.2.1, ?_⟩
  · intro assign inp hin
    exact (lowerExpr_correct expr widths sel flat h assign inp hin).2

#print axioms printWith_render
#print axioms parseFlat_render
#print axioms lowerExpr_loaded
#print axioms render_sample
#print axioms lower_sound
#print axioms lower_correct
#print axioms lowerExpr_correct
#print axioms Flat.run_eq_eval
#print axioms offsets_getElem?

end TlsMpc.FlatLowering
