import TlsMpc.Node.Flows.CurveCompiled
import TlsMpc.Node.Flows.CurveLive
import TlsMpc.Node.Flows.CurveRunB

/-!
# The curve programs compute their declarations and are live on honest inputs (PROOF_GAPS F22a)

Stage S11. The honest-run theorems (`CurveRun*.lean`) take, per program, `ComputesD` (every
returning evaluation gives the program's function) and `Live` (nonzero masks never abort on the
input). This file discharges both for every curve program the S11 flows run, from

  * the loader's facts (`LoadedAs`: the program under the name is the V3 program of its
    declaration `FieldProgramsV3.find name`, with the mask count the shell checks, F25c);
  * `FieldProgramsV3.Decl.values` (`FieldDagV3.eval_compileAll`) for `ComputesD`
    (`computesD_of_decl`; the output counts by `decide` on the declarations' list spines);
  * `Compiled.Decl.live` (every node of an accepted compilation is a subterm of the source, so the
    compiled denominators are the source's) for `Live`, with the source condition `DivOk` proved
    here from the programs' own definitions;
  * named hypotheses for the group facts, each a theorem of `proofs/` (SecurityMathlib section 7):
      - `CompleteAddition` (`CurveLive`): the `y` denominator `1 − d·x₁x₂y₁y₂ ≠ 0` on curve points,
        `edwards_complete`; the `x` denominator follows by negating a point (`den_x_ne`);
      - `AddClosed`: `pointAddValue` of curve points is a curve point, `pointAddValue_is_group_add`
        with `curveCheck_zero_iff` (`Affine` ⇔ the scaled curve equation);
      - `ExtClosed`: `extAddValue` of represented points represents a point (and its `Z ≠ 0`),
        `extAddValue_is_group_add` (`ExtGood` is `ExtRep` written in field elements);
      - `RecipientOnCurve`: `recipient`'s point is on the curve when its check is zero,
        `recipient_on_curve`.

THE INPUT CONDITION PER PROGRAM (what makes it live; the masks are any nonzero values):
  * mask-free programs (`x25519-fast`, `edwards-on-curve`, `edwards-add-u`, `lift-open`,
    `edwards-offset-sum-fast`, `edwards-bit-sum`, `edwards-affine-bit-sum`): none
    (`computes_of_find`: they compute their expressions on every input, `Conv.Computes`);
  * `edwards-offset-sum` (`OffsetSumIn`): the initial point and the 64 signed window points are
    curve points, and the sum's `y ≠ 1` (the agreement point is not the neutral element);
  * `edwards-torsion-hinted` (`TorsionIn`): the two hint points are curve points;
  * `edwards-signature-sum` (`SignatureIn`): `flip` and the 509 selection bits are bits, the 509
    table entries represent curve points;
  * `lift-point` (`LiftPointIn`): the two mask points and the selected point are curve points,
    `1 + valid·u ≠ 0`;
  * `edwards-bit-table` (`BitTableIn`): the point and the 2·63 hint points are curve points;
  * `edwards-prepare-hinted` (`PrepareHintedIn`): the same, and the 504 scalar bits are bits;
  * `edwards-prepare` (`PrepareIn`): `u + 1 ≠ 0`, `121666 − 121665·y² ≠ 0`, `2·x² ≠ 0` for the
    recipient's `y = (u − 1)/(u + 1)` and `x²`, the recipient's check is zero (u valid), and the
    504 scalar bits are bits.
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.FieldDag (F ofNat inverse Expr)
open TlsMpc.FieldDag.Compiled (DivOk divOk_bin)
open TlsMpc.FieldDag.V3 (FieldInverse Program)
open TlsMpc.Node.Local.Edwards (curveValue)

/-! ## Named hypotheses (theorems of `proofs/`) -/

/-- **Closure** (named hypothesis; `proofs/` `pointAddValue_is_group_add` with
`curveCheck_zero_iff`): the affine addition of two curve points is a curve point. -/
def AddClosed : Prop :=
  ∀ p q : TlsMpc.EdwardsAffine.Value, curveValue p = 0 → curveValue q = 0 →
    curveValue (TlsMpc.EdwardsAffine.pointAddValue p q) = 0

/-- Extended coordinates of a curve point (`proofs/` `ExtRep` in field elements): `Z ≠ 0`, the
affine point `(X/Z, Y/Z)` on the curve, `T = XY/Z`. -/
structure ExtGood (e : TlsMpc.EdwardsHinted.ExtV) : Prop where
  z_ne : e.z ≠ 0
  on : curveValue (TlsMpc.EdwardsHinted.toAffineValue e) = 0
  t_eq : e.t = e.x * e.y * inverse e.z

/-- **Closure in extended coordinates** (named hypothesis; `proofs/` `extAddValue_is_group_add`):
the unified addition of two represented points represents their sum (in particular `Z ≠ 0`). -/
def ExtClosed : Prop :=
  ∀ p q : TlsMpc.EdwardsHinted.ExtV, ExtGood p → ExtGood q → ExtGood (TlsMpc.EdwardsHinted.extAddValue p q)

/-- **The recipient's point is on the curve when its check is zero** (named hypothesis; `proofs/`
`recipient_on_curve`, with `curveCheck_zero_iff`). -/
def RecipientOnCurve : Prop :=
  ∀ input : Nat → F, (TlsMpc.EdwardsAffine.recipient (.input 0)).2.eval input = ofNat 0 →
    curveValue (TlsMpc.EdwardsAffine.evalPoint input (TlsMpc.EdwardsAffine.recipient (.input 0)).1) = 0

namespace PL

abbrev Pt := TlsMpc.EdwardsAffine.Point
abbrev Ex := TlsMpc.EdwardsHinted.ExtE
abbrev Val := TlsMpc.EdwardsAffine.Value
abbrev EV := TlsMpc.EdwardsHinted.ExtV

/-! ## Field facts -/

theorem zero_eq : (ofNat 0 : F) = 0 := rfl

theorem inverse_one : inverse (ofNat 1) = ofNat 1 := power_one_base _

theorem mul_one' (x : F) : x * ofNat 1 = x := by rw [one_eq]; grind

theorem curveValue_neg (x y : F) : curveValue (ofNat 0 - x, y) = curveValue (x, y) := by
  simp only [curveValue, zero_eq]
  grind

theorem curveValue_scale (c x y : F) (hc : c * c = ofNat 1) : curveValue (c * x, y) = curveValue (x, y) := by
  rw [one_eq] at hc
  simp only [curveValue]
  have e : c * x * (c * x) = x * x := by
    calc c * x * (c * x) = (c * c) * (x * x) := by grind
      _ = x * x := by rw [hc]; grind
  rw [e]

theorem neutral_curve : curveValue (ofNat 0, ofNat 1) = 0 := by decide

theorem zero_mul' (x : F) : ofNat 0 * x = ofNat 0 := by rw [zero_eq]; grind

theorem one_mul' (x : F) : ofNat 1 * x = x := by rw [one_eq]; grind

theorem one_add_zero : (ofNat 1 : F) + ofNat 0 = ofNat 1 := by decide

theorem one_add_sub_one (y : F) : ofNat 1 + (y - ofNat 1) = y := by rw [one_eq]; grind

theorem one_add_zero_mul (y : F) : ofNat 1 + ofNat 0 * y = ofNat 1 := by rw [zero_mul', one_add_zero]

theorem one_add_one_mul_sub (y : F) : ofNat 1 + ofNat 1 * (y - ofNat 1) = y := by rw [one_mul', one_add_sub_one]

/-- The `x` denominator of the scaled addition, from `CompleteAddition` on `(−x₁, y₁)`. -/
theorem den_x_ne (hinv : FieldInverse) (hC : CompleteAddition) (p q : Val) (hp : curveValue p = 0)
    (hq : curveValue q = 0) : ofNat 121666 - ofNat 121665 * (p.1 * q.1 * (p.2 * q.2)) ≠ 0 := by
  have hp' : curveValue (ofNat 0 - p.1, p.2) = 0 := by rw [curveValue_neg]; exact hp
  have h := addU_den_ne_zero hinv hC _ _ q.1 q.2 hp' hq
  have e : ofNat 121666 - ofNat 121665 * (p.1 * q.1 * (p.2 * q.2)) =
      ofNat 121666 + ofNat 121665 * ((ofNat 0 - p.1) * q.1 * (p.2 * q.2)) := by
    rw [zero_eq]
    grind
  rw [e]
  exact h

theorem den_y_ne (hinv : FieldInverse) (hC : CompleteAddition) (p q : Val) (hp : curveValue p = 0)
    (hq : curveValue q = 0) : ofNat 121666 + ofNat 121665 * (p.1 * q.1 * (p.2 * q.2)) ≠ 0 :=
  addU_den_ne_zero hinv hC p.1 p.2 q.1 q.2 hp hq

/-! ## `DivOk` of the expression builders -/

theorem dk_mul {input : Nat → F} {a b : Expr} (ha : DivOk input a) (hb : DivOk input b) :
    DivOk input (TlsMpc.EdwardsAffine.mul a b) := divOk_bin.mpr ⟨ha, hb, fun h => by cases h⟩

theorem dk_add {input : Nat → F} {a b : Expr} (ha : DivOk input a) (hb : DivOk input b) :
    DivOk input (TlsMpc.EdwardsAffine.add a b) := divOk_bin.mpr ⟨ha, hb, fun h => by cases h⟩

theorem dk_sub {input : Nat → F} {a b : Expr} (ha : DivOk input a) (hb : DivOk input b) :
    DivOk input (TlsMpc.EdwardsAffine.sub a b) := divOk_bin.mpr ⟨ha, hb, fun h => by cases h⟩

theorem dk_div {input : Nat → F} {a b : Expr} (ha : DivOk input a) (hb : DivOk input b) (hz : b.eval input ≠ 0) :
    DivOk input (TlsMpc.EdwardsAffine.div a b) := divOk_bin.mpr ⟨ha, hb, fun _ => hz⟩

theorem dk_input (input : Nat → F) (i : Nat) : DivOk input (.input i) := trivial

theorem dk_const (input : Nat → F) (n : Nat) : DivOk input (.const n) := trivial

theorem dk_bitCheck (input : Nat → F) (i : Nat) : DivOk input (TlsMpc.EdwardsAffine.bitCheck (.input i)) :=
  dk_mul (dk_input _ _) (dk_sub (dk_input _ _) (dk_const _ _))

/-! ## Affine points -/

/-- A point expression whose divisions are nonzero and whose value is a curve point. -/
structure PtOk (input : Nat → F) (p : Pt) : Prop where
  d1 : DivOk input p.1
  d2 : DivOk input p.2
  on : curveValue (TlsMpc.EdwardsAffine.evalPoint input p) = 0

theorem inputPoint_ok (input : Nat → F) (i : Nat) (h : curveValue (input i, input (i + 1)) = 0) :
    PtOk input (TlsMpc.EdwardsAffine.inputPoint i) := ⟨dk_input _ _, dk_input _ _, h⟩

theorem neutralPt_ok (input : Nat → F) : PtOk input (.const 0, .const 1) :=
  ⟨dk_const _ _, dk_const _ _, neutral_curve⟩

theorem negate_ok {input : Nat → F} {p : Pt} (hp : PtOk input p) : PtOk input (TlsMpc.EdwardsHinted.negate p) :=
  ⟨dk_sub (dk_const _ _) hp.d1, hp.d2, by
    show curveValue (ofNat 0 - p.1.eval input, p.2.eval input) = 0
    rw [curveValue_neg]
    exact hp.on⟩

theorem pointAdd_fst (p q : Pt) :
    (TlsMpc.EdwardsAffine.pointAdd p q).1 = TlsMpc.EdwardsAffine.div
      (TlsMpc.EdwardsAffine.mul (.const 121666) (TlsMpc.EdwardsAffine.add (TlsMpc.EdwardsAffine.mul p.1 q.2) (TlsMpc.EdwardsAffine.mul p.2 q.1)))
      (TlsMpc.EdwardsAffine.sub (.const 121666) (TlsMpc.EdwardsAffine.mul (.const 121665)
        (TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsAffine.mul p.1 q.1) (TlsMpc.EdwardsAffine.mul p.2 q.2)))) := rfl

theorem pointAdd_snd (p q : Pt) :
    (TlsMpc.EdwardsAffine.pointAdd p q).2 = TlsMpc.EdwardsAffine.div
      (TlsMpc.EdwardsAffine.mul (.const 121666) (TlsMpc.EdwardsAffine.add (TlsMpc.EdwardsAffine.mul p.2 q.2) (TlsMpc.EdwardsAffine.mul p.1 q.1)))
      (TlsMpc.EdwardsAffine.add (.const 121666) (TlsMpc.EdwardsAffine.mul (.const 121665)
        (TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsAffine.mul p.1 q.1) (TlsMpc.EdwardsAffine.mul p.2 q.2)))) := rfl

theorem den_x_eval (input : Nat → F) (p q : Pt) :
    (TlsMpc.EdwardsAffine.sub (.const 121666) (TlsMpc.EdwardsAffine.mul (.const 121665)
      (TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsAffine.mul p.1 q.1) (TlsMpc.EdwardsAffine.mul p.2 q.2)))).eval input =
    ofNat 121666 - ofNat 121665 * (p.1.eval input * q.1.eval input * (p.2.eval input * q.2.eval input)) := rfl

theorem den_y_eval (input : Nat → F) (p q : Pt) :
    (TlsMpc.EdwardsAffine.add (.const 121666) (TlsMpc.EdwardsAffine.mul (.const 121665)
      (TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsAffine.mul p.1 q.1) (TlsMpc.EdwardsAffine.mul p.2 q.2)))).eval input =
    ofNat 121666 + ofNat 121665 * (p.1.eval input * q.1.eval input * (p.2.eval input * q.2.eval input)) := rfl

/-- **The addition of two good points is good** (`CompleteAddition`, `AddClosed`). -/
theorem pointAdd_ok (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed) {input : Nat → F} {p q : Pt}
    (hp : PtOk input p) (hq : PtOk input q) : PtOk input (TlsMpc.EdwardsAffine.pointAdd p q) := by
  have hx := den_x_ne hinv hC (p.1.eval input, p.2.eval input) (q.1.eval input, q.2.eval input) hp.on hq.on
  have hy := den_y_ne hinv hC (p.1.eval input, p.2.eval input) (q.1.eval input, q.2.eval input) hp.on hq.on
  rw [← den_x_eval] at hx
  rw [← den_y_eval] at hy
  refine ⟨?_, ?_, ?_⟩
  rotate_left 2
  · rw [TlsMpc.EdwardsAffine.pointAdd_eval]
    exact hA _ _ hp.on hq.on
  · rw [pointAdd_fst]
    exact dk_div (dk_mul (dk_const _ _) (dk_add (dk_mul hp.d1 hq.d2) (dk_mul hp.d2 hq.d1)))
      (dk_sub (dk_const _ _) (dk_mul (dk_const _ _) (dk_mul (dk_mul hp.d1 hq.d1) (dk_mul hp.d2 hq.d2)))) hx
  · rw [pointAdd_snd]
    exact dk_div (dk_mul (dk_const _ _) (dk_add (dk_mul hp.d2 hq.d2) (dk_mul hp.d1 hq.d1)))
      (dk_add (dk_const _ _) (dk_mul (dk_const _ _) (dk_mul (dk_mul hp.d1 hq.d1) (dk_mul hp.d2 hq.d2)))) hy

/-! ## Lists, folds, balanced sums -/

theorem pairUp_ok {α : Type} (P : α → Prop) (f : α → α → α) (hf : ∀ a b, P a → P b → P (f a b)) :
    ∀ l : List α, (∀ x ∈ l, P x) → ∀ x ∈ TlsMpc.EdwardsAffine.pairUp f l, P x
  | [], h => fun x hx => h x hx
  | [a], h => fun x hx => h x hx
  | a :: b :: rest, h => by
    intro x hx
    simp only [TlsMpc.EdwardsAffine.pairUp, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hf a b (h a (by simp)) (h b (by simp))
    · exact pairUp_ok P f hf rest (fun y hy => h y (by simp [hy])) x hx

theorem reduce_ok {α : Type} (P : α → Prop) (f : α → α → α) (hf : ∀ a b, P a → P b → P (f a b)) :
    ∀ (n : Nat) (l : List α), (∀ x ∈ l, P x) → ∀ x ∈ TlsMpc.EdwardsAffine.reduce f n l, P x
  | 0, _, h => h
  | n + 1, l, h => reduce_ok P f hf n _ (pairUp_ok P f hf l h)

theorem head_ok {α : Type} (P : α → Prop) (l : List α) (d : α) (h : ∀ x ∈ l, P x) (hd : P d) :
    P (l.head?.getD d) := by
  cases hh : l.head? with
  | none => exact hd
  | some x => exact h x (List.mem_of_mem_head? hh)

theorem foldl_inv {α β : Type} (P : α → Prop) (g : α → β → α) (hg : ∀ a b, P a → P (g a b)) :
    ∀ (l : List β) (a : α), P a → P (l.foldl g a)
  | [], _, h => h
  | b :: l, a, h => foldl_inv P g hg l (g a b) (hg a b h)

theorem getD_ok {α : Type} (P : α → Prop) {l : List α} {d : α} (h : ∀ x ∈ l, P x) (hd : P d) (k : Nat) :
    P (l.getD k d) := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => exact hd
  | some x => exact h x (List.mem_of_getElem? hk)

theorem sumTree_ok (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed) {input : Nat → F}
    (pts : List Pt) (h : ∀ p ∈ pts, PtOk input p) : PtOk input (TlsMpc.EdwardsAffine.sumTree pts) :=
  head_ok (PtOk input) _ _
    (reduce_ok (PtOk input) TlsMpc.EdwardsAffine.pointAdd (fun _ _ ha hb => pointAdd_ok hinv hC hA ha hb) _ pts h)
    (neutralPt_ok input)

theorem bitEntry_ok {input : Nat → F} {entries : List Pt} (h : ∀ p ∈ entries, PtOk input p) (i : Nat) :
    PtOk input (TlsMpc.EdwardsAffine.bitEntry entries i) :=
  getD_ok (PtOk input) h (neutralPt_ok input) _

/-- A value that is 0 or 1. -/
def IsBit (v : F) : Prop := v = ofNat 0 ∨ v = ofNat 1

theorem choose_ok {input : Nat → F} (k : Nat) {p : Pt} (hp : PtOk input p) (hb : IsBit (input k)) :
    PtOk input (TlsMpc.EdwardsAffine.choose (.input k) p) :=
  ⟨dk_mul (dk_input _ _) hp.d1, dk_add (dk_const _ _) (dk_mul (dk_input _ _) (dk_sub hp.d2 (dk_const _ _))), by
    show curveValue (input k * p.1.eval input, ofNat 1 + input k * (p.2.eval input - ofNat 1)) = 0
    rcases hb with h | h
    · rw [h, zero_mul', one_add_zero_mul]
      exact neutral_curve
    · rw [h, one_mul', one_add_one_mul_sub]
      exact hp.on⟩

/-! ## Windows and the table of `EdwardsAffine` -/

theorem window_ok (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed) {input : Nat → F} (b : Pt)
    (hb : PtOk input b) :
    (∀ p ∈ (TlsMpc.EdwardsAffine.window b).1, PtOk input p) ∧ PtOk input (TlsMpc.EdwardsAffine.window b).2 := by
  have hm : ∀ p ∈ (List.range (TlsMpc.EdwardsAffine.digits - 1)).foldl (fun (acc : List Pt) (i : Nat) =>
      acc ++ [TlsMpc.EdwardsAffine.pointAdd (acc.getD ((i + 2 + 1) / 2 - 1) b) (acc.getD ((i + 2) / 2 - 1) b)]) [b],
      PtOk input p := by
    apply foldl_inv (fun (acc : List Pt) => ∀ p ∈ acc, PtOk input p)
    · intro acc i hacc p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hacc p hp
      · rw [List.mem_singleton] at hp
        subst hp
        exact pointAdd_ok hinv hC hA (getD_ok (PtOk input) hacc hb _) (getD_ok (PtOk input) hacc hb _)
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact hb
  exact ⟨hm, pointAdd_ok hinv hC hA (getD_ok (PtOk input) hm hb _) (getD_ok (PtOk input) hm hb _)⟩

theorem table_ok (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed) {input : Nat → F} (b : Pt)
    (hb : PtOk input b) : ∀ p ∈ TlsMpc.EdwardsAffine.table b, PtOk input p := by
  have := foldl_inv (fun (st : List Pt × Pt) => (∀ p ∈ st.1, PtOk input p) ∧ PtOk input st.2)
    (fun (st : List Pt × Pt) (_ : Nat) => (st.1 ++ (TlsMpc.EdwardsAffine.window st.2).1, (TlsMpc.EdwardsAffine.window st.2).2))
    (fun st _ h => by
      obtain ⟨w1, w2⟩ := window_ok hinv hC hA st.2 h.2
      refine ⟨fun p hp => ?_, w2⟩
      rcases List.mem_append.mp hp with hp | hp
      · exact h.1 p hp
      · exact w1 p hp)
    (List.range TlsMpc.EdwardsAffine.windows) ([], b) ⟨fun p hp => by simp at hp, hb⟩
  exact this.1

/-! ## Extended points -/

/-- An extended point expression whose divisions are nonzero and whose value represents a curve
point. -/
structure ExtOk (input : Nat → F) (e : Ex) : Prop where
  dx : DivOk input e.x
  dy : DivOk input e.y
  dz : DivOk input e.z
  dt : DivOk input e.t
  good : ExtGood (TlsMpc.EdwardsHinted.evalExt input e)

theorem extAdd_ok (hX : ExtClosed) {input : Nat → F} {p q : Ex} (hp : ExtOk input p) (hq : ExtOk input q) :
    ExtOk input (TlsMpc.EdwardsHinted.extAdd p q) := by
  have ha := dk_mul (dk_sub hp.dy hp.dx) (dk_sub hq.dy hq.dx)
  have hb := dk_mul (dk_add hp.dy hp.dx) (dk_add hq.dy hq.dx)
  have hc := dk_mul (dk_const input 243330) (dk_mul hp.dt hq.dt)
  have hd := dk_mul (dk_const input 243332) (dk_mul hp.dz hq.dz)
  have he := dk_mul (dk_const input 121666) (dk_sub hb ha)
  have hh := dk_mul (dk_const input 121666) (dk_add hb ha)
  have hf := dk_add hd hc
  have hg := dk_sub hd hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact dk_mul he hf
  · exact dk_mul hg hh
  · exact dk_mul hf hg
  · exact dk_mul he hh
  · rw [TlsMpc.EdwardsHinted.extAdd_eval]
    exact hX _ _ hp.good hq.good

theorem toAffine_ofAffine (v : Val) : TlsMpc.EdwardsHinted.toAffineValue (TlsMpc.EdwardsHinted.ofAffineValue v) = v := by
  simp only [TlsMpc.EdwardsHinted.toAffineValue, TlsMpc.EdwardsHinted.ofAffineValue, inverse_one, mul_one']

theorem ofAffineValue_good (v : Val) (hv : curveValue v = 0) : ExtGood (TlsMpc.EdwardsHinted.ofAffineValue v) := by
  refine ⟨?_, by rw [toAffine_ofAffine]; exact hv, ?_⟩
  · simp only [TlsMpc.EdwardsHinted.ofAffineValue]
    decide
  · simp only [TlsMpc.EdwardsHinted.ofAffineValue, inverse_one, mul_one']

theorem ofAffine_ok {input : Nat → F} {p : Pt} (hp : PtOk input p) : ExtOk input (TlsMpc.EdwardsHinted.ofAffine p) :=
  ⟨hp.d1, hp.d2, dk_const _ _, dk_mul hp.d1 hp.d2, ofAffineValue_good _ hp.on⟩

theorem toAffine_ok {input : Nat → F} {e : Ex} (he : ExtOk input e) : PtOk input (TlsMpc.EdwardsHinted.toAffine e) :=
  ⟨dk_div he.dx he.dz he.good.z_ne, dk_div he.dy he.dz he.good.z_ne, he.good.on⟩

theorem neutralValue_good : ExtGood TlsMpc.EdwardsHinted.neutralValue := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [TlsMpc.EdwardsHinted.neutralValue]
    decide
  · simp only [TlsMpc.EdwardsHinted.toAffineValue, TlsMpc.EdwardsHinted.neutralValue, inverse_one, mul_one']
    exact neutral_curve
  · simp only [TlsMpc.EdwardsHinted.neutralValue, inverse_one, mul_one', zero_mul']

theorem neutralExt_ok (input : Nat → F) : ExtOk input TlsMpc.EdwardsHinted.neutral :=
  ⟨dk_const _ _, dk_const _ _, dk_const _ _, dk_const _ _, neutralValue_good⟩

theorem extSum_ok (hX : ExtClosed) {input : Nat → F} (pts : List Ex) (h : ∀ p ∈ pts, ExtOk input p) :
    ExtOk input (TlsMpc.EdwardsHinted.extSum pts) :=
  head_ok (ExtOk input) _ _
    (reduce_ok (ExtOk input) TlsMpc.EdwardsHinted.extAdd (fun _ _ ha hb => extAdd_ok hX ha hb) _ pts h)
    (neutralExt_ok input)

theorem ext_eq (a b : EV) (h1 : a.x = b.x) (h2 : a.y = b.y) (h3 : a.z = b.z) (h4 : a.t = b.t) : a = b := by
  cases a
  cases b
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

theorem chooseExt_ok {input : Nat → F} (k : Nat) {p : Ex} (hp : ExtOk input p) (hb : IsBit (input k)) :
    ExtOk input (TlsMpc.EdwardsHinted.chooseExt (.input k) p) := by
  refine ⟨dk_mul (dk_input _ _) hp.dx, dk_add (dk_const _ _) (dk_mul (dk_input _ _) (dk_sub hp.dy (dk_const _ _))),
    dk_add (dk_const _ _) (dk_mul (dk_input _ _) (dk_sub hp.dz (dk_const _ _))), dk_mul (dk_input _ _) hp.dt, ?_⟩
  show ExtGood (TlsMpc.EdwardsHinted.chooseExtValue (input k) (TlsMpc.EdwardsHinted.evalExt input p))
  rcases hb with h | h
  · rw [h]
    have e : TlsMpc.EdwardsHinted.chooseExtValue (ofNat 0) (TlsMpc.EdwardsHinted.evalExt input p) =
        TlsMpc.EdwardsHinted.neutralValue := by
      apply ext_eq <;> simp only [TlsMpc.EdwardsHinted.chooseExtValue, TlsMpc.EdwardsHinted.neutralValue, zero_mul',
        one_add_zero_mul, one_add_zero]
    rw [e]
    exact neutralValue_good
  · rw [h]
    have e : TlsMpc.EdwardsHinted.chooseExtValue (ofNat 1) (TlsMpc.EdwardsHinted.evalExt input p) =
        TlsMpc.EdwardsHinted.evalExt input p := by
      apply ext_eq <;> simp only [TlsMpc.EdwardsHinted.chooseExtValue, one_mul', one_add_one_mul_sub, one_add_sub_one]
    rw [e]
    exact hp.good

theorem chooseAffine_ok {input : Nat → F} (k : Nat) {p : Pt} (hp : PtOk input p) (hb : IsBit (input k)) :
    ExtOk input (TlsMpc.EdwardsHinted.chooseAffine (.input k) p) := by
  refine ⟨dk_mul (dk_input _ _) hp.d1, dk_add (dk_const _ _) (dk_mul (dk_input _ _) (dk_sub hp.d2 (dk_const _ _))),
    dk_const _ _, dk_mul (dk_mul (dk_input _ _) hp.d1) hp.d2, ?_⟩
  rcases hb with h | h
  · have e : TlsMpc.EdwardsHinted.evalExt input (TlsMpc.EdwardsHinted.chooseAffine (.input k) p) =
        TlsMpc.EdwardsHinted.neutralValue := by
      apply ext_eq <;>
        simp only [TlsMpc.EdwardsHinted.evalExt, TlsMpc.EdwardsHinted.chooseAffine, TlsMpc.EdwardsHinted.neutralValue,
          TlsMpc.EdwardsAffine.mul, TlsMpc.EdwardsAffine.add, TlsMpc.EdwardsAffine.sub, TlsMpc.FieldDag.Expr.eval,
          TlsMpc.FieldDag.Bin.eval, h, zero_mul', one_add_zero_mul, one_add_zero]
    rw [e]
    exact neutralValue_good
  · have e : TlsMpc.EdwardsHinted.evalExt input (TlsMpc.EdwardsHinted.chooseAffine (.input k) p) =
        TlsMpc.EdwardsHinted.ofAffineValue (TlsMpc.EdwardsAffine.evalPoint input p) := by
      apply ext_eq <;>
        simp only [TlsMpc.EdwardsHinted.evalExt, TlsMpc.EdwardsHinted.chooseAffine, TlsMpc.EdwardsHinted.ofAffineValue,
          TlsMpc.EdwardsAffine.evalPoint, TlsMpc.EdwardsAffine.mul, TlsMpc.EdwardsAffine.add, TlsMpc.EdwardsAffine.sub,
          TlsMpc.FieldDag.Expr.eval, TlsMpc.FieldDag.Bin.eval, h, one_mul', one_add_one_mul_sub, one_add_sub_one]
    rw [e]
    exact ofAffineValue_good _ hp.on

/-! ## Hinted bases, links, entries (`EdwardsHinted`) -/

/-- The two parties' hint points of window `i` (inputs `h + 4i … h + 4i + 3`) are curve points. -/
def HintsIn (input : Nat → F) (h count : Nat) : Prop :=
  ∀ i, i < count - 1 → curveValue (input (h + 4 * i), input (h + 4 * i + 1)) = 0 ∧
    curveValue (input (h + 4 * i + 2), input (h + 4 * i + 2 + 1)) = 0

theorem hinted_ok (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed) {input : Nat → F} (i : Nat)
    (h1 : curveValue (input i, input (i + 1)) = 0) (h2 : curveValue (input (i + 2), input (i + 2 + 1)) = 0) :
    PtOk input (TlsMpc.EdwardsHinted.hinted i) :=
  pointAdd_ok hinv hC hA (inputPoint_ok input i h1) (negate_ok (inputPoint_ok input (i + 2) h2))

theorem bases_ok (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed) {input : Nat → F} (first : Pt)
    (hf : PtOk input first) (h count : Nat) (hh : HintsIn input h count) :
    ∀ b ∈ TlsMpc.EdwardsHinted.bases first h count, PtOk input b := by
  intro b hb
  simp only [TlsMpc.EdwardsHinted.bases, List.mem_cons, List.mem_map, List.mem_range] at hb
  rcases hb with rfl | ⟨i, hi, rfl⟩
  · exact hf
  · exact hinted_ok hinv hC hA _ (hh i hi).1 (hh i hi).2

theorem linksFrom_ok {ε : Type} {input : Nat → F} (step : Pt → List ε × Pt) (hs : ∀ b, PtOk input b → PtOk input (step b).2) :
    ∀ (b : Pt) (rest : List Pt), PtOk input b → (∀ c ∈ rest, PtOk input c) →
      ∀ d ∈ TlsMpc.EdwardsHinted.linksFrom step b rest, DivOk input d.1 ∧ DivOk input d.2
  | _, [], _, _ => fun d hd => by simp [TlsMpc.EdwardsHinted.linksFrom] at hd
  | b, c :: rest, hb, hr => by
    intro d hd
    simp only [TlsMpc.EdwardsHinted.linksFrom, List.mem_cons] at hd
    have hc := hr c (by simp)
    rcases hd with rfl | hd
    · exact ⟨dk_sub (hs b hb).d1 hc.d1, dk_sub (hs b hb).d2 hc.d2⟩
    · exact linksFrom_ok step hs c rest hc (fun x hx => hr x (by simp [hx])) d hd

theorem links_ok {ε : Type} {input : Nat → F} (step : Pt → List ε × Pt) (hs : ∀ b, PtOk input b → PtOk input (step b).2)
    (bs : List Pt) (h : ∀ b ∈ bs, PtOk input b) :
    ∀ d ∈ TlsMpc.EdwardsHinted.links step bs, DivOk input d.1 ∧ DivOk input d.2 := by
  cases bs with
  | nil => intro d hd; simp [TlsMpc.EdwardsHinted.links] at hd
  | cons b rest => exact linksFrom_ok step hs b rest (h b (by simp)) (fun x hx => h x (by simp [hx]))

theorem masked_ok {input : Nat → F} (m : Nat) (ds : List (Expr × Expr)) (h : ∀ d ∈ ds, DivOk input d.1 ∧ DivOk input d.2) :
    ∀ e ∈ TlsMpc.EdwardsHinted.masked m ds, DivOk input e := by
  intro e he
  simp only [TlsMpc.EdwardsHinted.masked, List.mem_flatMap] at he
  obtain ⟨⟨d, i⟩, hx, he⟩ := he
  have hd : d ∈ ds := by
    have := List.mem_map_of_mem (f := Prod.fst) hx
    rw [List.zipIdx_map_fst] at this
    exact this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact dk_mul (h d hd).1 (dk_input _ _)
  · exact dk_mul (h d hd).2 (dk_input _ _)

theorem doublings_ok (hinv : FieldInverse) (hX : ExtClosed) {input : Nat → F} (b : Pt) (hb : PtOk input b) :
    (∀ e ∈ (TlsMpc.EdwardsHinted.doublings b).1, ExtOk input e) ∧ PtOk input (TlsMpc.EdwardsHinted.doublings b).2 := by
  have h1 := ofAffine_ok hb
  have h2 := extAdd_ok hX h1 h1
  have h4 := extAdd_ok hX h2 h2
  have h8 := extAdd_ok hX h4 h4
  refine ⟨fun e he => ?_, toAffine_ok (extAdd_ok hX h8 h8)⟩
  simp only [TlsMpc.EdwardsHinted.doublings, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h4
  · exact h8

/-! ## Per program: the source divisions on honest inputs -/

section Programs

variable (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed) (hX : ExtClosed)

/-- **`edwards-offset-sum`'s input condition**: the initial point (inputs 0, 1) and the 64 signed
window points (`(s·x, y)` from inputs `2 + 3w …`) are curve points, and their sum's `y ≠ 1`. -/
structure OffsetSumIn (input : Nat → F) : Prop where
  initial : curveValue (input 0, input 1) = 0
  windows : ∀ w, w < TlsMpc.EdwardsAffine.windows →
    curveValue (input (2 + 3 * w + 2) * input (2 + 3 * w), input (2 + 3 * w + 1)) = 0
  notNeutral : ofNat 1 - (TlsMpc.EdwardsAffine.sumTreeValue ((input 0, input 1) ::
    (List.range TlsMpc.EdwardsAffine.windows).map
      (fun w => (input (2 + 3 * w + 2) * input (2 + 3 * w), input (2 + 3 * w + 1))))).2 ≠ 0

include hinv hC hA in
theorem offsetSum_divOk (input : Nat → F) (h : OffsetSumIn input) :
    ∀ e ∈ TlsMpc.EdwardsAffine.offsetSum, DivOk input e := by
  have hpts : ∀ p ∈ (TlsMpc.EdwardsAffine.inputPoint 0 :: (List.range TlsMpc.EdwardsAffine.windows).map
      (fun w => TlsMpc.EdwardsAffine.signedPoint (2 + 3 * w))), PtOk input p := by
    intro p hp
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
    rcases hp with rfl | ⟨w, hw, rfl⟩
    · exact inputPoint_ok input 0 h.initial
    · exact ⟨dk_mul (dk_input _ _) (dk_input _ _), dk_input _ _, h.windows w hw⟩
  have hs := sumTree_ok hinv hC hA _ hpts
  intro e he
  simp only [TlsMpc.EdwardsAffine.offsetSum, List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  refine dk_div (dk_add (dk_const _ _) hs.d2) (dk_sub (dk_const _ _) hs.d2) ?_
  have e2 := congrArg Prod.snd (TlsMpc.EdwardsAffine.sumTree_eval input (TlsMpc.EdwardsAffine.inputPoint 0 ::
    (List.range TlsMpc.EdwardsAffine.windows).map (fun w => TlsMpc.EdwardsAffine.signedPoint (2 + 3 * w))))
  simp only [TlsMpc.EdwardsAffine.evalPoint, List.map_cons, List.map_map] at e2
  show ofNat 1 - _ ≠ 0
  rw [e2]
  exact h.notNeutral

/-- **`edwards-torsion-hinted`'s input condition**: the two parties' hint points (inputs 2, 3 and
4, 5) are curve points. -/
structure TorsionIn (input : Nat → F) : Prop where
  hintA : curveValue (input 2, input 3) = 0
  hintB : curveValue (input 4, input 5) = 0

include hinv hC hA hX in
theorem torsion_divOk (input : Nat → F) (h : TorsionIn input) :
    ∀ e ∈ TlsMpc.EdwardsHinted.torsionHinted (), DivOk input e := by
  have hq := hinted_ok hinv hC hA (input := input) 2 h.hintA h.hintB
  have e1 := ofAffine_ok hq
  have e2 := extAdd_ok hX e1 e1
  have e4 := extAdd_ok hX e2 e2
  have e8 := toAffine_ok (extAdd_ok hX e4 e4)
  have hcc : DivOk input (TlsMpc.EdwardsHinted.curveCheck (TlsMpc.EdwardsHinted.hinted 2)) :=
    dk_add (dk_mul (dk_const _ _) (dk_sub (dk_sub (dk_mul hq.d2 hq.d2) (dk_mul hq.d1 hq.d1)) (dk_const _ _)))
      (dk_mul (dk_const _ _) (dk_mul (dk_mul hq.d1 hq.d1) (dk_mul hq.d2 hq.d2)))
  intro e he
  simp only [TlsMpc.EdwardsHinted.torsionHinted, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact dk_sub e8.d1 (dk_input _ _)
  · exact dk_add (dk_sub e8.d2 (dk_input _ _)) (dk_mul (dk_input _ _) hcc)

/-- **`edwards-signature-sum`'s input condition**: `flip` (input 0) and the selection bits (the
256 bits of `h` from 1025, the 253 bits of `s` from 2293) are bits, and the table entries (4 inputs
each, from 1 and from 1281) represent curve points. -/
structure SignatureIn (input : Nat → F) : Prop where
  flip : IsBit (input 0)
  keyBits : ∀ i, i < 256 → IsBit (input (1025 + i))
  keyPts : ∀ i, i < 256 → ExtGood ⟨input (1 + 4 * i), input (1 + 4 * i + 1), input (1 + 4 * i + 2), input (1 + 4 * i + 3)⟩
  baseBits : ∀ i, i < 253 → IsBit (input (2293 + i))
  basePts : ∀ i, i < 253 →
    ExtGood ⟨input (1281 + 4 * i), input (1281 + 4 * i + 1), input (1281 + 4 * i + 2), input (1281 + 4 * i + 3)⟩

theorem extInput_ok (input : Nat → F) (i : Nat)
    (h : ExtGood ⟨input i, input (i + 1), input (i + 2), input (i + 3)⟩) :
    ExtOk input (TlsMpc.EdwardsHinted.extInput i) := ⟨dk_input _ _, dk_input _ _, dk_input _ _, dk_input _ _, h⟩

/-- A sign `c` with `c² = 1` applied to `X` and `T` keeps a represented point represented. -/
theorem extGood_scale (hinv : FieldInverse) (c : F) (hc : c * c = ofNat 1) (v : EV) (hv : ExtGood v) :
    ExtGood ⟨c * v.x, v.y, v.z, c * v.t⟩ := by
  have hon := hv.on
  have ht := hv.t_eq
  simp only [TlsMpc.EdwardsHinted.toAffineValue] at hon
  refine ⟨hv.z_ne, ?_, ?_⟩
  · simp only [TlsMpc.EdwardsHinted.toAffineValue]
    generalize inverse v.z = iz at hon ⊢
    have e : c * v.x * iz = c * (v.x * iz) := by grind
    rw [e, curveValue_scale _ _ _ hc]
    exact hon
  · simp only
    rw [ht]
    generalize inverse v.z = iz
    grind

theorem sign_sq (f : F) (hf : IsBit f) : (ofNat 2 * f - ofNat 1) * (ofNat 2 * f - ofNat 1) = ofNat 1 := by
  rcases hf with h | h <;> rw [h] <;> decide

/-- `signatureSum`'s key entry `i`: `±(2^i·A)` selected by bit `i` of `h` (the program's `key`). -/
def sigKey (i : Nat) : Ex :=
  let sign := TlsMpc.EdwardsAffine.sub (TlsMpc.EdwardsAffine.mul (.const 2) (.input 0)) (.const 1)
  let p := TlsMpc.EdwardsHinted.extInput (1 + 4 * i)
  let m := TlsMpc.EdwardsAffine.mul (.input (1025 + i)) sign
  ⟨TlsMpc.EdwardsAffine.mul m p.x,
    TlsMpc.EdwardsAffine.add (.const 1) (TlsMpc.EdwardsAffine.mul (.input (1025 + i)) (TlsMpc.EdwardsAffine.sub p.y (.const 1))),
    TlsMpc.EdwardsAffine.add (.const 1) (TlsMpc.EdwardsAffine.mul (.input (1025 + i)) (TlsMpc.EdwardsAffine.sub p.z (.const 1))),
    TlsMpc.EdwardsAffine.mul m p.t⟩

/-- `signatureSum`'s chosen points. -/
def sigChosen : List Ex :=
  (List.range 256).map sigKey ++
    (List.range 253).map (fun i => TlsMpc.EdwardsHinted.chooseExt (.input (2293 + i)) (TlsMpc.EdwardsHinted.extInput (1281 + 4 * i)))

theorem signatureSum_eq : TlsMpc.EdwardsHinted.signatureSum () =
    [(TlsMpc.EdwardsHinted.toAffine (TlsMpc.EdwardsHinted.extSum sigChosen)).1,
     (TlsMpc.EdwardsHinted.toAffine (TlsMpc.EdwardsHinted.extSum sigChosen)).2] := rfl

theorem sigKey_zero (input : Nat → F) (i : Nat) (hb : input (1025 + i) = ofNat 0) :
    TlsMpc.EdwardsHinted.evalExt input (sigKey i) = TlsMpc.EdwardsHinted.neutralValue := by
  apply ext_eq <;>
    simp only [sigKey, TlsMpc.EdwardsHinted.evalExt, TlsMpc.EdwardsHinted.extInput, TlsMpc.EdwardsHinted.neutralValue,
      TlsMpc.EdwardsAffine.mul, TlsMpc.EdwardsAffine.add, TlsMpc.EdwardsAffine.sub, TlsMpc.FieldDag.Expr.eval,
      TlsMpc.FieldDag.Bin.eval, hb, zero_mul', one_add_zero_mul, one_add_zero]

theorem sigKey_one (input : Nat → F) (i : Nat) (hb : input (1025 + i) = ofNat 1) :
    TlsMpc.EdwardsHinted.evalExt input (sigKey i) =
      ⟨(ofNat 2 * input 0 - ofNat 1) * input (1 + 4 * i), input (1 + 4 * i + 1), input (1 + 4 * i + 2),
        (ofNat 2 * input 0 - ofNat 1) * input (1 + 4 * i + 3)⟩ := by
  apply ext_eq <;>
    simp only [sigKey, TlsMpc.EdwardsHinted.evalExt, TlsMpc.EdwardsHinted.extInput,
      TlsMpc.EdwardsAffine.mul, TlsMpc.EdwardsAffine.add, TlsMpc.EdwardsAffine.sub, TlsMpc.FieldDag.Expr.eval,
      TlsMpc.FieldDag.Bin.eval, hb, one_mul', one_add_one_mul_sub, one_add_sub_one]

include hinv in
theorem sigKey_ok (input : Nat → F) (h : SignatureIn input) (i : Nat) (hi : i < 256) : ExtOk input (sigKey i) := by
  have hsign : DivOk input (TlsMpc.EdwardsAffine.sub (TlsMpc.EdwardsAffine.mul (.const 2) (.input 0)) (.const 1)) :=
    dk_sub (dk_mul (dk_const _ _) (dk_input _ _)) (dk_const _ _)
  have hp := extInput_ok input (1 + 4 * i) (h.keyPts i hi)
  refine ⟨dk_mul (dk_mul (dk_input _ _) hsign) hp.dx,
    dk_add (dk_const _ _) (dk_mul (dk_input _ _) (dk_sub hp.dy (dk_const _ _))),
    dk_add (dk_const _ _) (dk_mul (dk_input _ _) (dk_sub hp.dz (dk_const _ _))),
    dk_mul (dk_mul (dk_input _ _) hsign) hp.dt, ?_⟩
  rcases h.keyBits i hi with hb | hb
  · rw [sigKey_zero input i hb]
    exact neutralValue_good
  · rw [sigKey_one input i hb]
    exact extGood_scale hinv _ (sign_sq (input 0) h.flip) ⟨input (1 + 4 * i), input (1 + 4 * i + 1),
      input (1 + 4 * i + 2), input (1 + 4 * i + 3)⟩ (h.keyPts i hi)

include hinv hX in
theorem signature_divOk (input : Nat → F) (h : SignatureIn input) :
    ∀ e ∈ TlsMpc.EdwardsHinted.signatureSum (), DivOk input e := by
  have hall : ∀ q ∈ sigChosen, ExtOk input q := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · simp only [List.mem_map, List.mem_range] at hq
      obtain ⟨i, hi, rfl⟩ := hq
      exact sigKey_ok hinv input h i hi
    · simp only [List.mem_map, List.mem_range] at hq
      obtain ⟨i, hi, rfl⟩ := hq
      exact chooseExt_ok _ (extInput_ok input _ (h.basePts i hi)) (h.baseBits i hi)
  have hs := toAffine_ok (extSum_ok hX _ hall)
  intro e he
  rw [signatureSum_eq] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact hs.d1
  · exact hs.d2

/-- **`lift-point`'s input condition**: the two mask points (inputs 5, 6 and 7, 8) and the selected
point `p` (the lifted point when `valid`, the base point otherwise) are curve points, and the
denominator `1 + valid·u` of `y` is not zero. -/
structure LiftPointIn (input : Nat → F) : Prop where
  maskA : curveValue (input 5, input 6) = 0
  maskB : curveValue (input 7, input 8) = 0
  den : ofNat 1 + (input 1 + input 4 - ofNat 2 * (input 1 * input 4)) * input 2 ≠ 0
  point : curveValue
    (ofNat TlsMpc.EdwardsHinted.baseX + (input 1 + input 4 - ofNat 2 * (input 1 * input 4)) *
        (input 0 * (input 2 * input 3) - ofNat TlsMpc.EdwardsHinted.baseX),
      ofNat TlsMpc.EdwardsHinted.baseY + (input 1 + input 4 - ofNat 2 * (input 1 * input 4)) *
        ((input 2 - ofNat 1) * inverse (ofNat 1 + (input 1 + input 4 - ofNat 2 * (input 1 * input 4)) * input 2) -
          ofNat TlsMpc.EdwardsHinted.baseY)) = 0

include hinv hC hA in
theorem liftPoint_divOk (input : Nat → F) (h : LiftPointIn input) :
    ∀ e ∈ TlsMpc.EdwardsHinted.liftPoint (), DivOk input e := by
  have hv : DivOk input (TlsMpc.EdwardsHinted.bitXor (.input 1) (.input 4)) :=
    dk_sub (dk_add (dk_input _ _) (dk_input _ _)) (dk_mul (dk_const _ _) (dk_mul (dk_input _ _) (dk_input _ _)))
  have hx : DivOk input (TlsMpc.EdwardsAffine.mul (.input 0) (TlsMpc.EdwardsAffine.mul (.input 2) (.input 3))) :=
    dk_mul (dk_input _ _) (dk_mul (dk_input _ _) (dk_input _ _))
  have hy : DivOk input (TlsMpc.EdwardsAffine.div (TlsMpc.EdwardsAffine.sub (.input 2) (.const 1))
      (TlsMpc.EdwardsAffine.add (.const 1) (TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsHinted.bitXor (.input 1) (.input 4)) (.input 2)))) :=
    dk_div (dk_sub (dk_input _ _) (dk_const _ _)) (dk_add (dk_const _ _) (dk_mul hv (dk_input _ _))) h.den
  have hp : PtOk input
      (TlsMpc.EdwardsAffine.add (.const TlsMpc.EdwardsHinted.baseX)
        (TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsHinted.bitXor (.input 1) (.input 4))
          (TlsMpc.EdwardsAffine.sub (TlsMpc.EdwardsAffine.mul (.input 0) (TlsMpc.EdwardsAffine.mul (.input 2) (.input 3)))
            (.const TlsMpc.EdwardsHinted.baseX))),
       TlsMpc.EdwardsAffine.add (.const TlsMpc.EdwardsHinted.baseY)
        (TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsHinted.bitXor (.input 1) (.input 4))
          (TlsMpc.EdwardsAffine.sub (TlsMpc.EdwardsAffine.div (TlsMpc.EdwardsAffine.sub (.input 2) (.const 1))
            (TlsMpc.EdwardsAffine.add (.const 1) (TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsHinted.bitXor (.input 1) (.input 4)) (.input 2))))
            (.const TlsMpc.EdwardsHinted.baseY)))) :=
    ⟨dk_add (dk_const _ _) (dk_mul hv (dk_sub hx (dk_const _ _))),
      dk_add (dk_const _ _) (dk_mul hv (dk_sub hy (dk_const _ _))), h.point⟩
  have hz := pointAdd_ok hinv hC hA (pointAdd_ok hinv hC hA (inputPoint_ok input 5 h.maskA)
    (inputPoint_ok input 7 h.maskB)) hp
  intro e he
  simp only [TlsMpc.EdwardsHinted.liftPoint, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact hv
  · exact hp.d1
  · exact hp.d2
  · exact hz.d1
  · exact hz.d2

/-- **`edwards-bit-table`'s input condition**: the point (inputs 0, 1) and the two parties' 63 hint
points per side (from input 2) are curve points. -/
structure BitTableIn (input : Nat → F) : Prop where
  point : curveValue (input 0, input 1) = 0
  hints : HintsIn input 2 TlsMpc.EdwardsAffine.windows

include hinv hC hA hX in
theorem bitTable_divOk (input : Nat → F) (h : BitTableIn input) :
    ∀ e ∈ TlsMpc.EdwardsHinted.bitTable (), DivOk input e := by
  have hb := bases_ok hinv hC hA (TlsMpc.EdwardsAffine.inputPoint 0) (inputPoint_ok input 0 h.point) 2
    TlsMpc.EdwardsAffine.windows h.hints
  have hl := links_ok TlsMpc.EdwardsHinted.doublings (fun b hb => (doublings_ok hinv hX b hb).2) _ hb
  have hm := masked_ok (2 + 4 * (TlsMpc.EdwardsAffine.windows - 1)) _ hl
  intro e he
  unfold TlsMpc.EdwardsHinted.bitTable at he
  rcases List.mem_append.mp he with he | he
  · exact hm e he
  · simp only [List.mem_flatMap, TlsMpc.EdwardsHinted.entries] at he
    obtain ⟨q, ⟨b, hbm, hq⟩, he⟩ := he
    have hq' := (doublings_ok hinv hX b (hb b hbm)).1 q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact hq'.dx
    · exact hq'.dy
    · exact hq'.dz
    · exact hq'.dt

/-- **`edwards-prepare-hinted`'s input condition**: as `edwards-bit-table` (the point and the hint
points), and the two parties' 252 scalar bits each (from input `prepareBits`) are bits. -/
structure PrepareHintedIn (input : Nat → F) : Prop where
  point : curveValue (input 0, input 1) = 0
  hints : HintsIn input TlsMpc.EdwardsHinted.prepareHints TlsMpc.EdwardsAffine.windows
  bits : ∀ i, i < 2 * TlsMpc.EdwardsAffine.scalarBits → IsBit (input (TlsMpc.EdwardsHinted.prepareBits + i))

include hinv hC hA hX in
theorem prepareHinted_divOk (input : Nat → F) (h : PrepareHintedIn input) :
    ∀ e ∈ TlsMpc.EdwardsHinted.prepareHinted (), DivOk input e := by
  have hb := bases_ok hinv hC hA (TlsMpc.EdwardsAffine.inputPoint 0) (inputPoint_ok input 0 h.point)
    TlsMpc.EdwardsHinted.prepareHints TlsMpc.EdwardsAffine.windows h.hints
  have hl := links_ok TlsMpc.EdwardsAffine.window (fun b hb => (window_ok hinv hC hA b hb).2) _ hb
  have hm := masked_ok TlsMpc.EdwardsHinted.prepareMasks _ hl
  have ht : ∀ p ∈ TlsMpc.EdwardsHinted.entries TlsMpc.EdwardsAffine.window (TlsMpc.EdwardsHinted.prepareBases ()),
      PtOk input p := by
    intro p hp
    simp only [TlsMpc.EdwardsHinted.entries, List.mem_flatMap] at hp
    obtain ⟨b, hbm, hp⟩ := hp
    exact (window_ok hinv hC hA b (hb b hbm)).1 p hp
  have hch : ∀ q ∈ (List.range (2 * TlsMpc.EdwardsAffine.scalarBits)).map (fun i =>
      TlsMpc.EdwardsHinted.chooseAffine (.input (TlsMpc.EdwardsHinted.prepareBits + i))
        (TlsMpc.EdwardsAffine.bitEntry (TlsMpc.EdwardsHinted.entries TlsMpc.EdwardsAffine.window
          (TlsMpc.EdwardsHinted.prepareBases ())) (i % TlsMpc.EdwardsAffine.scalarBits))), ExtOk input q := by
    intro q hq
    simp only [List.mem_map, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact chooseAffine_ok _ (bitEntry_ok ht _) (h.bits i hi)
  have hinit := toAffine_ok (extSum_ok hX _ hch)
  intro e he
  unfold TlsMpc.EdwardsHinted.prepareHinted at he
  dsimp only at he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · simp only [List.mem_map, List.mem_range] at he
        obtain ⟨i, -, rfl⟩ := he
        exact dk_bitCheck _ _
      · exact hm e he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact hinit.d1
      · exact hinit.d2
  · simp only [List.mem_flatMap] at he
    obtain ⟨p, hp, he⟩ := he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (ht p hp).d1
    · exact (ht p hp).d2

/-! ### `edwards-prepare`: the recipient, the table, the initial point -/

def rY : Expr := TlsMpc.EdwardsAffine.div (TlsMpc.EdwardsAffine.sub (.input 0) (.const 1)) (TlsMpc.EdwardsAffine.add (.input 0) (.const 1))
def rYY : Expr := TlsMpc.EdwardsAffine.mul rY rY
def rXX : Expr := TlsMpc.EdwardsAffine.div (TlsMpc.EdwardsAffine.mul (.const 121666) (TlsMpc.EdwardsAffine.sub rYY (.const 1)))
  (TlsMpc.EdwardsAffine.sub (.const 121666) (TlsMpc.EdwardsAffine.mul (.const 121665) rYY))
def rT : Expr := (List.range 250).foldl (fun t _ => TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsAffine.mul t t) rXX) rXX
def rC : Expr := TlsMpc.EdwardsAffine.mul rT rT
def rCC : Expr := TlsMpc.EdwardsAffine.mul rC rC
def rB : Expr := TlsMpc.EdwardsAffine.div (TlsMpc.EdwardsAffine.add rCC rXX) (TlsMpc.EdwardsAffine.mul (.const 2) rXX)
def rX : Expr := TlsMpc.EdwardsAffine.mul rC (TlsMpc.EdwardsAffine.add (.const TlsMpc.EdwardsAffine.sqrtMinusOne)
  (TlsMpc.EdwardsAffine.mul rB (.const (TlsMpc.FieldDag.modulus + 1 - TlsMpc.EdwardsAffine.sqrtMinusOne))))

theorem recipient_eq : TlsMpc.EdwardsAffine.recipient (.input 0) =
    ((rX, rY), TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsAffine.sub rCC rXX) (TlsMpc.EdwardsAffine.add rCC rXX)) := rfl

/-- The table and the chosen points of `prepare`, for the recipient point `R`. -/
def prepChosen (R : Pt) : List Pt :=
  (List.range (2 * TlsMpc.EdwardsAffine.scalarBits)).map (fun i =>
    TlsMpc.EdwardsAffine.choose (.input (2 + i)) (TlsMpc.EdwardsAffine.bitEntry (TlsMpc.EdwardsAffine.table R) (i % TlsMpc.EdwardsAffine.scalarBits)))

theorem prepare_eq : TlsMpc.EdwardsAffine.prepare =
    [TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsAffine.sub rCC rXX) (TlsMpc.EdwardsAffine.add rCC rXX)) (.input 1)] ++
      ((List.range (2 * TlsMpc.EdwardsAffine.scalarBits)).map (fun i => Expr.input (2 + i))).map TlsMpc.EdwardsAffine.bitCheck ++
      [(TlsMpc.EdwardsAffine.sumTree (prepChosen (rX, rY))).1, (TlsMpc.EdwardsAffine.sumTree (prepChosen (rX, rY))).2] ++
      (TlsMpc.EdwardsAffine.table (rX, rY)).flatMap (fun p => [p.1, p.2]) := rfl

/-- The recipient's `y = (u − 1)/(u + 1)` on `u = input 0`. -/
def recY (input : Nat → F) : F := (input 0 - ofNat 1) * inverse (input 0 + ofNat 1)

/-- The recipient's `x² = 121666·(y² − 1)/(121666 − 121665·y²)`. -/
def recXX (input : Nat → F) : F :=
  ofNat 121666 * (recY input * recY input - ofNat 1) * inverse (ofNat 121666 - ofNat 121665 * (recY input * recY input))

/-- **`edwards-prepare`'s input condition** (input 0 the recipient's `u`, 1 the mask, 2 … 505 the
scalar bits): the recipient's three denominators `u + 1`, `121666 − 121665·y²`, `2·x²` are nonzero,
its check is zero (`u` is the Montgomery coordinate of a curve point, so its point is a curve point
under `RecipientOnCurve`), and the 504 scalar bits are bits. -/
structure PrepareIn (input : Nat → F) : Prop where
  u1 : input 0 + ofNat 1 ≠ 0
  yden : ofNat 121666 - ofNat 121665 * (recY input * recY input) ≠ 0
  xx : ofNat 2 * recXX input ≠ 0
  valid : (TlsMpc.EdwardsAffine.recipient (.input 0)).2.eval input = ofNat 0
  bits : ∀ i, i < 2 * TlsMpc.EdwardsAffine.scalarBits → IsBit (input (2 + i))

theorem rY_eval (input : Nat → F) : rY.eval input = recY input := rfl

theorem rXX_eval (input : Nat → F) : rXX.eval input = recXX input := rfl

include hinv hC hA in
theorem prepare_divOk (hR : RecipientOnCurve) (input : Nat → F) (h : PrepareIn input) :
    ∀ e ∈ TlsMpc.EdwardsAffine.prepare, DivOk input e := by
  have hy : DivOk input rY := dk_div (dk_sub (dk_input _ _) (dk_const _ _)) (dk_add (dk_input _ _) (dk_const _ _)) h.u1
  have hyy : DivOk input rYY := dk_mul hy hy
  have hxx : DivOk input rXX := by
    refine dk_div (dk_mul (dk_const _ _) (dk_sub hyy (dk_const _ _))) (dk_sub (dk_const _ _) (dk_mul (dk_const _ _) hyy)) ?_
    have e : (TlsMpc.EdwardsAffine.sub (.const 121666) (TlsMpc.EdwardsAffine.mul (.const 121665) rYY)).eval input =
        ofNat 121666 - ofNat 121665 * (rY.eval input * rY.eval input) := rfl
    rw [e, rY_eval]
    exact h.yden
  have ht : DivOk input rT :=
    foldl_inv (DivOk input) (fun t _ => TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsAffine.mul t t) rXX)
      (fun t _ ht => dk_mul (dk_mul ht ht) hxx) _ _ hxx
  have hc : DivOk input rC := dk_mul ht ht
  have hcc : DivOk input rCC := dk_mul hc hc
  have hb : DivOk input rB := by
    refine dk_div (dk_add hcc hxx) (dk_mul (dk_const _ _) hxx) ?_
    have e : (TlsMpc.EdwardsAffine.mul (.const 2) rXX).eval input = ofNat 2 * rXX.eval input := rfl
    rw [e, rXX_eval]
    exact h.xx
  have hx : DivOk input rX := dk_mul hc (dk_add (dk_const _ _) (dk_mul hb (dk_const _ _)))
  have hon := hR input h.valid
  rw [recipient_eq] at hon
  have hR' : PtOk input (rX, rY) := ⟨hx, hy, hon⟩
  have htab := table_ok hinv hC hA (rX, rY) hR'
  have hch : ∀ p ∈ prepChosen (rX, rY), PtOk input p := by
    intro p hp
    simp only [prepChosen, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact choose_ok _ (bitEntry_ok htab _) (h.bits i hi)
  have hinit := sumTree_ok hinv hC hA _ hch
  intro e he
  rw [prepare_eq] at he
  generalize TlsMpc.EdwardsAffine.sumTree (prepChosen (rX, rY)) = s at hinit he
  generalize TlsMpc.EdwardsAffine.table (rX, rY) = tab at htab he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        subst he
        exact dk_mul (dk_mul (dk_sub hcc hxx) (dk_add hcc hxx)) (dk_input _ _)
      · simp only [List.map_map, List.mem_map, List.mem_range] at he
        obtain ⟨i, -, rfl⟩ := he
        exact dk_bitCheck _ _
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | he
      · rw [he]
        exact hinit.d1
      · rw [he]
        exact hinit.d2
  · simp only [List.mem_flatMap] at he
    obtain ⟨p, hp, he⟩ := he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | he
    · rw [he]
      exact (htab p hp).d1
    · rw [he]
      exact (htab p hp).d2

end Programs

end PL

/-! ## The programs as loaded: `ComputesD` and `Live` -/

open TlsMpc.FieldProgramsV3 (Decl)

/-- **What the loader establishes** (named per program): the program under `name` is the V3
program of the declaration `d` (`FieldProgramsV3.find name`: the loader checks the text's pin, and
`parse_render` gives the program back), with the mask count the shell checks (`WFB.CurveProgs`,
F25c). -/
structure LoadedAs (E : Env) (name : Bytes) (d : Decl) (m : Nat) (p : Program) : Prop where
  loaded : E.programs name = some p
  decl : d.program = some p
  masks : p.masks = m

/-- **`ComputesD` for a declaration's program** (`Decl.values`: `FieldDagV3.eval_compileAll`). -/
theorem computesD_of_decl (hinv : FieldInverse) (d : Decl) (p : Program) (hp : d.program = some p) (m o : Nat)
    (hm : p.masks = m) (ho : d.exprs.length = o) :
    ComputesD p d.inputs m o (fun i => d.exprs.map (Expr.eval i)) := by
  refine ⟨?_, hm, by rw [TlsMpc.FieldDag.Compiled.Decl.outputs_length d p hp, ho],
    fun input mask outs opened h => TlsMpc.FieldProgramsV3.Decl.values hinv d p hp input mask outs opened h⟩
  obtain ⟨a, -, rfl⟩ := TlsMpc.FieldProgramsV3.Decl.program_eq hp
  rfl

/-- **`Live` for a declaration's program** on an input where its source divisions are nonzero
(`Compiled.Decl.live`). -/
theorem live_of_decl (hinv : FieldInverse) (d : Decl) (p : Program) (hp : d.program = some p) (input : Nat → F)
    (hd : ∀ e ∈ d.exprs, DivOk input e) : Live p input :=
  fun mask hm => TlsMpc.FieldDag.Compiled.Decl.live hinv d p hp input hd mask hm

/-! ### The declarations (`FieldProgramsV3.find`) -/

def dPrepare : Decl := TlsMpc.FieldProgramsV3.first "edwards-prepare" (2 + 2 * TlsMpc.EdwardsAffine.scalarBits)
  TlsMpc.EdwardsAffine.prepare TlsMpc.EdwardsAffine.prepareChecks
def dOffsetSum : Decl := TlsMpc.FieldProgramsV3.first "edwards-offset-sum" (2 + 3 * TlsMpc.EdwardsAffine.windows)
  TlsMpc.EdwardsAffine.offsetSum 0
def dLiftPoint : Decl := ⟨"lift-point", 9, TlsMpc.EdwardsHinted.liftPoint (), [.check, .secret, .secret, .check, .check]⟩
def dPrepareHinted : Decl := TlsMpc.FieldProgramsV3.first "edwards-prepare-hinted" TlsMpc.EdwardsHinted.prepareInputs
  (TlsMpc.EdwardsHinted.prepareHinted ()) TlsMpc.EdwardsHinted.prepareHintedChecks
def dBitTable : Decl := TlsMpc.FieldProgramsV3.first "edwards-bit-table" TlsMpc.EdwardsHinted.bitTableInputs
  (TlsMpc.EdwardsHinted.bitTable ()) (2 * (TlsMpc.EdwardsAffine.windows - 1))
def dSignatureSum : Decl := TlsMpc.FieldProgramsV3.first "edwards-signature-sum" TlsMpc.EdwardsHinted.signatureSumInputs
  (TlsMpc.EdwardsHinted.signatureSum ()) 0
def dTorsion : Decl := TlsMpc.FieldProgramsV3.first "edwards-torsion-hinted" 7 (TlsMpc.EdwardsHinted.torsionHinted ()) 0
def dX25519 : Decl := TlsMpc.FieldProgramsV3.first "x25519-fast" 257 X25519Fast.exprs 0
def dOffsetSumFast : Decl := TlsMpc.FieldProgramsV3.first "edwards-offset-sum-fast" (2 + 3 * TlsMpc.EdwardsAffine.windows)
  (TlsMpc.EdwardsHinted.offsetSumFast ()) 0
def dBitSum : Decl := TlsMpc.FieldProgramsV3.first "edwards-bit-sum" TlsMpc.EdwardsHinted.bitSumInputs
  (TlsMpc.EdwardsHinted.bitSum ()) 0
def dAffineBitSum : Decl := TlsMpc.FieldProgramsV3.first "edwards-affine-bit-sum" TlsMpc.EdwardsHinted.affineBitSumInputs
  (TlsMpc.EdwardsHinted.affineBitSum ()) 0
def dLiftOpen : Decl := ⟨"lift-open", 8, TlsMpc.EdwardsHinted.liftOpen (), TlsMpc.FieldProgramsV3.firstPublic 5 6⟩
def dOnCurve : Decl := TlsMpc.FieldProgramsV3.onCurve
def dAddU : Decl := TlsMpc.FieldProgramsV3.first "edwards-add-u" 4 TlsMpc.EdwardsShare.addU 0

/-- They are what `FieldProgramsV3.find` exports under the flows' names. -/
theorem find_decls :
    TlsMpc.FieldProgramsV3.find "edwards-prepare" = some dPrepare ∧
    TlsMpc.FieldProgramsV3.find "edwards-offset-sum" = some dOffsetSum ∧
    TlsMpc.FieldProgramsV3.find "lift-point" = some dLiftPoint ∧
    TlsMpc.FieldProgramsV3.find "edwards-prepare-hinted" = some dPrepareHinted ∧
    TlsMpc.FieldProgramsV3.find "edwards-bit-table" = some dBitTable ∧
    TlsMpc.FieldProgramsV3.find "edwards-signature-sum" = some dSignatureSum ∧
    TlsMpc.FieldProgramsV3.find "edwards-torsion-hinted" = some dTorsion ∧
    TlsMpc.FieldProgramsV3.find "x25519-fast" = some dX25519 ∧
    TlsMpc.FieldProgramsV3.find "edwards-offset-sum-fast" = some dOffsetSumFast ∧
    TlsMpc.FieldProgramsV3.find "edwards-bit-sum" = some dBitSum ∧
    TlsMpc.FieldProgramsV3.find "edwards-affine-bit-sum" = some dAffineBitSum ∧
    TlsMpc.FieldProgramsV3.find "lift-open" = some dLiftOpen ∧
    TlsMpc.FieldProgramsV3.find "edwards-on-curve" = some dOnCurve ∧
    TlsMpc.FieldProgramsV3.find "edwards-add-u" = some dAddU :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Mask-free programs: `Conv.Computes` -/

theorem x25519_ok : dX25519.ok = true := by decide
theorem offsetSumFast_ok : dOffsetSumFast.ok = true := by decide
theorem bitSum_ok : dBitSum.ok = true := by decide
theorem affineBitSum_ok : dAffineBitSum.ok = true := by decide
theorem liftOpen_ok : dLiftOpen.ok = true := by decide
theorem addU_ok : dAddU.ok = true := by decide

/-- **`x25519-fast` as loaded computes its expressions** (no mask). -/
theorem x25519_computes (hinv : FieldInverse) (p : Program) (hp : dX25519.program = some p) (hm : p.masks = 0) :
    Conv.Computes p 257 [.never, .never] (fun i => X25519Fast.exprs.map (Expr.eval i)) :=
  Conv.computes_of_decl hinv dX25519 x25519_ok p hp hm

theorem offsetSumFast_computes (hinv : FieldInverse) (p : Program) (hp : dOffsetSumFast.program = some p)
    (hm : p.masks = 0) :
    Conv.Computes p 194 [.never, .never] (fun i => (TlsMpc.EdwardsHinted.offsetSumFast ()).map (Expr.eval i)) :=
  Conv.computes_of_decl hinv dOffsetSumFast offsetSumFast_ok p hp hm

theorem bitSum_computes (hinv : FieldInverse) (p : Program) (hp : dBitSum.program = some p) (hm : p.masks = 0) :
    Conv.Computes p 1261 [.never, .never] (fun i => (TlsMpc.EdwardsHinted.bitSum ()).map (Expr.eval i)) :=
  Conv.computes_of_decl hinv dBitSum bitSum_ok p hp hm

theorem affineBitSum_computes (hinv : FieldInverse) (p : Program) (hp : dAffineBitSum.program = some p)
    (hm : p.masks = 0) :
    Conv.Computes p 757 [.never, .never] (fun i => (TlsMpc.EdwardsHinted.affineBitSum ()).map (Expr.eval i)) :=
  Conv.computes_of_decl hinv dAffineBitSum affineBitSum_ok p hp hm

theorem liftOpen_computes (hinv : FieldInverse) (p : Program) (hp : dLiftOpen.program = some p) (hm : p.masks = 0) :
    Conv.Computes p 8 [.pub, .pub, .pub, .pub, .pub, .never] (fun i => (TlsMpc.EdwardsHinted.liftOpen ()).map (Expr.eval i)) :=
  Conv.computes_of_decl hinv dLiftOpen liftOpen_ok p hp hm

theorem onCurve_computes (hinv : FieldInverse) (p : Program) (hp : dOnCurve.program = some p) (hm : p.masks = 0) :
    Conv.Computes p 2 [.pub] (fun i => [TlsMpc.EdwardsShare.onCurve.eval i]) :=
  Conv.computes_of_decl hinv dOnCurve TlsMpc.FieldProgramsV3.onCurve_ok p hp hm

theorem addU_computes (hinv : FieldInverse) (p : Program) (hp : dAddU.program = some p) (hm : p.masks = 0) :
    Conv.Computes p 4 [.never, .never] (fun i => TlsMpc.EdwardsShare.addU.map (Expr.eval i)) :=
  Conv.computes_of_decl hinv dAddU addU_ok p hp hm

/-! ### Masked programs: `ComputesD` and `Live` from the input conditions -/

set_option maxRecDepth 100000 in
theorem prepare_length : TlsMpc.EdwardsAffine.prepare.length = 1531 := by decide +kernel
theorem offsetSum_length : TlsMpc.EdwardsAffine.offsetSum.length = 1 := by decide
theorem liftPoint_length : (TlsMpc.EdwardsHinted.liftPoint ()).length = 5 := by decide
set_option maxRecDepth 100000 in
theorem prepareHinted_length : (TlsMpc.EdwardsHinted.prepareHinted ()).length = 1656 := by decide +kernel
set_option maxRecDepth 100000 in
theorem bitTable_length : (TlsMpc.EdwardsHinted.bitTable ()).length = 1150 := by decide +kernel
theorem signatureSum_length : (TlsMpc.EdwardsHinted.signatureSum ()).length = 2 := by decide
theorem torsion_length : (TlsMpc.EdwardsHinted.torsionHinted ()).length = 2 := by decide

theorem prepare_computesD (hinv : FieldInverse) (p : Program) (hp : dPrepare.program = some p) (hm : p.masks = 2031) :
    ComputesD p 506 2031 1531 (fun i => TlsMpc.EdwardsAffine.prepare.map (Expr.eval i)) :=
  computesD_of_decl hinv dPrepare p hp 2031 1531 hm prepare_length

theorem offsetSum_computesD (hinv : FieldInverse) (p : Program) (hp : dOffsetSum.program = some p) (hm : p.masks = 128) :
    ComputesD p 194 128 1 (fun i => TlsMpc.EdwardsAffine.offsetSum.map (Expr.eval i)) :=
  computesD_of_decl hinv dOffsetSum p hp 128 1 hm offsetSum_length

theorem liftPoint_computesD (hinv : FieldInverse) (p : Program) (hp : dLiftPoint.program = some p) (hm : p.masks = 5) :
    ComputesD p 9 5 5 (fun i => (TlsMpc.EdwardsHinted.liftPoint ()).map (Expr.eval i)) :=
  computesD_of_decl hinv dLiftPoint p hp 5 5 hm liftPoint_length

theorem prepareHinted_computesD (hinv : FieldInverse) (p : Program) (hp : dPrepareHinted.program = some p)
    (hm : p.masks = 1150) :
    ComputesD p 884 1150 1656 (fun i => (TlsMpc.EdwardsHinted.prepareHinted ()).map (Expr.eval i)) :=
  computesD_of_decl hinv dPrepareHinted p hp 1150 1656 hm prepareHinted_length

theorem bitTable_computesD (hinv : FieldInverse) (p : Program) (hp : dBitTable.program = some p) (hm : p.masks = 252) :
    ComputesD p 380 252 1150 (fun i => (TlsMpc.EdwardsHinted.bitTable ()).map (Expr.eval i)) :=
  computesD_of_decl hinv dBitTable p hp 252 1150 hm bitTable_length

theorem signatureSum_computesD (hinv : FieldInverse) (p : Program) (hp : dSignatureSum.program = some p)
    (hm : p.masks = 2) :
    ComputesD p 2546 2 2 (fun i => (TlsMpc.EdwardsHinted.signatureSum ()).map (Expr.eval i)) :=
  computesD_of_decl hinv dSignatureSum p hp 2 2 hm signatureSum_length

theorem torsion_computesD (hinv : FieldInverse) (p : Program) (hp : dTorsion.program = some p) (hm : p.masks = 4) :
    ComputesD p 7 4 2 (fun i => (TlsMpc.EdwardsHinted.torsionHinted ()).map (Expr.eval i)) :=
  computesD_of_decl hinv dTorsion p hp 4 2 hm torsion_length

/-- **`edwards-prepare` is live on its honest inputs** (`PrepareIn`). -/
theorem prepare_live (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed) (hR : RecipientOnCurve)
    (p : Program) (hp : dPrepare.program = some p) (input : Nat → F) (h : PL.PrepareIn input) : Live p input :=
  live_of_decl hinv dPrepare p hp input (PL.prepare_divOk hinv hC hA hR input h)

theorem offsetSum_live (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed)
    (p : Program) (hp : dOffsetSum.program = some p) (input : Nat → F) (h : PL.OffsetSumIn input) : Live p input :=
  live_of_decl hinv dOffsetSum p hp input (PL.offsetSum_divOk hinv hC hA input h)

theorem liftPoint_live (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed)
    (p : Program) (hp : dLiftPoint.program = some p) (input : Nat → F) (h : PL.LiftPointIn input) : Live p input :=
  live_of_decl hinv dLiftPoint p hp input (PL.liftPoint_divOk hinv hC hA input h)

theorem prepareHinted_live (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed) (hX : ExtClosed)
    (p : Program) (hp : dPrepareHinted.program = some p) (input : Nat → F) (h : PL.PrepareHintedIn input) :
    Live p input :=
  live_of_decl hinv dPrepareHinted p hp input (PL.prepareHinted_divOk hinv hC hA hX input h)

theorem bitTable_live (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed) (hX : ExtClosed)
    (p : Program) (hp : dBitTable.program = some p) (input : Nat → F) (h : PL.BitTableIn input) : Live p input :=
  live_of_decl hinv dBitTable p hp input (PL.bitTable_divOk hinv hC hA hX input h)

theorem signatureSum_live (hinv : FieldInverse) (hX : ExtClosed)
    (p : Program) (hp : dSignatureSum.program = some p) (input : Nat → F) (h : PL.SignatureIn input) : Live p input :=
  live_of_decl hinv dSignatureSum p hp input (PL.signature_divOk hinv hX input h)

theorem torsion_live (hinv : FieldInverse) (hC : CompleteAddition) (hA : AddClosed) (hX : ExtClosed)
    (p : Program) (hp : dTorsion.program = some p) (input : Nat → F) (h : PL.TorsionIn input) : Live p input :=
  live_of_decl hinv dTorsion p hp input (PL.torsion_divOk hinv hC hA hX input h)

end TlsMpc.Node.Flows.Curve
