import TlsMpcProofs.EdwardsCurve
import TlsMpcProofs.QuadraticResidue
import TlsMpcProofs.XEdDsaRecover

/-!
# H-GROUP for Curve25519's Edwards form: the main package's formulas are a group law

`K = ZMod (2²⁵⁵ − 19)`, `d = −121665/121666`.

* `dK_not_isSquare`: `d` is not a square (Euler's criterion, the power evaluated by the kernel);
  `−1` is a square (`sqrtMinusOne`); so `Complete dK` and `Curve := Edwards.Point dK` is a
  commutative group (`Edwards.Point.instAddCommGroup`), with a complete addition law.
* The main package's formulas compute that group law (`Affine v P`: the pair of `F` values `v`
  is the curve point `P`, through `toZMod`):
  `affine_pointAddValue` (`EdwardsAffine.pointAddValue`), `affine_neg` (`EdwardsHinted.negate`),
  `affine_neutral`, `curveCheckValue_zero_iff` (`EdwardsHinted.curveCheck` is zero exactly on the
  curve), `extRep_extAddValue` (`EdwardsHinted.extAddValue`, extended coordinates; its `Z` never
  vanishes), `extRep_ofAffineValue`, `affine_toAffineValue`, and the balanced sums
  `affine_sumTreeValue` (`EdwardsAffine.sumTreeValue`) and `extRep_extSumValue`
  (`EdwardsHinted.extSumValue`): they are the group sum of the points.
* "A square `xx` means a curve point": `recipient_onCurve` (`EdwardsAffine.recipient`: when its
  check is zero its output is a curve point) and `recover_onCurve` (`XEdDsaField.recover`: when
  `valid = 1` its `(x, y)` is a curve point).

Not here: the group ORDER (`#E = 8ℓ`, point counting). `EdwardsBasePoint.lean` proves what the
offset theorems need instead: the base point has order exactly `ℓ`.
-/

namespace TlsMpcProofs.Ed25519
open TlsMpc Edwards

/-- The Ed25519 curve constant `d = −121665/121666` in `ZMod p`. -/
def dK : K := -121665 / 121666

/-- `d` as a natural number below `p` (the main package's `XEdDsaField.d`). -/
def dNat : ℕ := 37095705934669439343138083508754565189542113879843219016388785533085940283555

theorem dNat_eq : dNat = Signal.XEdDsaField.d := rfl

theorem c121666_ne_zero : (121666 : K) ≠ 0 := by
  intro h
  have h2 : ((121666 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact absurd (Nat.le_of_dvd (by norm_num) h2) (by decide)

theorem dK_mul : dK * 121666 = -121665 := div_mul_cancel₀ _ c121666_ne_zero

theorem dK_eq_natCast : dK = (dNat : K) := by
  have h : ((dNat * 121666 + 121665 : ℕ) : K) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero (by decide)
  push_cast at h
  rw [dK, div_eq_iff c121666_ne_zero]
  linear_combination (-1 : K) * h

/-- **`d` is not a square mod `p`** (Euler's criterion: `d^((p−1)/2) = −1`, by kernel
square-and-multiply). -/
theorem dK_not_isSquare : ¬ IsSquare dK := by
  rw [dK_eq_natCast]
  have hne : ((dNat : ℕ) : K) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    decide
  rw [ZMod.euler_criterion _ hne]
  have h : powMod dNat (FieldDag.modulus / 2) FieldDag.modulus = FieldDag.modulus - 1 := by
    decide +kernel
  rw [zmod_pow_eq_powMod dNat _ (by decide), h, Nat.cast_sub (by decide), ZMod.natCast_self,
    Nat.cast_one, zero_sub]
  exact ZMod.neg_one_ne_one

/-- **`−1` is a square mod `p`** (`p ≡ 1 mod 4`): `sqrtMinusOne² = −1`. -/
theorem neg_one_isSquare : IsSquare (-1 : K) :=
  ⟨(EdwardsAffine.sqrtMinusOne : K), zmod_sqrtMinusOne_sq.symm⟩

/-- **The Ed25519 addition law is complete.** -/
instance complete_dK : Complete dK := ⟨two_ne_zero_K, neg_one_isSquare, dK_not_isSquare⟩

/-- The points of `−x² + y² = 1 + d·x²·y²` over `ZMod (2²⁵⁵ − 19)`: a commutative group. -/
abbrev Curve := Point dK

/-! ### The main package's affine formulas -/

section Bridge
open FieldDag EdwardsAffine EdwardsHinted

/-- The pair of field values `v` is the curve point `P`. -/
def Affine (v : Value) (P : Curve) : Prop := toZMod v.1 = P.x ∧ toZMod v.2 = P.y

theorem scaled_div {c N D X : K} (hc : c ≠ 0) (hD : D ≠ 0) (h : X = c * D) :
    c * N * X⁻¹ = N / D := by
  subst h
  field_simp

/-- **`EdwardsAffine.pointAddValue` is the group law** on curve points. -/
theorem affine_pointAddValue {p q : Value} {P Q : Curve} (hp : Affine p P) (hq : Affine q Q) :
    Affine (pointAddValue p q) (P + Q) := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  constructor
  · simp only [pointAddValue, toZMod_mul, toZMod_add, toZMod_sub, toZMod_inverse, toZMod_ofNat,
      hp1, hp2, hq1, hq2, Nat.cast_ofNat]
    rw [Point.add_x]
    exact scaled_div c121666_ne_zero (Point.denom_x_ne_zero P Q)
      (by linear_combination (-(P.x * Q.x * (P.y * Q.y))) * dK_mul)
  · simp only [pointAddValue, toZMod_mul, toZMod_add, toZMod_inverse, toZMod_ofNat,
      hp1, hp2, hq1, hq2, Nat.cast_ofNat]
    rw [Point.add_y]
    exact scaled_div c121666_ne_zero (Point.denom_y_ne_zero P Q)
      (by linear_combination (P.x * Q.x * (P.y * Q.y)) * dK_mul)

/-- The neutral element of the programs, `(0, 1)`, is the group's zero. -/
theorem affine_neutral : Affine (ofNat 0, ofNat 1) (0 : Curve) :=
  ⟨toZMod_ofNat_zero, toZMod_ofNat_one⟩

/-- **`EdwardsHinted.negate` (`(0 − x, y)`) is the group negation.** -/
theorem affine_neg {v : Value} {P : Curve} (hp : Affine v P) : Affine (ofNat 0 - v.1, v.2) (-P) :=
  ⟨by rw [toZMod_sub, toZMod_ofNat_zero, zero_sub, hp.1]; rfl, hp.2⟩

theorem negate_eval (input : ℕ → F) (p : EdwardsAffine.Point) :
    evalPoint input (negate p) = (ofNat 0 - (evalPoint input p).1, (evalPoint input p).2) := rfl

/-- `EdwardsHinted.curveCheck` on values: `121666·(y² − x² − 1) + 121665·x²·y²`. -/
def curveCheckValue (v : Value) : F :=
  ofNat 121666 * (v.2 * v.2 - v.1 * v.1 - ofNat 1) + ofNat 121665 * (v.1 * v.1 * (v.2 * v.2))

theorem curveCheck_eval (input : ℕ → F) (p : EdwardsAffine.Point) :
    (curveCheck p).eval input = curveCheckValue (evalPoint input p) := rfl

/-- **`curveCheck` is zero exactly on the curve.** -/
theorem curveCheckValue_zero_iff (v : Value) :
    curveCheckValue v = ofNat 0 ↔ OnCurve dK (toZMod v.1) (toZMod v.2) := by
  rw [← toZMod_eq_iff, toZMod_ofNat_zero]
  simp only [curveCheckValue, toZMod_mul, toZMod_add, toZMod_sub, toZMod_ofNat, Nat.cast_ofNat,
    Nat.cast_one]
  generalize toZMod v.1 = x
  generalize toZMod v.2 = y
  unfold OnCurve
  constructor
  · intro h
    have h1 : (121666 : K) * (-x ^ 2 + y ^ 2 - (1 + dK * x ^ 2 * y ^ 2)) = 0 := by
      linear_combination h - x ^ 2 * y ^ 2 * dK_mul
    have h2 := (mul_eq_zero.mp h1).resolve_left c121666_ne_zero
    linear_combination h2
  · intro h
    linear_combination (121666 : K) * h + x ^ 2 * y ^ 2 * dK_mul

/-- **`curveCheck` is zero exactly when the pair is a point of the group.** -/
theorem curveCheckValue_zero_iff_exists (v : Value) :
    curveCheckValue v = ofNat 0 ↔ ∃ P : Curve, Affine v P := by
  rw [curveCheckValue_zero_iff]
  constructor
  · intro h
    exact ⟨⟨_, _, h⟩, rfl, rfl⟩
  · rintro ⟨P, h1, h2⟩
    rw [h1, h2]
    exact P.on

/-! ### Extended coordinates -/

/-- The four coordinates of an `ExtV`, in `ZMod p`. -/
def tup (e : ExtV) : K × K × K × K := (toZMod e.x, toZMod e.y, toZMod e.z, toZMod e.t)

/-- The extended value `e` represents the curve point `P`: `Z ≠ 0`, `X = x·Z`, `Y = y·Z`,
`T = x·y·Z`. -/
def ExtRep (e : ExtV) (P : Curve) : Prop := Rep4 (tup e) P

theorem tup_extAddValue (p q : ExtV) :
    tup (extAddValue p q) = Edwards.extAdd 121666 121665 (tup p) (tup q) := by
  simp only [tup, extAddValue, Edwards.extAdd, toZMod_mul, toZMod_add, toZMod_sub, toZMod_ofNat,
    Nat.cast_ofNat]
  norm_num

/-- **`EdwardsHinted.extAddValue` is the group law** in extended coordinates (in particular the
`Z` of the result is nonzero, so `toAffine` never divides by zero on curve points). -/
theorem extRep_extAddValue {p q : ExtV} {P Q : Curve} (hp : ExtRep p P) (hq : ExtRep q Q) :
    ExtRep (extAddValue p q) (P + Q) := by
  unfold ExtRep
  rw [tup_extAddValue]
  exact rep4_add c121666_ne_zero dK_mul hp hq

theorem extRep_ofAffineValue {v : Value} {P : Curve} (hp : Affine v P) :
    ExtRep (ofAffineValue v) P := by
  simp [ExtRep, tup, ofAffineValue, Rep4, toZMod_mul, toZMod_ofNat_one, hp.1, hp.2]

theorem extRep_neutralValue : ExtRep neutralValue (0 : Curve) := by
  simp [ExtRep, tup, neutralValue, Rep4, toZMod_ofNat_one, toZMod_ofNat_zero]

/-- **`toAffineValue` of a representative is the point.** -/
theorem affine_toAffineValue {e : ExtV} {P : Curve} (he : ExtRep e P) :
    Affine (toAffineValue e) P := by
  obtain ⟨hz, hx, hy, -⟩ := he
  simp only [tup] at hz hx hy
  constructor
  · simp only [toAffineValue, toZMod_mul, toZMod_inverse]
    rw [hx, mul_inv_cancel_right₀ hz]
  · simp only [toAffineValue, toZMod_mul, toZMod_inverse]
    rw [hy, mul_inv_cancel_right₀ hz]

end Bridge

/-! ### Balanced sums (`sumTree`, `extSum`) are the group sum -/

section Tree
open EdwardsAffine

variable {α G : Type} [AddCommMonoid G]

theorem pairUp_rel (Rel : α → G → Prop) (f : α → α → α)
    (hf : ∀ a b g h, Rel a g → Rel b h → Rel (f a b) (g + h)) :
    ∀ l : List (α × G), (∀ a ∈ l, Rel a.1 a.2) →
      ∃ l' : List (α × G), (∀ a ∈ l', Rel a.1 a.2) ∧ l'.map Prod.fst = pairUp f (l.map Prod.fst) ∧
        (l'.map Prod.snd).sum = (l.map Prod.snd).sum ∧ l'.length = (l.length + 1) / 2
  | [], _ => ⟨[], by simp, rfl, rfl, by simp⟩
  | [a], h => ⟨[a], h, rfl, rfl, by simp⟩
  | a :: b :: rest, h => by
    obtain ⟨l', h1, h2, h3, h4⟩ := pairUp_rel Rel f hf rest (fun x hx => h x (by simp [hx]))
    refine ⟨(f a.1 b.1, a.2 + b.2) :: l', ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hf _ _ _ _ (h a (by simp)) (h b (by simp))
      · exact h1 x hx
    · simp [pairUp, h2]
    · simp [h3, add_assoc]
    · simp only [List.length_cons, h4]
      omega

theorem reduce_rel (Rel : α → G → Prop) (f : α → α → α)
    (hf : ∀ a b g h, Rel a g → Rel b h → Rel (f a b) (g + h)) :
    ∀ (n : ℕ) (l : List (α × G)), (∀ a ∈ l, Rel a.1 a.2) → l.length ≤ n + 1 →
      ∃ l' : List (α × G), (∀ a ∈ l', Rel a.1 a.2) ∧
        l'.map Prod.fst = reduce f n (l.map Prod.fst) ∧
        (l'.map Prod.snd).sum = (l.map Prod.snd).sum ∧ l'.length ≤ 1
  | 0, l, h, hl => ⟨l, h, rfl, rfl, hl⟩
  | n + 1, l, h, hl => by
    obtain ⟨l1, a1, a2, a3, a4⟩ := pairUp_rel Rel f hf l h
    obtain ⟨l2, b1, b2, b3, b4⟩ := reduce_rel Rel f hf n l1 a1 (by omega)
    refine ⟨l2, b1, ?_, b3.trans a3, b4⟩
    rw [b2, a2]
    rfl

/-- A balanced sum (`reduce f |l| l`, then the head or the neutral element) of related values is
related to the sum. -/
theorem tree_rel (Rel : α → G → Prop) (f : α → α → α)
    (hf : ∀ a b g h, Rel a g → Rel b h → Rel (f a b) (g + h)) (neutral : α) (hn : Rel neutral 0)
    (l : List (α × G)) (h : ∀ a ∈ l, Rel a.1 a.2) :
    Rel (((reduce f (l.map Prod.fst).length (l.map Prod.fst)).head?).getD neutral)
      (l.map Prod.snd).sum := by
  obtain ⟨l', h1, h2, h3, h4⟩ := reduce_rel Rel f hf l.length l h (Nat.le_succ _)
  rw [List.length_map, ← h2, ← h3]
  match l', h1, h4 with
  | [], _, _ => simpa using hn
  | [a], h1, _ => simpa using h1 a (by simp)
  | _ :: _ :: _, _, h4 => simp at h4

end Tree

section Sums
open FieldDag EdwardsAffine EdwardsHinted

/-- **`EdwardsAffine.sumTreeValue` of curve points is their group sum.** -/
theorem affine_sumTreeValue (l : List (Value × Curve)) (h : ∀ a ∈ l, Affine a.1 a.2) :
    Affine (sumTreeValue (l.map Prod.fst)) (l.map Prod.snd).sum :=
  tree_rel Affine pointAddValue (fun _ _ _ _ => affine_pointAddValue) _ affine_neutral l h

/-- **`EdwardsHinted.extSumValue` of represented points represents their group sum.** -/
theorem extRep_extSumValue (l : List (ExtV × Curve)) (h : ∀ a ∈ l, ExtRep a.1 a.2) :
    ExtRep (extSumValue (l.map Prod.fst)) (l.map Prod.snd).sum :=
  tree_rel ExtRep extAddValue (fun _ _ _ _ => extRep_extAddValue) _ extRep_neutralValue l h

end Sums

/-! ### "A square means a curve point" -/

section Lift
open FieldDag EdwardsAffine

/-- `x² = 121666·(y² − 1)/(121666 − 121665·y²)` puts `(x, y)` on the curve (the denominator is
never zero: `d` is not a square). -/
theorem onCurve_of_sq {X Y : K}
    (h : X * X = 121666 * (Y * Y - 1) * (121666 - 121665 * (Y * Y))⁻¹) : OnCurve dK X Y := by
  have hW : (121666 : K) - 121665 * (Y * Y) = 121666 * (1 + dK * Y ^ 2) := by
    linear_combination (-(Y * Y)) * dK_mul
  have hne : (121666 : K) - 121665 * (Y * Y) ≠ 0 := by
    rw [hW]
    exact mul_ne_zero c121666_ne_zero (one_add_d_sq_ne_zero Y)
  have h3 : X * X * (121666 - 121665 * (Y * Y)) = 121666 * (Y * Y - 1) := by
    rw [h, mul_assoc, inv_mul_cancel₀ hne, mul_one]
  have h4 : (121666 : K) * (-X ^ 2 + Y ^ 2 - (1 + dK * X ^ 2 * Y ^ 2)) = 0 := by
    linear_combination (-1 : K) * h3 - X ^ 2 * Y ^ 2 * dK_mul
  have h5 := (mul_eq_zero.mp h4).resolve_left c121666_ne_zero
  unfold OnCurve
  linear_combination h5

/-- **When `recipient`'s check value is zero, its output is a point of the curve group** (which
of the two roots `±x` is whatever the formula gives). -/
theorem recipient_onCurve (u : Expr) (input : ℕ → F)
    (h : (recipient u).2.eval input = ofNat 0) :
    ∃ P : Curve, Affine (evalPoint input (recipient u).1) P := by
  have hx := congrArg toZMod (recipient_x_mul_self u input h)
  have hy := (recipient_eval u input).2.1
  show ∃ P : Curve, Affine ((recipient u).1.1.eval input, (recipient u).1.2.eval input) P
  rw [hy]
  generalize (recipient u).1.1.eval input = x at hx
  refine ⟨⟨toZMod x, toZMod (recY (u.eval input)), ?_⟩, rfl, rfl⟩
  apply onCurve_of_sq
  rw [toZMod_mul] at hx
  rw [hx]
  simp only [recXX, toZMod_mul, toZMod_sub, toZMod_inverse, toZMod_ofNat, Nat.cast_ofNat,
    Nat.cast_one]

end Lift

section Recover
open FieldDag Signal.XEdDsaField

/-- **When `recover` reports `valid = 1`, its `(x, y)` is a point of the curve group.** -/
theorem recover_onCurve (U valid x y : F) (h : recover X25519.concrete U = [valid, x, y])
    (hv : valid = ofNat 1) : ∃ P : Curve, toZMod x = P.x ∧ toZMod y = P.y := by
  have hx := congrArg toZMod (recover_x_mul_self_of_valid U valid x y h hv)
  have hy := recover_y U valid x y h
  have hV := toZMod_ne_zero ((recover_valid_iff U valid x y h).mp hv).2.1
  rw [hy]
  clear h hy
  refine ⟨⟨toZMod x, toZMod (xedY U), ?_⟩, rfl, rfl⟩
  have hVe : toZMod (xedV U) = dK * (toZMod (xedY U) * toZMod (xedY U)) + 1 := by
    rw [xedV, toZMod_add, toZMod_mul, toZMod_mul, toZMod_ofNat, toZMod_ofNat_one, dK_eq_natCast,
      dNat_eq]
  rw [toZMod_mul, xedXX, toZMod_mul, toZMod_inverse, toZMod_sub, toZMod_mul, toZMod_ofNat_one] at hx
  have h3 : toZMod x * toZMod x * toZMod (xedV U) = toZMod (xedY U) * toZMod (xedY U) - 1 := by
    rw [hx, mul_assoc, inv_mul_cancel₀ hV, mul_one]
  rw [hVe] at h3
  unfold OnCurve
  linear_combination (-1 : K) * h3

end Recover

end TlsMpcProofs.Ed25519
