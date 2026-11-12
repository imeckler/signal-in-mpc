import TlsMpcProofs.EdwardsPoly
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The twisted Edwards curve `−x² + y² = 1 + d·x²·y²` is a commutative group

For any field `K` in which `2 ≠ 0`, `−1` is a square and `d` is not a square (`Complete d`):

* `sq_delta_ne_one`: **completeness** (Bernstein–Lange): for two curve points,
  `(d·x₁x₂y₁y₂)² ≠ 1`, so neither denominator `1 ± d·x₁x₂y₁y₂` of the addition law vanishes.
* `Point d`: the curve points; `Point.add` (the unified addition law), `Point.neg` (`(−x, y)`),
  `Point.zero` (`(0, 1)`).
* closure (`add_onCurve`, from `closure_poly`), commutativity, identity, inverse, and
  **associativity** (`Point.add_assoc'`, from `assoc_x_poly` / `assoc_y_poly`: the direct polynomial
  identity modulo the three curve equations, with explicit cofactors).
* `instAddCommGroup : AddCommGroup (Point d)`.

Nothing here is specific to Curve25519; `EdwardsEd25519.lean` instantiates `K = ZMod (2²⁵⁵ − 19)`,
`d = −121665/121666`.
-/

namespace TlsMpcProofs.Edwards

variable {K : Type*} [Field K]

/-- The curve equation (twisted Edwards, `a = −1`). -/
@[reducible] def OnCurve (d x y : K) : Prop := -x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2

/-- What makes the addition law complete: `2 ≠ 0`, `−1` a square, `d` not a square. -/
class Complete (d : K) : Prop where
  two_ne_zero : (2 : K) ≠ 0
  neg_one_isSquare : IsSquare (-1 : K)
  not_isSquare : ¬ IsSquare d

/-- **Completeness** (Bernstein–Lange, "Faster addition and doubling on elliptic curves",
Theorem 3.3, for `a = −1 = i²`): on curve points `d·x₁x₂y₁y₂` is neither `1` nor `−1`. -/
theorem sq_delta_ne_one {d : K} [hc : Complete d] {x1 y1 x2 y2 : K}
    (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2) : (d * x1 * x2 * y1 * y2) ^ 2 ≠ 1 := by
  intro hε
  obtain ⟨i, hi⟩ := hc.neg_one_isSquare
  have hne : d * x1 * x2 * y1 * y2 ≠ 0 := by
    intro h0
    rw [h0] at hε
    simp at hε
  have hx1 : x1 ≠ 0 := by rintro rfl; exact hne (by ring)
  have hy1 : y1 ≠ 0 := by rintro rfl; exact hne (by ring)
  have hy2 : y2 ≠ 0 := by rintro rfl; exact hne (by ring)
  have key : ∀ s : K, s ^ 2 = 1 →
      (i * x1 + s * (d * x1 * x2 * y1 * y2) * y1) ^ 2 = d * (x1 * y1 * (i * x2 + s * y2)) ^ 2 := by
    intro s hs
    linear_combination (-(x1 ^ 2 - d * x1 ^ 2 * y1 ^ 2 * x2 ^ 2)) * hi +
      ((d * x1 * x2 * y1 * y2) ^ 2 * y1 ^ 2 - d * x1 ^ 2 * y1 ^ 2 * y2 ^ 2) * hs +
      (y1 ^ 2 - 1) * hε + h1 - d * x1 ^ 2 * y1 ^ 2 * h2
  have hzero : ∀ s : K, s ^ 2 = 1 → i * x2 + s * y2 = 0 := by
    intro s hs
    by_contra hnz
    apply hc.not_isSquare
    have hb : x1 * y1 * (i * x2 + s * y2) ≠ 0 := mul_ne_zero (mul_ne_zero hx1 hy1) hnz
    refine ⟨(i * x1 + s * (d * x1 * x2 * y1 * y2) * y1) / (x1 * y1 * (i * x2 + s * y2)), ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb hb)]
    linear_combination (-1 : K) * key s hs
  have ha := hzero 1 (one_pow 2)
  have hb := hzero (-1) (by ring)
  have h2y : 2 * y2 = 0 := by linear_combination ha - hb
  rcases mul_eq_zero.mp h2y with h | h
  · exact hc.two_ne_zero h
  · exact hy2 h

theorem one_add_delta_ne_zero {d : K} [Complete d] {x1 y1 x2 y2 : K}
    (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2) : 1 + d * x1 * x2 * y1 * y2 ≠ 0 := by
  intro h
  apply sq_delta_ne_one h1 h2
  linear_combination (d * x1 * x2 * y1 * y2 - 1) * h

theorem one_sub_delta_ne_zero {d : K} [Complete d] {x1 y1 x2 y2 : K}
    (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2) : 1 - d * x1 * x2 * y1 * y2 ≠ 0 := by
  intro h
  apply sq_delta_ne_one h1 h2
  linear_combination (-(d * x1 * x2 * y1 * y2) - 1) * h

/-- A pair of fractions is on the curve when the cleared equation holds. -/
theorem onCurve_div {d X Y Dx Dy : K} (hx : Dx ≠ 0) (hy : Dy ≠ 0)
    (poly : -X ^ 2 * Dy ^ 2 + Y ^ 2 * Dx ^ 2 = Dx ^ 2 * Dy ^ 2 + d * X ^ 2 * Y ^ 2) :
    OnCurve d (X / Dx) (Y / Dy) := by
  unfold OnCurve
  field_simp
  linear_combination poly

/-- `1 + d·y²` never vanishes (so `x² = (y² − 1)/(1 + d·y²)` is always defined). -/
theorem one_add_d_sq_ne_zero {d : K} [hc : Complete d] (y : K) : 1 + d * y ^ 2 ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := hc.neg_one_isSquare
  have hy : y ≠ 0 := by
    rintro rfl
    simp at h
  apply hc.not_isSquare
  refine ⟨i / y, ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy hy)]
  linear_combination h + hi

/-- **Closure:** the sum of two curve points is on the curve. -/
theorem add_onCurve {d : K} [Complete d] {x1 y1 x2 y2 : K}
    (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2) :
    OnCurve d ((x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2))
      ((y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2)) := by
  exact onCurve_div (one_add_delta_ne_zero h1 h2) (one_sub_delta_ne_zero h1 h2)
    (closure_poly d x1 y1 x2 y2 h1 h2)

/-! Clearing the denominators of a nested sum (pure field identities, no curve equation). -/

theorem scale_numL {X Y Dx Dy a b : K} (hx : Dx ≠ 0) (hy : Dy ≠ 0) :
    (X / Dx * a + Y / Dy * b) * (Dx * Dy) = X * Dy * a + Y * Dx * b := by
  field_simp

theorem scale_numL' {X Y Dx Dy a b : K} (hx : Dx ≠ 0) (hy : Dy ≠ 0) :
    (Y / Dy * a + X / Dx * b) * (Dx * Dy) = Y * Dx * a + X * Dy * b := by
  field_simp

theorem scale_denL {d X Y Dx Dy a b : K} (hx : Dx ≠ 0) (hy : Dy ≠ 0) :
    (1 + d * (X / Dx) * a * (Y / Dy) * b) * (Dx * Dy) = Dx * Dy + d * X * Y * a * b := by
  field_simp

theorem scale_denL' {d X Y Dx Dy a b : K} (hx : Dx ≠ 0) (hy : Dy ≠ 0) :
    (1 - d * (X / Dx) * a * (Y / Dy) * b) * (Dx * Dy) = Dx * Dy - d * X * Y * a * b := by
  field_simp

theorem scale_numR {X Y Dx Dy a b : K} (hx : Dx ≠ 0) (hy : Dy ≠ 0) :
    (a * (Y / Dy) + b * (X / Dx)) * (Dx * Dy) = a * Y * Dx + b * X * Dy := by
  field_simp

theorem scale_denR {d X Y Dx Dy a b : K} (hx : Dx ≠ 0) (hy : Dy ≠ 0) :
    (1 + d * a * (X / Dx) * b * (Y / Dy)) * (Dx * Dy) = Dx * Dy + d * a * b * X * Y := by
  field_simp

theorem scale_denR' {d X Y Dx Dy a b : K} (hx : Dx ≠ 0) (hy : Dy ≠ 0) :
    (1 - d * a * (X / Dx) * b * (Y / Dy)) * (Dx * Dy) = Dx * Dy - d * a * b * X * Y := by
  field_simp

/-- Two fractions are equal when their numerators and denominators, each scaled by a nonzero
factor, satisfy the cross-multiplied identity. -/
theorem div_eq_div_of_scaled {A B C D m n NL DL NR DR : K} (hm : m ≠ 0) (hn : n ≠ 0)
    (hB : B ≠ 0) (hD : D ≠ 0) (eA : A * m = NL) (eB : B * m = DL) (eC : C * n = NR)
    (eD : D * n = DR) (poly : NL * DR = NR * DL) : A / B = C / D := by
  rw [div_eq_div_iff hB hD]
  apply mul_right_cancel₀ (mul_ne_zero hm hn)
  rw [← eA, ← eB, ← eC, ← eD] at poly
  linear_combination poly

/-- **Associativity, x-coordinate**, as a statement about field elements. -/
theorem assoc_x {d : K} [Complete d] {x1 y1 x2 y2 x3 y3 : K}
    (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2) (h3 : OnCurve d x3 y3) :
    ((x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2) * y3 +
        (y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2) * x3) /
      (1 + d * ((x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2)) * x3 *
        ((y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2)) * y3) =
    (x1 * ((y2 * y3 + x2 * x3) / (1 - d * x2 * x3 * y2 * y3)) +
        y1 * ((x2 * y3 + y2 * x3) / (1 + d * x2 * x3 * y2 * y3))) /
      (1 + d * x1 * ((x2 * y3 + y2 * x3) / (1 + d * x2 * x3 * y2 * y3)) * y1 *
        ((y2 * y3 + x2 * x3) / (1 - d * x2 * x3 * y2 * y3))) := by
  have p12 := one_add_delta_ne_zero h1 h2
  have m12 := one_sub_delta_ne_zero h1 h2
  have p23 := one_add_delta_ne_zero h2 h3
  have m23 := one_sub_delta_ne_zero h2 h3
  have hL := one_add_delta_ne_zero (add_onCurve h1 h2) h3
  have hR := one_add_delta_ne_zero h1 (add_onCurve h2 h3)
  refine div_eq_div_of_scaled (mul_ne_zero p12 m12) (mul_ne_zero p23 m23) hL hR ?_ ?_ ?_ ?_
    (assoc_x_poly d x1 y1 x2 y2 x3 y3 h1 h2 h3)
  · exact scale_numL p12 m12
  · exact scale_denL p12 m12
  · exact scale_numR p23 m23
  · exact scale_denR p23 m23

/-- **Associativity, y-coordinate.** -/
theorem assoc_y {d : K} [Complete d] {x1 y1 x2 y2 x3 y3 : K}
    (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2) (h3 : OnCurve d x3 y3) :
    ((y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2) * y3 +
        (x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2) * x3) /
      (1 - d * ((x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2)) * x3 *
        ((y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2)) * y3) =
    (y1 * ((y2 * y3 + x2 * x3) / (1 - d * x2 * x3 * y2 * y3)) +
        x1 * ((x2 * y3 + y2 * x3) / (1 + d * x2 * x3 * y2 * y3))) /
      (1 - d * x1 * ((x2 * y3 + y2 * x3) / (1 + d * x2 * x3 * y2 * y3)) * y1 *
        ((y2 * y3 + x2 * x3) / (1 - d * x2 * x3 * y2 * y3))) := by
  have p12 := one_add_delta_ne_zero h1 h2
  have m12 := one_sub_delta_ne_zero h1 h2
  have p23 := one_add_delta_ne_zero h2 h3
  have m23 := one_sub_delta_ne_zero h2 h3
  have hL := one_sub_delta_ne_zero (add_onCurve h1 h2) h3
  have hR := one_sub_delta_ne_zero h1 (add_onCurve h2 h3)
  refine div_eq_div_of_scaled (mul_ne_zero p12 m12) (mul_ne_zero p23 m23) hL hR ?_ ?_ ?_ ?_
    (assoc_y_poly d x1 y1 x2 y2 x3 y3 h1 h2 h3)
  · exact scale_numL' p12 m12
  · exact scale_denL' p12 m12
  · exact scale_numR p23 m23
  · exact scale_denR' p23 m23

/-! ### The points and the group -/

/-- A point of the curve with parameter `d`. -/
@[ext] structure Point (d : K) where
  x : K
  y : K
  on : OnCurve d x y

namespace Point

variable {d : K}

/-- The neutral element `(0, 1)`. -/
protected def zero : Point d := ⟨0, 1, by unfold OnCurve; ring⟩

/-- Negation: `−(x, y) = (−x, y)`. -/
protected def neg (P : Point d) : Point d := ⟨-P.x, P.y, by
  have h := P.on
  unfold OnCurve at h ⊢
  linear_combination h⟩

instance : Zero (Point d) := ⟨Point.zero⟩
instance : Neg (Point d) := ⟨Point.neg⟩

@[simp] theorem zero_x : (0 : Point d).x = 0 := rfl
@[simp] theorem zero_y : (0 : Point d).y = 1 := rfl
@[simp] theorem neg_x (P : Point d) : (-P).x = -P.x := rfl
@[simp] theorem neg_y (P : Point d) : (-P).y = P.y := rfl

variable [Complete d]

/-- The unified (complete) addition law. -/
protected def add (P Q : Point d) : Point d :=
  ⟨(P.x * Q.y + P.y * Q.x) / (1 + d * P.x * Q.x * P.y * Q.y),
   (P.y * Q.y + P.x * Q.x) / (1 - d * P.x * Q.x * P.y * Q.y), add_onCurve P.on Q.on⟩

instance : Add (Point d) := ⟨Point.add⟩

theorem add_x (P Q : Point d) :
    (P + Q).x = (P.x * Q.y + P.y * Q.x) / (1 + d * P.x * Q.x * P.y * Q.y) := rfl
theorem add_y (P Q : Point d) :
    (P + Q).y = (P.y * Q.y + P.x * Q.x) / (1 - d * P.x * Q.x * P.y * Q.y) := rfl

/-- The denominators of the addition law do not vanish (completeness). -/
theorem denom_x_ne_zero (P Q : Point d) : 1 + d * P.x * Q.x * P.y * Q.y ≠ 0 :=
  one_add_delta_ne_zero P.on Q.on
theorem denom_y_ne_zero (P Q : Point d) : 1 - d * P.x * Q.x * P.y * Q.y ≠ 0 :=
  one_sub_delta_ne_zero P.on Q.on

/-- **Commutativity.** -/
protected theorem add_comm' (P Q : Point d) : P + Q = Q + P := by
  apply Point.ext
  · rw [add_x, add_x]; ring
  · rw [add_y, add_y]; ring

/-- **Identity.** -/
protected theorem zero_add' (P : Point d) : 0 + P = P := by
  apply Point.ext
  · rw [add_x]; simp
  · rw [add_y]; simp

/-- **Inverse.** -/
protected theorem neg_add_cancel' (P : Point d) : -P + P = 0 := by
  apply Point.ext
  · rw [add_x, neg_x, neg_y, zero_x, div_eq_zero_iff]
    left; ring
  · rw [add_y, zero_y, div_eq_one_iff_eq (denom_y_ne_zero (-P) P), neg_x, neg_y]
    have h := P.on
    unfold OnCurve at h
    linear_combination h

/-- **Associativity** (route (a): the polynomial identities `assoc_x_poly`, `assoc_y_poly`). -/
protected theorem add_assoc' (P Q R : Point d) : P + Q + R = P + (Q + R) := by
  apply Point.ext
  · exact assoc_x P.on Q.on R.on
  · exact assoc_y P.on Q.on R.on

/-- **The curve points form a commutative group** under the unified addition law. -/
instance instAddCommGroup : AddCommGroup (Point d) where
  add_assoc := Point.add_assoc'
  zero_add := Point.zero_add'
  add_zero := fun P => by rw [Point.add_comm', Point.zero_add']
  neg_add_cancel := Point.neg_add_cancel'
  add_comm := Point.add_comm'
  nsmul := nsmulRec
  zsmul := zsmulRec

end Point

/-! ### Extended coordinates `(X, Y, Z, T)`, `x = X/Z`, `y = Y/Z`, `T = X·Y/Z`

The division-free unified addition (Hisil–Wong–Carter–Dawson, `a = −1`), with every coordinate
scaled by `c²` for a nonzero `c` with `d·c = −c'` (the main package uses `c = 121666`,
`c' = 121665`), computes the group law. -/

section Extended

variable {d : K} [Complete d]

/-- `(X, Y, Z, T)` represents the curve point `P`: `Z ≠ 0`, `X = x·Z`, `Y = y·Z`, `T = x·y·Z`. -/
def Rep4 (e : K × K × K × K) (P : Point d) : Prop :=
  e.2.2.1 ≠ 0 ∧ e.1 = P.x * e.2.2.1 ∧ e.2.1 = P.y * e.2.2.1 ∧ e.2.2.2 = P.x * P.y * e.2.2.1

/-- The extended addition, as the main package's `EdwardsHinted.extAddValue` computes it. -/
def extAdd (c c' : K) (p q : K × K × K × K) : K × K × K × K :=
  let a := (p.2.1 - p.1) * (q.2.1 - q.1)
  let b := (p.2.1 + p.1) * (q.2.1 + q.1)
  let cc := 2 * c' * (p.2.2.2 * q.2.2.2)
  let dd := 2 * c * (p.2.2.1 * q.2.2.1)
  let e := c * (b - a)
  let h := c * (b + a)
  let f := dd + cc
  let g := dd - cc
  (e * f, g * h, f * g, e * h)

omit [Complete d] in
theorem rep4_zero : Rep4 ((0, 1, 1, 0) : K × K × K × K) (0 : Point d) := by
  simp [Rep4]

/-- **The extended addition computes the group law** (and its `Z` never vanishes). -/
theorem rep4_add {c c' : K} (hc : c ≠ 0) (hdc : d * c = -c') {p q : K × K × K × K}
    {P Q : Point d} (hp : Rep4 p P) (hq : Rep4 q Q) : Rep4 (extAdd c c' p q) (P + Q) := by
  obtain ⟨x1, y1, z1, t1⟩ := p
  obtain ⟨x2, y2, z2, t2⟩ := q
  obtain ⟨hz1, hx1, hy1, ht1⟩ := hp
  obtain ⟨hz2, hx2, hy2, ht2⟩ := hq
  simp only at hz1 hx1 hy1 ht1 hz2 hx2 hy2 ht2
  subst hx1 hy1 ht1 hx2 hy2 ht2
  have h2 := Complete.two_ne_zero (d := d)
  have hp' := Point.denom_x_ne_zero P Q
  have hm' := Point.denom_y_ne_zero P Q
  have hf : 2 * c * (z1 * z2) + 2 * c' * (P.x * P.y * z1 * (Q.x * Q.y * z2)) =
      2 * c * (z1 * z2) * (1 - d * P.x * Q.x * P.y * Q.y) := by
    linear_combination (2 * (z1 * z2) * (P.x * Q.x * P.y * Q.y)) * hdc
  have hg : 2 * c * (z1 * z2) - 2 * c' * (P.x * P.y * z1 * (Q.x * Q.y * z2)) =
      2 * c * (z1 * z2) * (1 + d * P.x * Q.x * P.y * Q.y) := by
    linear_combination (-(2 * (z1 * z2) * (P.x * Q.x * P.y * Q.y))) * hdc
  have hZ : 2 * c * (z1 * z2) ≠ 0 := mul_ne_zero (mul_ne_zero h2 hc) (mul_ne_zero hz1 hz2)
  simp only [Rep4, extAdd, Point.add_x, Point.add_y]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    have h : (2 * c * (z1 * z2) * (1 - d * P.x * Q.x * P.y * Q.y)) *
        (2 * c * (z1 * z2) * (1 + d * P.x * Q.x * P.y * Q.y)) = 0 := by
      linear_combination h0 -
        (2 * c * (z1 * z2) - 2 * c' * (P.x * P.y * z1 * (Q.x * Q.y * z2))) * hf -
        (2 * c * (z1 * z2) * (1 - d * P.x * Q.x * P.y * Q.y)) * hg
    exact mul_ne_zero (mul_ne_zero hZ hm') (mul_ne_zero hZ hp') h
  · rw [div_mul_eq_mul_div, eq_div_iff hp']
    linear_combination
      (-((2 * c * (z1 * z2) + 2 * c' * (P.x * P.y * z1 * (Q.x * Q.y * z2))) *
        (P.x * Q.y + P.y * Q.x))) * hg
  · rw [div_mul_eq_mul_div, eq_div_iff hm']
    linear_combination
      (-((2 * c * (z1 * z2) - 2 * c' * (P.x * P.y * z1 * (Q.x * Q.y * z2))) *
        (P.y * Q.y + P.x * Q.x))) * hf
  · rw [div_mul_div_comm, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hp' hm')]
    linear_combination
      (-((P.x * Q.y + P.y * Q.x) * (P.y * Q.y + P.x * Q.x) *
        (2 * c * (z1 * z2) - 2 * c' * (P.x * P.y * z1 * (Q.x * Q.y * z2))))) * hf +
      (-((P.x * Q.y + P.y * Q.x) * (P.y * Q.y + P.x * Q.x) * (2 * c * (z1 * z2)) *
        (1 - d * P.x * Q.x * P.y * Q.y))) * hg

/-- Double-and-add over `k` bits of `e`, most significant first (as `FieldBridge.powModAux`). -/
def extSmul (c c' : K) (b : K × K × K × K) (e : ℕ) : ℕ → K × K × K × K
  | 0 => (0, 1, 1, 0)
  | k + 1 =>
    if e % 2 = 1 then
      extAdd c c' (extAdd c c' (extSmul c c' b (e / 2) k) (extSmul c c' b (e / 2) k)) b
    else extAdd c c' (extSmul c c' b (e / 2) k) (extSmul c c' b (e / 2) k)

/-- **Double-and-add in extended coordinates computes the scalar multiple.** -/
theorem rep4_smul {c c' : K} (hc : c ≠ 0) (hdc : d * c = -c') {b : K × K × K × K} {P : Point d}
    (hb : Rep4 b P) : ∀ (k e : ℕ), e < 2 ^ k → Rep4 (extSmul c c' b e k) (e • P)
  | 0, e, he => by
    have h0 : e = 0 := by simpa using he
    subst h0
    rw [zero_nsmul]
    exact rep4_zero
  | k + 1, e, he => by
    have he' : e / 2 < 2 ^ k := by rw [pow_succ] at he; omega
    have ih := rep4_smul hc hdc hb k (e / 2) he'
    have hh := rep4_add hc hdc ih ih
    unfold extSmul
    split_ifs with h
    · have hP : e • P = (e / 2) • P + (e / 2) • P + P := by
        have h3 : e = e / 2 + e / 2 + 1 := by omega
        conv_lhs => rw [h3]
        rw [add_nsmul, add_nsmul, one_nsmul]
      rw [hP]
      exact rep4_add hc hdc hh hb
    · have hP : e • P = (e / 2) • P + (e / 2) • P := by
        have h3 : e = e / 2 + e / 2 := by omega
        conv_lhs => rw [h3]
        rw [add_nsmul]
      rw [hP]
      exact hh

omit [Complete d] in
/-- Reading the point off a representative. -/
theorem rep4_eq_zero {e : K × K × K × K} {P : Point d} (h : Rep4 e P) (hx : e.1 = 0)
    (hy : e.2.1 = e.2.2.1) : P = 0 := by
  obtain ⟨hz, h1, h2, -⟩ := h
  apply Point.ext
  · rw [hx] at h1
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hz
  · rw [hy] at h2
    have : (P.y - 1) * e.2.2.1 = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp this with h | h
    · rw [Point.zero_y]; linear_combination h
    · exact absurd h hz

end Extended

end TlsMpcProofs.Edwards
