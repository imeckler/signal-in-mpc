import TlsMpcProofs.EdwardsEd25519

/-!
# The X25519 ladder computes scalar multiplication in the Edwards group

The Montgomery `u`-coordinate of an Edwards point is `u = (1 + y)/(1 − y)` (`montU`);
projectively `(X : Z) = (1 + y : 1 − y)` (`MRep X Z P`), which also covers the neutral element
(`(1 : 0)`, the point at infinity) and `(0, −1)` (`(0 : 1)`).

* `mrep_double`: the ladder's doubling `(X : Z) ↦ ((X+Z)²(X−Z)² : E·((X+Z)² + c'·E))`,
  `E = (X+Z)² − (X−Z)²`, maps a representative of `P` to one of `P + P` (for `d·c = −c'`,
  `c = c' + 1`, i.e. Montgomery `A = 4c' + 2`, `d = −(A−2)/(A+2)`).
* `mrep_diffadd`: the differential addition maps representatives of `Q`, `R` and the affine
  `u ≠ 0` of `R − Q` to a representative of `Q + R`.
  Both are proved in Edwards coordinates from `mont_double_poly` / `mont_diffadd_poly`, with all
  degenerate cases (infinity, 2- and 4-torsion) included; only `u ≠ 0` is required.
* For the main package's `X25519` (`K = ZMod (2²⁵⁵ − 19)`, `c' = 121665`):
  `advance_inv`, `ladderSpec_inv` (the ladder state is `(n·P, (n+1)·P)` after the bits of `n`),
  and **`spec_eq_montU`**: for a curve point `P` with Montgomery coordinate `u ≠ 0`,
  `X25519.spec input u` is the Montgomery coordinate of `k·P` in the Edwards group, `k` the
  clamped scalar (`0` when `k·P` is the neutral element, as `x/0 = 0` in the program).

Not proved: inputs `u` that are not the coordinate of a curve point (points of the quadratic
twist), and `u = 0`; that `u ↦ (u, v)` lands on `v² = u³ + 486662u² + u` is not needed and not
stated.
-/

namespace TlsMpcProofs.Edwards

variable {K : Type*} [Field K] {d : K}

namespace Point

theorem sub_y [Complete d] (P Q : Point d) :
    (P - Q).y = (P.y * Q.y - P.x * Q.x) / (1 + d * P.x * Q.x * P.y * Q.y) := by
  rw [sub_eq_add_neg, add_y, neg_x, neg_y]
  congr 1 <;> ring

end Point

/-- `(X : Z)` is the projective Montgomery coordinate `(1 + y : 1 − y)` of the Edwards point `P`. -/
def MRep (X Z : K) (P : Point d) : Prop := ∃ l : K, l ≠ 0 ∧ X = l * (1 + P.y) ∧ Z = l * (1 - P.y)

/-- The affine Montgomery coordinate `(1 + y)/(1 − y)` (`0` at the neutral element, by `x/0 = 0`). -/
def montU (P : Point d) : K := (1 + P.y) / (1 - P.y)

theorem mrep_cross {X Z : K} {P : Point d} (h : MRep X Z P) : X * (1 - P.y) = Z * (1 + P.y) := by
  obtain ⟨l, -, rfl, rfl⟩ := h
  ring

theorem mrep_neg {X Z : K} {P : Point d} (h : MRep X Z P) : MRep X Z (-P) := h

theorem mrep_div {X Z : K} {P : Point d} (h : MRep X Z P) : X / Z = montU P := by
  obtain ⟨l, hl, rfl, rfl⟩ := h
  exact mul_div_mul_left _ _ hl

variable [Complete d]

theorem mrep_of_cross {X Z : K} {P : Point d} (h : X * (1 - P.y) = Z * (1 + P.y))
    (hne : X ≠ 0 ∨ Z ≠ 0) : MRep X Z P := by
  have h2 := Complete.two_ne_zero (d := d)
  by_cases hy : 1 - P.y = 0
  · have hy1 : P.y = 1 := by linear_combination -hy
    have hZ : Z = 0 := by
      rw [hy, mul_zero, hy1] at h
      have hZ2 : Z * 2 = 0 := by linear_combination -h
      exact (mul_eq_zero.mp hZ2).resolve_right h2
    have hX : X ≠ 0 := hne.resolve_right (not_not.mpr hZ)
    refine ⟨X / 2, div_ne_zero hX h2, ?_, ?_⟩
    · rw [hy1, show (1 : K) + 1 = 2 by norm_num, div_mul_cancel₀ _ h2]
    · rw [hy, mul_zero, hZ]
  · refine ⟨Z / (1 - P.y), ?_, ?_, ?_⟩
    · apply div_ne_zero _ hy
      intro hZ0
      rcases hne with hX | hZ
      · exact hX ((mul_eq_zero.mp (by rw [h, hZ0, zero_mul])).resolve_right hy)
      · exact hZ hZ0
    · rw [div_mul_eq_mul_div, eq_div_iff hy]
      exact h
    · rw [div_mul_cancel₀ _ hy]

theorem mrep_zero : MRep (1 : K) 0 (0 : Point d) := by
  have h2 := Complete.two_ne_zero (d := d)
  refine ⟨2⁻¹, inv_ne_zero h2, ?_, ?_⟩
  · rw [Point.zero_y, show (1 : K) + 1 = 2 by norm_num, inv_mul_cancel₀ h2]
  · rw [Point.zero_y, sub_self, mul_zero]

/-- The affine coordinate of a point other than the neutral element. -/
theorem mrep_montU {P : Point d} (hy : P.y ≠ 1) : MRep (montU P) 1 P := by
  have hy' : 1 - P.y ≠ 0 := fun h => hy (by linear_combination -h)
  apply mrep_of_cross
  · rw [montU, div_mul_cancel₀ _ hy', one_mul]
  · exact Or.inr one_ne_zero

/-- **Montgomery doubling is doubling in the Edwards group.** -/
theorem mrep_double {c c' : K} (hdc : d * c = -c') (hcc : c = c' + 1) {X Z : K} {P : Point d}
    (h : MRep X Z P) :
    MRep ((X + Z) * (X + Z) * ((X - Z) * (X - Z)))
      (((X + Z) * (X + Z) - (X - Z) * (X - Z)) *
        ((X + Z) * (X + Z) + c' * ((X + Z) * (X + Z) - (X - Z) * (X - Z)))) (P + P) := by
  obtain ⟨l, hl, rfl, rfl⟩ := h
  have h2 := Complete.two_ne_zero (d := d)
  have e2 : c * (1 + d) = 1 := by linear_combination hcc + hdc
  have hc : c ≠ 0 := by
    rintro rfl
    simp at e2
  have hDm := Point.denom_y_ne_zero P P
  apply mrep_of_cross
  · rw [Point.add_y, one_sub_div hDm, one_add_div hDm, mul_div_assoc', mul_div_assoc',
      div_left_inj' hDm]
    have poly := mont_double_poly d P.x P.y P.on
    have e1 : 1 + c' * (1 - P.y ^ 2) = c * (1 + d * P.y ^ 2) := by
      linear_combination (-1 : K) * hcc - P.y ^ 2 * hdc
    linear_combination (16 * l ^ 4 * c) * poly -
      (16 * l ^ 4 * P.y ^ 2 * ((1 - d * P.x * P.x * P.y * P.y) - (P.y * P.y + P.x * P.x))) * e2 -
      (16 * l ^ 4 * (1 - P.y ^ 2) * ((1 - d * P.x * P.x * P.y * P.y) + (P.y * P.y + P.x * P.x))) * e1
  · by_cases hy : P.y = 0
    · right
      intro h0
      apply mul_ne_zero (pow_ne_zero 4 (mul_ne_zero h2 hl)) hc
      rw [hy] at h0
      linear_combination h0 + (16 * l ^ 4) * hcc
    · left
      intro h0
      apply mul_ne_zero (pow_ne_zero 2 (mul_ne_zero h2 hl))
        (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero h2 hl) hy))
      linear_combination h0

/-- Clearing two denominators in the differential-addition identity. -/
theorem cross_div {S T n1 d1 n2 d2 : K} (h1 : d1 ≠ 0) (h2 : d2 ≠ 0)
    (poly : S * (d1 - n1) * (d2 - n2) = T * (d1 + n1) * (d2 + n2)) :
    S * (1 - n1 / d1) * (1 - n2 / d2) = T * (1 + n1 / d1) * (1 + n2 / d2) := by
  rw [one_sub_div h1, one_sub_div h2, one_add_div h1, one_add_div h2]
  field_simp
  linear_combination poly

/-- **Montgomery differential addition is addition in the Edwards group:** from `(X₂ : Z₂)` of
`Q`, `(X₃ : Z₃)` of `R` and the affine coordinate `u ≠ 0` of `R − Q`, the ladder's formulas give
a representative of `Q + R`. -/
theorem mrep_diffadd {X2 Z2 X3 Z3 u : K} {Q R : Point d} (hQ : MRep X2 Z2 Q) (hR : MRep X3 Z3 R)
    (hD : MRep u 1 (R - Q)) (hu : u ≠ 0) :
    MRep (((X3 - Z3) * (X2 + Z2) + (X3 + Z3) * (X2 - Z2)) *
        ((X3 - Z3) * (X2 + Z2) + (X3 + Z3) * (X2 - Z2)))
      (u * (((X3 - Z3) * (X2 + Z2) - (X3 + Z3) * (X2 - Z2)) *
        ((X3 - Z3) * (X2 + Z2) - (X3 + Z3) * (X2 - Z2)))) (Q + R) := by
  obtain ⟨l, hl, rfl, rfl⟩ := hQ
  obtain ⟨m, hm, rfl, rfl⟩ := hR
  obtain ⟨n, -, hu1, h1⟩ := hD
  have h2 := Complete.two_ne_zero (d := d)
  have hDS := Point.denom_y_ne_zero Q R
  have hDD := Point.denom_x_ne_zero R Q
  have hsub := Point.sub_y R Q
  generalize (R - Q).y = b at hu1 h1 hsub
  have FP : (Q.y + R.y) ^ 2 * (1 - (Q + R).y) * (1 - b) =
      (Q.y - R.y) ^ 2 * (1 + (Q + R).y) * (1 + b) := by
    rw [hsub, Point.add_y]
    exact cross_div hDS hDD (mont_diffadd_poly d Q.x Q.y R.x R.y Q.on R.on)
  have hlm : 2 * 2 * l * m ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) hl) hm
  apply mrep_of_cross
  · rw [hu1]
    linear_combination (16 * l ^ 2 * m ^ 2 * n) * FP +
      (16 * l ^ 2 * m ^ 2 * (Q.y + R.y) ^ 2 * (1 - (Q + R).y)) * h1
  · by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨hX0, hZ0⟩ := hcon
    have hs : Q.y + R.y = 0 := by
      have h3 : (2 * 2 * l * m * (Q.y + R.y)) ^ 2 = 0 := by linear_combination hX0
      exact (mul_eq_zero.mp (sq_eq_zero_iff.mp h3)).resolve_left hlm
    have ht : Q.y - R.y = 0 := by
      have h3 : u * (2 * 2 * l * m * (Q.y - R.y)) ^ 2 = 0 := by linear_combination hZ0
      have h4 := (mul_eq_zero.mp h3).resolve_left hu
      exact (mul_eq_zero.mp (sq_eq_zero_iff.mp h4)).resolve_left hlm
    have hyQ : Q.y = 0 := by
      have h3 : 2 * Q.y = 0 := by linear_combination hs + ht
      exact (mul_eq_zero.mp h3).resolve_left h2
    have hyR : R.y = 0 := by linear_combination hs - hyQ
    have hbv : b = -(R.x * Q.x) := by
      rw [hsub, hyQ, hyR]
      simp
    have hQon := Q.on
    have hRon := R.on
    unfold OnCurve at hQon hRon
    rw [hyQ] at hQon
    rw [hyR] at hRon
    have hbb : (b - 1) * (b + 1) = 0 := by
      rw [hbv]
      linear_combination (-(Q.x ^ 2)) * hRon + hQon
    rcases mul_eq_zero.mp hbb with h | h
    · have h10 : (1 : K) = 0 := by
        rw [h1]
        linear_combination (-n) * h
      exact one_ne_zero h10
    · exact hu (by rw [hu1]; linear_combination n * h)

end TlsMpcProofs.Edwards

/-! ### The main package's `X25519` ladder -/

namespace TlsMpcProofs.Ed25519
open TlsMpc Edwards X25519
open FieldDag (F)

/-- The ladder state holds `n·P` and `(n+1)·P` (as projective Montgomery coordinates). -/
def LadderInv (P : Curve) (s : Coordinates F) (n : ℕ) : Prop :=
  MRep (toZMod s.x2) (toZMod s.z2) (n • P) ∧ MRep (toZMod s.x3) (toZMod s.z3) ((n + 1) • P)

theorem swapSpec_xor (p b : Bool) (s : Coordinates F) :
    swapSpec (p ^^ b) s = swapSpec b (swapSpec p s) := by
  cases p <;> cases b <;> rfl

/-- **One ladder step** (`advance`) on representatives of `Q` and `R` with `R − Q = ±P`:
`(Q, R) ↦ (2Q, Q + R)`. -/
theorem advance_rep {u : F} {s : Coordinates F} {Q R : Curve}
    (hD : MRep (toZMod u) 1 (R - Q)) (hu : toZMod u ≠ 0)
    (hQ : MRep (toZMod s.x2) (toZMod s.z2) Q) (hR : MRep (toZMod s.x3) (toZMod s.z3) R) :
    MRep (toZMod (advance concrete u s).x2) (toZMod (advance concrete u s).z2) (Q + Q) ∧
      MRep (toZMod (advance concrete u s).x3) (toZMod (advance concrete u s).z3) (Q + R) := by
  simp only [advance, concrete, toZMod_mul, toZMod_add, toZMod_sub, toZMod_ofNat, Nat.cast_ofNat]
  exact ⟨mrep_double dK_mul (by norm_num) hQ, mrep_diffadd hQ hR hD hu⟩

/-- **One ladder iteration with its conditional swaps** keeps the invariant: after the bit `b`,
the state holds `(2n + b)·P` and `(2n + b + 1)·P`. -/
theorem advance_inv {u : F} {P : Curve} (hP : MRep (toZMod u) 1 P) (hu : toZMod u ≠ 0) (b : Bool)
    {s : Coordinates F} {n : ℕ} (h : LadderInv P s n) :
    LadderInv P (swapSpec b (advance concrete u (swapSpec b s))) (2 * n + b.toNat) := by
  obtain ⟨hQ, hR⟩ := h
  cases b
  · have hD : MRep (toZMod u) 1 ((n + 1) • P - n • P) := by
      rw [succ_nsmul, add_sub_cancel_left]
      exact hP
    obtain ⟨h1, h2⟩ := advance_rep hD hu hQ hR
    refine ⟨?_, ?_⟩
    · have e : (2 * n + false.toNat) • P = n • P + n • P := by
        rw [← add_nsmul]; congr 1; simp; omega
      rw [e]; exact h1
    · have e : (2 * n + false.toNat + 1) • P = n • P + (n + 1) • P := by
        rw [← add_nsmul]; congr 1; simp; omega
      rw [e]; exact h2
  · have hD : MRep (toZMod u) 1 (n • P - (n + 1) • P) := by
      rw [succ_nsmul, sub_add_cancel_left]
      exact mrep_neg hP
    obtain ⟨h1, h2⟩ := advance_rep (s := swapSpec true s) hD hu hR hQ
    refine ⟨?_, ?_⟩
    · have e : (2 * n + true.toNat) • P = (n + 1) • P + n • P := by
        rw [← add_nsmul]; congr 1; simp; omega
      rw [e]; exact h2
    · have e : (2 * n + true.toNat + 1) • P = (n + 1) • P + (n + 1) • P := by
        rw [← add_nsmul]; congr 1; simp; omega
      rw [e]; exact h1

/-- **The ladder invariant:** started from a state holding `(n·P, (n+1)·P)`, `ladderSpec` ends
holding `(m·P, (m+1)·P)` for `m` the big-endian value of the bits appended to `n`. -/
theorem ladderSpec_inv {u : F} {P : Curve} (hP : MRep (toZMod u) 1 P) (hu : toZMod u ≠ 0) :
    ∀ (bits : List Bool) (prev : Bool) (s : Coordinates F) (n : ℕ),
      LadderInv P (swapSpec prev s) n → LadderInv P (ladderSpec u prev s bits) (bitsValue n bits)
  | [], _, _, _, h => h
  | b :: rest, prev, s, n, h => by
    show LadderInv P (ladderSpec u b (advance concrete u (swapSpec (prev ^^ b) s)) rest)
      (bitsValue (2 * n + b.toNat) rest)
    apply ladderSpec_inv hP hu rest b _ (2 * n + b.toNat)
    rw [swapSpec_xor]
    exact advance_inv hP hu b h

/-- The clamped X25519 scalar (bits 0–2 cleared, bit 254 set, bit 255 ignored), as a number. -/
def clampedScalar (input : ℕ → Bool) : ℕ :=
  bitsValue 0 ((List.range 255).reverse.map (scalarSpec input))

/-- **X25519 is scalar multiplication in the Edwards group.** If `u ≠ 0` is the Montgomery
coordinate of the curve point `P`, the main package's `X25519.spec input u` is the Montgomery
coordinate `(1 + y)/(1 − y)` of `k·P`, `k` the clamped scalar (and `0` when `k·P = 0`).
`X25519.compiled_compute_correct` links the compiled program to `spec`. -/
theorem spec_eq_montU (input : ℕ → Bool) (u : F) (P : Curve) (hP : MRep (toZMod u) 1 P)
    (hu : toZMod u ≠ 0) : toZMod (spec input u) = montU (clampedScalar input • P) := by
  have h0 : LadderInv P (swapSpec false ⟨1, 0, u, 1⟩) 0 := by
    refine ⟨?_, ?_⟩
    · show MRep (toZMod 1) (toZMod 0) (0 • P)
      rw [toZMod_one, toZMod_zero, zero_nsmul]
      exact mrep_zero
    · show MRep (toZMod u) (toZMod 1) ((0 + 1) • P)
      rw [toZMod_one, zero_add, one_nsmul]
      exact hP
  have h := (ladderSpec_inv hP hu ((List.range 255).reverse.map (scalarSpec input)) false
    ⟨1, 0, u, 1⟩ 0 h0).1
  simp only [spec]
  rw [toZMod_mul, x25519_inverse_eq, toZMod_inverse, ← div_eq_mul_inv]
  exact mrep_div h

/-- The hypothesis of `spec_eq_montU`, from the affine relation: `u = (1 + y)/(1 − y)` for a curve
point other than the neutral element. -/
theorem mrep_of_affine {u : F} {P : Curve} (hy : P.y ≠ 1) (h : toZMod u = montU P) :
    MRep (toZMod u) 1 P := by
  rw [h]
  exact mrep_montU hy

end TlsMpcProofs.Ed25519
