import TlsMpcProofs.MontgomeryLift
import TlsMpcProofs.X25519Clamp

/-!
# X25519 at `u = 0`, and on every coordinate of a curve point

* `spec_u_zero`: **`X25519.spec input u = 0` when `u = 0`** (RFC 7748's all-zero output, which TLS
  must reject): with `u = 0` every ladder step leaves `X·Z = 0` in both registers (the doubling's
  `Z` is `4·X·Z·(…)`, the differential addition's `Z` is `u·(…)`), so `x2·z2⁻¹ = 0`.
* The group reading: `u = 0` is the Montgomery coordinate of `T2 = (0, −1)`, the point of order 2
  (`T2_add_self`), and the clamped scalar is even, so `k·T2 = 0` and `montU 0 = 0`
  (`spec_u_zero_montU`). Hence `spec_eq_montU'`: **for every curve point `P` with
  `MRep u 1 P` (now including `u = 0`), `X25519.spec input u` is the Montgomery coordinate of
  `k·P`**, and `x25519_on_curve`: for every `u` with `montQ u` a square (exactly the Montgomery
  coordinates of curve points, `montQ_isSquare_iff`) there is a curve point `P` with that
  coordinate and `X25519.spec input u = montU (k·P)`.

Not proved: inputs `u` on the quadratic twist (`montQ u` not a square). There the ladder
computes the `u`-coordinate of `k·Q` on the twist `2·v² = u³ + 486662u² + u`. Its Edwards model is
`−2x² + y² = 1 + 2d·x²y²`: the coefficient `a = −2` is not a square in `ZMod p` (2 is not, `−1` is),
and scaling `x` to `a = −1` needs `√2`, so neither `EdwardsCurve.lean`'s construction (which needs
`a = −1` with `−1` a square and `d` not a square, i.e. a complete addition law) nor its
associativity identities apply; a group on the twist would need the incomplete (projective)
Edwards law or a transfer from Mathlib's Weierstrass group, plus the x-only ladder formulas proved
against that law. That is not done here.
-/

namespace TlsMpcProofs.Ed25519
open TlsMpc Edwards X25519
open FieldDag (F ofNat)

/-- Both ladder registers hold a pair with `X·Z = 0`. -/
def ZeroInv (s : Coordinates F) : Prop :=
  toZMod s.x2 * toZMod s.z2 = 0 ∧ toZMod s.x3 * toZMod s.z3 = 0

theorem swapSpec_zeroInv (b : Bool) {s : Coordinates F} (h : ZeroInv s) : ZeroInv (swapSpec b s) := by
  cases b
  · exact h
  · exact ⟨h.2, h.1⟩

theorem advance_zeroInv {u : F} (hu : toZMod u = 0) {s : Coordinates F} (h : ZeroInv s) :
    ZeroInv (advance concrete u s) := by
  obtain ⟨h1, -⟩ := h
  simp only [ZeroInv, advance, concrete_add, concrete_sub, concrete_mul, concrete_const, toZMod_mul,
    toZMod_add, toZMod_sub, toZMod_ofNat, Nat.cast_ofNat, hu]
  generalize toZMod s.x2 = a at h1 ⊢
  generalize toZMod s.z2 = b at h1 ⊢
  constructor
  · linear_combination
      (4 * ((a + b) * (a + b)) * ((a - b) * (a - b)) * ((a + b) * (a + b) + 121665 * 4 * a * b)) * h1
  · ring

theorem ladderSpec_zeroInv {u : F} (hu : toZMod u = 0) :
    ∀ (bits : List Bool) (prev : Bool) (s : Coordinates F), ZeroInv s →
      ZeroInv (ladderSpec u prev s bits)
  | [], prev, _, h => swapSpec_zeroInv prev h
  | b :: rest, _, _, h =>
    ladderSpec_zeroInv hu rest b _ (advance_zeroInv hu (swapSpec_zeroInv _ h))

/-- **X25519 of `u = 0` is `0`** (for every scalar). -/
theorem spec_u_zero (input : ℕ → Bool) {u : F} (hu : toZMod u = 0) : toZMod (spec input u) = 0 := by
  have h0 : ZeroInv (⟨1, 0, u, 1⟩ : Coordinates F) := by
    refine ⟨?_, ?_⟩
    · show toZMod 1 * toZMod 0 = 0
      rw [toZMod_zero, mul_zero]
    · show toZMod u * toZMod 1 = 0
      rw [hu, zero_mul]
  have h := (ladderSpec_zeroInv hu ((List.range 255).reverse.map (scalarSpec input)) false _ h0).1
  simp only [spec]
  rw [toZMod_mul, x25519_inverse_eq, toZMod_inverse]
  rcases mul_eq_zero.mp h with hX | hZ
  · rw [hX, zero_mul]
  · rw [hZ, inv_zero, mul_zero]

/-- `(0, −1)` has order 2. -/
theorem T2_add_self : T2 + T2 = 0 := by
  apply Point.ext
  · rw [Point.add_x]
    simp [T2]
  · rw [Point.add_y]
    simp [T2]

theorem montU_zero : montU (0 : Curve) = 0 := by
  show (1 + 1) / (1 - 1) = (0 : K)
  rw [sub_self, div_zero]

/-- **The group reading of `u = 0`:** the clamped scalar is even, so `k·T2 = 0`, whose Montgomery
coordinate is `0`. -/
theorem spec_u_zero_montU (input : ℕ → Bool) {u : F} (hu : toZMod u = 0) :
    clampedScalar input • T2 = 0 ∧ toZMod (spec input u) = montU (clampedScalar input • T2) := by
  have hk : clampedScalar input • T2 = 0 := by
    have h8 := clampedScalar_mod_eight input
    rw [show clampedScalar input = clampedScalar input / 2 * 2 by omega, mul_smul, two_nsmul,
      T2_add_self, smul_zero]
  refine ⟨hk, ?_⟩
  rw [hk, montU_zero, spec_u_zero input hu]

/-- The only curve point with Montgomery representative `(0 : 1)` is `T2`. -/
theorem mrep_zero_eq_T2 {P : Curve} (h : MRep 0 1 P) : P = T2 := by
  have hc := mrep_cross h
  have hy : P.y = -1 := by linear_combination -hc
  have hon := P.on
  unfold OnCurve at hon
  rw [hy] at hon
  have hx2 : P.x ^ 2 * (1 + dK) = 0 := by linear_combination -hon
  have hd : 1 + dK ≠ 0 := by
    have := one_add_d_sq_ne_zero (d := dK) 1
    rwa [one_pow, mul_one] at this
  have hx : P.x = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    ((mul_eq_zero.mp hx2).resolve_right hd)
  exact Point.ext hx hy

/-- **X25519 is scalar multiplication for every curve point** (`spec_eq_montU` without
`u ≠ 0`). -/
theorem spec_eq_montU' (input : ℕ → Bool) (u : F) (P : Curve) (hP : MRep (toZMod u) 1 P) :
    toZMod (spec input u) = montU (clampedScalar input • P) := by
  by_cases hu : toZMod u = 0
  · rw [hu] at hP
    rw [mrep_zero_eq_T2 hP]
    exact (spec_u_zero_montU input hu).2
  · exact spec_eq_montU input u P hP hu

/-- **X25519 on every coordinate of a curve point:** if `montQ u` is a square (equivalently, `u`
is the Montgomery coordinate of a curve point), there is a curve point `P` with
`(1 + y)/(1 − y) = u` and `X25519.spec input u = montU (k·P)`. -/
theorem x25519_on_curve (input : ℕ → Bool) (u : F) (h : IsSquare (montQ (toZMod u))) :
    ∃ P : Curve, P.y ≠ 1 ∧ montU P = toZMod u ∧
      toZMod (spec input u) = montU (clampedScalar input • P) := by
  obtain ⟨P, hy, hm⟩ := (montQ_isSquare_iff _).mp h
  exact ⟨P, hy, hm, spec_eq_montU' input u P (mrep_of_affine hy hm.symm)⟩

end TlsMpcProofs.Ed25519
