import TlsMpcProofs.MontgomeryLadder
import TlsMpcProofs.EdwardsBasePoint

/-!
# The Montgomery-to-Edwards map of `liftPoint`, and which `u` are curve coordinates

Over `K = ZMod (2²⁵⁵ − 19)`, Montgomery curve `v² = u³ + 486662·u² + u` (`montQ u = u(u² + 486662u + 1)`),
Edwards curve `−x² + y² = 1 + d·x²y²` (`Ed25519.Curve`).

* `sA2_mul_self`: the main package's constant `EdwardsHinted.sqrtMinusA2` squares to `−486664`.
* `montgomery_lift`: for `v² = montQ u` with `v ≠ 0`, the point
  `x = √(−486664)·u/v`, `y = (u − 1)/(u + 1)` (RFC 7748's map; `u + 1 ≠ 0` is automatic) is a point
  of the Edwards group whose Montgomery coordinate `(1 + y)/(1 − y)` is `u` (`y ≠ 1`);
  `v ↦ −v` gives its negative (`montgomery_lift_neg`), which has the same `u`.
* `montQ_isSquare_iff`: **`montQ u` is a square exactly when `u` is the Montgomery coordinate of
  an Edwards point** other than the neutral element (`u = 0` ↔ the point `(0, −1)`, the case
  `v = 0`; `x² + 486662x + 1` has no root because `d` is not a square).
* `liftPoint_valid`, `liftPoint_invalid`: the program `EdwardsHinted.liftPoint`, given the
  opened root as the protocol supplies it (`input 0 = √(−486664)/s` with `s² = q·r²`, which is
  what `valid = sel xor b = 1` means: `lift_root`), outputs a point `P` of the Edwards group with
  Montgomery coordinate `u`, and `Z = M_A + M_B + P` for the mask points; with `valid = 0` it
  outputs the base point `B` (and `Z = M_A + M_B + B`).
* `x25519_lift`: X25519 of such a `u` is the Montgomery coordinate of `k·P` for the lifted `P`
  (`spec_eq_montU`).
-/

namespace TlsMpcProofs.Ed25519
open TlsMpc Edwards
open FieldDag (F ofNat)

/-- The Montgomery right-hand side `u·(u² + 486662·u + 1)`. -/
def montQ (u : K) : K := u * (u ^ 2 + 486662 * u + 1)

/-- `√(−486664)` (`EdwardsHinted.sqrtMinusA2`) in `ZMod p`. -/
def sA2 : K := (EdwardsHinted.sqrtMinusA2 : K)

theorem sA2_mul_self : sA2 * sA2 = -486664 := by
  have h : ((EdwardsHinted.sqrtMinusA2 * EdwardsHinted.sqrtMinusA2 + 486664 : ℕ) : K) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero EdwardsHinted.sqrtMinusA2_square
  push_cast at h
  unfold sA2
  linear_combination h

theorem natCast_ne_zero_K {n : ℕ} (h0 : 0 < n) (hn : n < FieldDag.modulus) : (n : K) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd h0 hd) (by omega)

theorem sA2_ne_zero : sA2 ≠ 0 := by
  intro h
  have h1 := sA2_mul_self
  rw [h, zero_mul] at h1
  have h2 : ((486664 : ℕ) : K) = 0 := by push_cast; linear_combination h1
  exact natCast_ne_zero_K (by norm_num) (by decide) h2

theorem two_ne_zero' : (2 : K) ≠ 0 := Complete.two_ne_zero (d := dK)

/-- `486660 = d·(√(−486664))²`. -/
theorem c486660_eq : (486660 : K) = dK * (sA2 * sA2) := by
  linear_combination (-dK) * sA2_mul_self + 4 * dK_mul

/-- `486660 = A − 2` is not a square (so `u = −1` is not on the curve). -/
theorem c486660_not_isSquare : ¬ IsSquare (486660 : K) := by
  rintro ⟨v, hv⟩
  apply dK_not_isSquare
  refine ⟨v / sA2, ?_⟩
  have hs := sA2_ne_zero
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hs hs)]
  rw [← c486660_eq]
  exact hv

/-- `u² + 486662u + 1` has no root (its discriminant `A² − 4 = −d·486664²` is not a square). -/
theorem montW_ne_zero (u : K) : u ^ 2 + 486662 * u + 1 ≠ 0 := by
  intro hu
  obtain ⟨i, hi⟩ := neg_one_isSquare
  have hs := sA2_ne_zero
  have hi0 : i ≠ 0 := by
    rintro rfl
    have : (1 : K) = 0 := by linear_combination -hi
    exact one_ne_zero this
  have h1 : (2 * u + 486662) ^ 2 = 486660 * 486664 := by linear_combination 4 * hu
  apply dK_not_isSquare
  refine ⟨(2 * u + 486662) / (i * (sA2 * sA2)), ?_⟩
  have hw : i * (sA2 * sA2) ≠ 0 := mul_ne_zero hi0 (mul_ne_zero hs hs)
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hw hw)]
  linear_combination (-dK * (sA2 * sA2) ^ 2) * hi - h1 + (-dK * (sA2 * sA2)) * sA2_mul_self -
    486664 * c486660_eq

theorem montQ_neg_one : montQ (-1) = 486660 := by
  unfold montQ
  ring

/-- **The Montgomery-to-Edwards map:** for `v² = montQ u`, `v ≠ 0`, `u + 1 ≠ 0` and
`(√(−486664)·u/v, (u − 1)/(u + 1))` is on the Edwards curve. -/
theorem lift_onCurve {u v : K} (hv : v * v = montQ u) (hv0 : v ≠ 0) :
    u + 1 ≠ 0 ∧ OnCurve dK (sA2 * u / v) ((u - 1) / (u + 1)) := by
  have hu1 : u + 1 ≠ 0 := by
    intro h
    have hu : u = -1 := by linear_combination h
    rw [hu, montQ_neg_one] at hv
    exact c486660_not_isSquare ⟨v, hv.symm⟩
  refine ⟨hu1, onCurve_div hv0 hu1 ?_⟩
  unfold montQ at hv
  linear_combination (-(u ^ 2) * (u + 1) ^ 2 - dK * u ^ 2 * (u - 1) ^ 2) * sA2_mul_self +
    (-4 * u) * hv + (4 * u ^ 2 * (u - 1) ^ 2) * dK_mul

/-- **The lifted point is a point of the Edwards group with Montgomery coordinate `u`.** -/
theorem montgomery_lift {u v : K} (hv : v * v = montQ u) (hv0 : v ≠ 0) :
    ∃ P : Curve, P.x = sA2 * u / v ∧ P.y = (u - 1) / (u + 1) ∧ P.y ≠ 1 ∧ montU P = u := by
  obtain ⟨hu1, hon⟩ := lift_onCurve hv hv0
  refine ⟨⟨_, _, hon⟩, rfl, rfl, ?_, ?_⟩
  · intro h
    rw [div_eq_one_iff_eq hu1] at h
    have : (2 : K) = 0 := by linear_combination -h
    exact two_ne_zero' this
  · show (1 + (u - 1) / (u + 1)) / (1 - (u - 1) / (u + 1)) = u
    rw [one_add_div hu1, one_sub_div hu1, div_div_div_cancel_right₀ hu1, div_eq_iff]
    · ring
    · intro h
      exact two_ne_zero' (by linear_combination h)

/-- **`v ↦ −v` is negation:** the lift of `(u, −v)` is `−P` (same `u`). -/
theorem montgomery_lift_neg {u v : K} {P : Curve} (hx : P.x = sA2 * u / v) :
    (-P).x = sA2 * u / (-v) ∧ (-P).y = P.y ∧ montU (-P) = montU P := by
  refine ⟨?_, rfl, rfl⟩
  rw [Point.neg_x, hx, div_neg]

/-- The point `(0, −1)` (Montgomery `(0, 0)`, of order 2). -/
def T2 : Curve := ⟨0, -1, by unfold OnCurve; ring⟩

theorem montU_T2 : montU T2 = 0 := by
  show (1 + -1) / (1 - -1) = (0 : K)
  rw [add_neg_cancel, zero_div]

theorem T2_y_ne_one : T2.y ≠ 1 := by
  intro h
  have h' : (-1 : K) = 1 := h
  exact two_ne_zero' (by linear_combination -h')

/-- **`montQ u` is a square exactly when `u` is the Montgomery coordinate `(1 + y)/(1 − y)` of a
point of the Edwards group other than the neutral element.** -/
theorem montQ_isSquare_iff (u : K) : IsSquare (montQ u) ↔ ∃ P : Curve, P.y ≠ 1 ∧ montU P = u := by
  constructor
  · rintro ⟨v, hv⟩
    by_cases hv0 : v = 0
    · have hq : montQ u = 0 := by rw [hv, hv0, mul_zero]
      have hu : u = 0 := by
        unfold montQ at hq
        rcases mul_eq_zero.mp hq with h | h
        · exact h
        · exact absurd h (montW_ne_zero u)
      exact ⟨T2, T2_y_ne_one, by rw [montU_T2, hu]⟩
    · obtain ⟨P, -, -, hy, hm⟩ := montgomery_lift hv.symm hv0
      exact ⟨P, hy, hm⟩
  · rintro ⟨P, hy, rfl⟩
    have ht : 1 - P.y ≠ 0 := fun h => hy (by linear_combination -h)
    have hu : montU P * (1 - P.y) = 1 + P.y := div_mul_cancel₀ _ ht
    by_cases hx : P.x = 0
    · have hc := P.on
      unfold OnCurve at hc
      rw [hx] at hc
      have hyy : (P.y - 1) * (P.y + 1) = 0 := by linear_combination hc
      have hm1 : P.y + 1 = 0 := (mul_eq_zero.mp hyy).resolve_left (fun h => hy (by linear_combination h))
      have hu0 : montU P = 0 := by
        have h1y : 1 + P.y = 0 := by linear_combination hm1
        unfold montU
        rw [h1y, zero_div]
      rw [hu0]
      exact ⟨0, by unfold montQ; ring⟩
    · refine ⟨sA2 * montU P / P.x, ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hx hx)]
      have key : (1 - P.y) ^ 3 *
          (montQ (montU P) * (P.x * P.x) - sA2 * montU P * (sA2 * montU P)) = 0 := by
        unfold montQ
        linear_combination
          (P.x ^ 2 * ((montU P * (1 - P.y)) ^ 2 + montU P * (1 - P.y) * (1 + P.y) + (1 + P.y) ^ 2 +
              486662 * (1 - P.y) * (montU P * (1 - P.y) + (1 + P.y)) + (1 - P.y) ^ 2) -
            sA2 * sA2 * (1 - P.y) * (montU P * (1 - P.y) + (1 + P.y))) * hu +
          (-486664 * (1 + P.y)) * P.on + (-4 * (1 + P.y) * P.x ^ 2 * P.y ^ 2) * dK_mul +
          (-(1 + P.y) ^ 2 * (1 - P.y)) * sA2_mul_self
      have h3 := (mul_eq_zero.mp key).resolve_left (pow_ne_zero 3 ht)
      linear_combination h3

/-! ### The program `liftPoint` -/

section Program
open EdwardsAffine EdwardsHinted

/-- **What `valid = 1` means for the opened root:** with `w = q·r²·(1 + b)` opened, `s` its public
root when `sel` (`w` a square), else a root of `w/2`, and `sel xor b = 1`, `s² = q·r²`. -/
theorem lift_root {q r w s : K} {sel b : Bool} (hw : w = q * (r * r) * (if b then 2 else 1))
    (hs : if sel then s * s = w else 2 * (s * s) = w) (hv : (sel ^^ b) = true) :
    s * s = q * (r * r) := by
  cases sel <;> cases b <;> simp at hv hs hw
  · rw [hw] at hs
    have h2 := two_ne_zero'
    have : 2 * (s * s - q * (r * r)) = 0 := by linear_combination hs
    linear_combination ((mul_eq_zero.mp this).resolve_left h2)
  · rw [hs, hw]

/-- **`liftPoint` with `valid = 1`:** if `input 0 · s = √(−486664)` for `s ≠ 0` with
`s² = montQ(u)·r²` (`u` = input 2, `r` = input 3), its point output is a point `P` of the Edwards
group with Montgomery coordinate `u`, and its `Z` output is `M_A + M_B + P` for the mask points
`M_A` (inputs 5, 6) and `M_B` (inputs 7, 8). -/
theorem liftPoint_valid (input : ℕ → F) {s : K} (hs0 : s ≠ 0)
    (h0 : toZMod (input 0) * s = sA2)
    (hsq : s * s = montQ (toZMod (input 2)) * (toZMod (input 3) * toZMod (input 3)))
    (hvalid : toZMod (input 1 + input 4 - ofNat 2 * (input 1 * input 4)) = 1)
    {MA MB : Curve} (hA : Affine (input 5, input 6) MA) (hB : Affine (input 7, input 8) MB) :
    ∃ (P : Curve) (val px py zx zy : F),
      (liftPoint ()).map (FieldDag.Expr.eval input) = [val, px, py, zx, zy] ∧ toZMod val = 1 ∧
        Affine (px, py) P ∧ montU P = toZMod (input 2) ∧ P.y ≠ 1 ∧ Affine (zx, zy) (MA + MB + P) := by
  have hr0 : toZMod (input 3) ≠ 0 := by
    intro hr
    rw [hr, mul_zero, mul_zero] at hsq
    exact hs0 (mul_self_eq_zero.mp hsq)
  have hv : (s / toZMod (input 3)) * (s / toZMod (input 3)) = montQ (toZMod (input 2)) := by
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hr0 hr0), hsq]
  have hv0 : s / toZMod (input 3) ≠ 0 := div_ne_zero hs0 hr0
  obtain ⟨P, hPx, hPy, hy1, hm⟩ := montgomery_lift hv hv0
  have hu1 := (lift_onCurve hv hv0).1
  have hu1' : 1 + toZMod (input 2) ≠ 0 := by rw [add_comm]; exact hu1
  have hi0 : toZMod (input 0) = sA2 / s := by rw [eq_div_iff hs0, h0]
  rw [liftPoint_eval]
  set valid := input 1 + input 4 - ofNat 2 * (input 1 * input 4) with hval
  have hp : Affine (ofNat EdwardsHinted.baseX + valid * (input 0 * (input 2 * input 3) - ofNat EdwardsHinted.baseX),
      ofNat EdwardsHinted.baseY + valid * ((input 2 - ofNat 1) * FieldDag.inverse (ofNat 1 + valid * input 2) -
        ofNat EdwardsHinted.baseY)) P := by
    constructor
    · show toZMod (ofNat EdwardsHinted.baseX + valid * (input 0 * (input 2 * input 3) - ofNat EdwardsHinted.baseX)) = P.x
      simp only [toZMod_add, toZMod_mul, toZMod_sub, hvalid, hPx, hi0, one_mul]
      field_simp
      ring
    · show toZMod (ofNat EdwardsHinted.baseY + valid * ((input 2 - ofNat 1) *
          FieldDag.inverse (ofNat 1 + valid * input 2) - ofNat EdwardsHinted.baseY)) = P.y
      simp only [toZMod_add, toZMod_mul, toZMod_sub, toZMod_inverse, toZMod_ofNat_one, hvalid, hPy,
        one_mul]
      field_simp
      ring
  refine ⟨P, valid, _, _, _, _, rfl, hvalid, hp, hm, hy1, ?_⟩
  exact affine_pointAddValue (affine_pointAddValue hA hB) hp

/-- **`liftPoint` with `valid = 0`:** its point output is the base point `B`, and `Z` is
`M_A + M_B + B`. -/
theorem liftPoint_invalid (input : ℕ → F)
    (hvalid : toZMod (input 1 + input 4 - ofNat 2 * (input 1 * input 4)) = 0)
    {MA MB : Curve} (hA : Affine (input 5, input 6) MA) (hB : Affine (input 7, input 8) MB) :
    ∃ (val px py zx zy : F),
      (liftPoint ()).map (FieldDag.Expr.eval input) = [val, px, py, zx, zy] ∧ toZMod val = 0 ∧
        Affine (px, py) B ∧ Affine (zx, zy) (MA + MB + B) := by
  rw [liftPoint_eval]
  set valid := input 1 + input 4 - ofNat 2 * (input 1 * input 4) with hval
  have hp : Affine (ofNat EdwardsHinted.baseX + valid * (input 0 * (input 2 * input 3) - ofNat EdwardsHinted.baseX),
      ofNat EdwardsHinted.baseY + valid * ((input 2 - ofNat 1) * FieldDag.inverse (ofNat 1 + valid * input 2) -
        ofNat EdwardsHinted.baseY)) B := by
    constructor
    · show toZMod (ofNat EdwardsHinted.baseX + valid * _) = B.x
      rw [toZMod_add, toZMod_mul, hvalid, zero_mul, add_zero, toZMod_ofNat]
      rfl
    · show toZMod (ofNat EdwardsHinted.baseY + valid * _) = B.y
      rw [toZMod_add, toZMod_mul, hvalid, zero_mul, add_zero, toZMod_ofNat]
      rfl
  refine ⟨valid, _, _, _, _, rfl, hvalid, hp, ?_⟩
  exact affine_pointAddValue (affine_pointAddValue hA hB) hp

end Program

/-- **X25519 of a lifted `u`:** for `v² = montQ u`, `v ≠ 0`, the lifted Edwards point `P` has
`X25519.spec input u = montU (k·P)`, `k` the clamped scalar. -/
theorem x25519_lift (input : ℕ → Bool) (u : F) {v : K} (hv : v * v = montQ (toZMod u))
    (hv0 : v ≠ 0) :
    ∃ P : Curve, P.x = sA2 * toZMod u / v ∧ P.y = (toZMod u - 1) / (toZMod u + 1) ∧
      toZMod (X25519.spec input u) = montU (clampedScalar input • P) := by
  obtain ⟨P, hx, hy, hy1, hm⟩ := montgomery_lift hv hv0
  have hu0 : toZMod u ≠ 0 := by
    intro h
    rw [h] at hv
    unfold montQ at hv
    rw [zero_mul] at hv
    exact hv0 (mul_self_eq_zero.mp hv)
  exact ⟨P, hx, hy, spec_eq_montU input u P (mrep_of_affine hy1 hm.symm) hu0⟩

end TlsMpcProofs.Ed25519
