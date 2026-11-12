import TlsMpcProofs.Prime25519
import TlsMpcProofs.Uniform
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import TlsMpc.EdwardsAffine
import TlsMpc.EdwardsHinted
import TlsMpc.Signal.XEdDsaField

/-!
# H-QR: the quadratic-residue facts over p = 2²⁵⁵ − 19, as theorems

What the main package assumes (REORGANIZATION_PLAN.md R7 / P-HINT(b); `EdwardsHinted` header;
`EdwardsAffine.recipient`'s docstring):

* **2 is not a square** mod p (`two_not_square`), because p ≡ 5 (mod 8).
* **Euler's criterion** for this p (`euler_criterion`, `euler_nonsquare`).
* **√−1 = 2^((p−1)/4)** (`sqrtMinusOne_eq_power`, `sqrtMinusOne_mul_self`): the constant
  `EdwardsAffine.sqrtMinusOne` (= `XEdDsaField.sqrtM1`) is that power and squares to −1.
* **The p ≡ 5 (mod 8) square-root candidate** `c = x^((p+3)/8)`: `c⁴ = x²` iff `x` is a square,
  and then `c² = ±x` (`candidate_fourth_iff`, `candidate_sq`). For the program
  `EdwardsAffine.recipient`: its check value is zero exactly when its `x²` is a square
  (`recipient_check_zero_iff`), and then its `x` is a square root (`recipient_x_mul_self`); which
  of ±x comes out is whatever the formula gives (`x = c` when `c² = x²`, else `c·√−1`), as its
  docstring says.
* **The hinted lift** (`EdwardsHinted.liftOpen`): for `q ≠ 0, r ≠ 0`, the opened
  `w = q·r²·(1 + b)` is a square iff (`q` is a square iff `b = 0`) — so validity is
  `sel xor b` (`lift_select`, `liftOpen_square_iff`); and for `q ≠ 0` with `r` uniform in F and
  `b` a uniform bit, `w` is **exactly uniform on F** (`lift_opened_uniform`), whatever `q`, and
  whatever bit the other party contributes (`lift_opened_uniform_xor`). (The plan's P-HINT(b) said
  "4 pairs to each value"; for the pair `(r, b)` it is 2, `lift_fiber_card`; with both parties'
  bits `(r, b_A, b_B)` it is 4.)

Everything is stated with the main package's own `F`, `ofNat`, `power`, `inverse`, programs and
`*_eval` theorems; the proofs move to `ZMod p` through `FieldBridge.toZMod`.
-/

namespace TlsMpcProofs
open TlsMpc

/-- Mathlib's `ZMod p` for the main package's modulus. -/
abbrev K := ZMod FieldDag.modulus

instance fact_two_lt_modulus : Fact (2 < FieldDag.modulus) := ⟨by decide⟩

theorem modulus_mod_eight : FieldDag.modulus % 8 = 5 := by decide

theorem two_ne_zero_K : (2 : K) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact absurd (Nat.le_of_dvd (by norm_num) h2) (by decide)

theorem zmod_two_not_square : ¬ IsSquare (2 : K) := by
  rw [ZMod.exists_sq_eq_two_iff (by decide), modulus_mod_eight]
  decide

/-- Squares multiply like signs (from Euler's criterion). -/
theorem isSquare_mul_iff {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsSquare (a * b) ↔ (IsSquare a ↔ IsSquare b) := by
  rw [ZMod.euler_criterion _ (mul_ne_zero ha hb), ZMod.euler_criterion _ ha,
    ZMod.euler_criterion _ hb, mul_pow]
  have hne : (-1 : K) ≠ 1 := ZMod.neg_one_ne_one
  rcases ZMod.pow_div_two_eq_neg_one_or_one _ ha with h1 | h1 <;>
    rcases ZMod.pow_div_two_eq_neg_one_or_one _ hb with h2 | h2 <;>
    simp [h1, h2, hne, hne.symm]

/-! ### Moving between `F` and `ZMod p` -/

theorem exists_mul_self_iff (x : FieldDag.F) : (∃ r : FieldDag.F, r * r = x) ↔ IsSquare (toZMod x) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨toZMod r, by rw [toZMod_mul]⟩
  · rintro ⟨s, hs⟩
    refine ⟨toZMod.symm s, toZMod_injective ?_⟩
    rw [toZMod_mul, RingEquiv.apply_symm_apply, hs]

theorem toZMod_ofNat_zero : toZMod (FieldDag.ofNat 0) = 0 := by
  rw [toZMod_ofNat, Nat.cast_zero]

theorem toZMod_ofNat_one : toZMod (FieldDag.ofNat 1) = 1 := by
  rw [toZMod_ofNat, Nat.cast_one]

theorem toZMod_ne_zero {x : FieldDag.F} (hx : x ≠ FieldDag.ofNat 0) : toZMod x ≠ 0 := by
  intro h
  apply hx
  apply toZMod_injective
  rw [h, toZMod_ofNat_zero]

theorem toZMod_bitValue (b : Bool) : toZMod (X25519.bitValue b) = if b then 1 else 0 := by
  cases b
  · show toZMod 0 = _; simp
  · show toZMod 1 = _; simp

theorem toZMod_one_add_bitValue (b : Bool) :
    toZMod (FieldDag.ofNat 1 + X25519.bitValue b) = if b then 2 else 1 := by
  rw [toZMod_add, toZMod_ofNat_one, toZMod_bitValue]
  cases b <;> norm_num

/-! ### H-QR-1, H-QR-2: 2 is a non-square; Euler's criterion -/

/-- **2 is not a square mod p** (p ≡ 5 mod 8). -/
theorem two_not_square : ¬ ∃ r : FieldDag.F, r * r = FieldDag.ofNat 2 := by
  rw [exists_mul_self_iff, toZMod_ofNat]
  have h : ((2 : ℕ) : K) = 2 := by norm_num
  rw [h]
  exact zmod_two_not_square

/-- **Euler's criterion for p = 2²⁵⁵ − 19**, with the main package's `power`. -/
theorem euler_criterion (x : FieldDag.F) (hx : x ≠ FieldDag.ofNat 0) :
    (∃ r : FieldDag.F, r * r = x) ↔ FieldDag.power x ((FieldDag.modulus - 1) / 2) = FieldDag.ofNat 1 := by
  rw [exists_mul_self_iff, ← toZMod_eq_iff, toZMod_power, toZMod_ofNat_one]
  have he : (FieldDag.modulus - 1) / 2 = FieldDag.modulus / 2 := by decide
  rw [he]
  exact ZMod.euler_criterion _ (toZMod_ne_zero hx)

/-- **Euler's criterion, the other half:** a nonzero non-square has `x^((p−1)/2) = −1`. -/
theorem euler_nonsquare (x : FieldDag.F) (hx : x ≠ FieldDag.ofNat 0) (hn : ¬ ∃ r : FieldDag.F, r * r = x) :
    FieldDag.power x ((FieldDag.modulus - 1) / 2) = FieldDag.ofNat 0 - FieldDag.ofNat 1 := by
  rw [exists_mul_self_iff, ZMod.euler_criterion _ (toZMod_ne_zero hx)] at hn
  apply toZMod_injective
  rw [toZMod_power, toZMod_sub, toZMod_ofNat_zero, toZMod_ofNat_one, zero_sub]
  have he : (FieldDag.modulus - 1) / 2 = FieldDag.modulus / 2 := by decide
  rw [he]
  rcases ZMod.pow_div_two_eq_neg_one_or_one _ (toZMod_ne_zero hx) with h | h
  · exact absurd h hn
  · exact h

/-! ### H-QR-3: √−1 = 2^((p−1)/4) -/

/-- The two copies of the constant in the main package are the same number. -/
theorem sqrtM1_eq_sqrtMinusOne : Signal.XEdDsaField.sqrtM1 = EdwardsAffine.sqrtMinusOne := rfl

/-- **`EdwardsAffine.sqrtMinusOne` is `2^((p−1)/4)`** (checked by kernel square-and-multiply). -/
theorem sqrtMinusOne_eq_power :
    FieldDag.ofNat EdwardsAffine.sqrtMinusOne = FieldDag.power (FieldDag.ofNat 2) ((FieldDag.modulus - 1) / 4) := by
  apply toZMod_injective
  have h : powMod 2 ((FieldDag.modulus - 1) / 4) FieldDag.modulus = EdwardsAffine.sqrtMinusOne := by
    decide +kernel
  rw [toZMod_power, toZMod_ofNat, toZMod_ofNat, zmod_pow_eq_powMod 2 _ (by decide), h]

/-- **`sqrtMinusOne² = −1`** in `F`. -/
theorem sqrtMinusOne_mul_self :
    FieldDag.ofNat EdwardsAffine.sqrtMinusOne * FieldDag.ofNat EdwardsAffine.sqrtMinusOne =
      FieldDag.ofNat 0 - FieldDag.ofNat 1 := by
  apply toZMod_injective
  rw [toZMod_mul, toZMod_sub, toZMod_ofNat, toZMod_ofNat_zero, toZMod_ofNat_one]
  have h : ((EdwardsAffine.sqrtMinusOne * EdwardsAffine.sqrtMinusOne + 1 : ℕ) : K) = 0 := by
    rw [← ZMod.natCast_mod, EdwardsAffine.sqrtMinusOne_square, Nat.cast_zero]
  push_cast at h
  linear_combination h

theorem zmod_sqrtMinusOne_sq : ((EdwardsAffine.sqrtMinusOne : ℕ) : K) * (EdwardsAffine.sqrtMinusOne : ℕ) = -1 := by
  have h := congrArg toZMod sqrtMinusOne_mul_self
  rw [toZMod_mul, toZMod_sub, toZMod_ofNat, toZMod_ofNat_zero, toZMod_ofNat_one, zero_sub] at h
  exact h

/-! ### H-QR-4: the square-root candidate for p ≡ 5 (mod 8) -/

theorem candidate_pow_four (X : K) :
    (X ^ ((FieldDag.modulus + 3) / 8)) ^ 4 = X ^ 2 * X ^ (FieldDag.modulus / 2) := by
  rw [← pow_mul, ← pow_add]
  congr 1

/-- **`c = x^((p+3)/8)` has `c⁴ = x²` exactly when `x` is a square.** -/
theorem candidate_fourth_iff (X : K) : (X ^ ((FieldDag.modulus + 3) / 8)) ^ 4 = X ^ 2 ↔ IsSquare X := by
  by_cases hX : X = 0
  · subst hX
    simp [zero_pow (show (FieldDag.modulus + 3) / 8 ≠ 0 by decide)]
  · rw [candidate_pow_four, ZMod.euler_criterion _ hX]
    have hX2 : X ^ 2 ≠ 0 := pow_ne_zero 2 hX
    constructor
    · intro h
      exact mul_left_cancel₀ hX2 (h.trans (mul_one _).symm)
    · intro h
      rw [h, mul_one]

/-- **For a square `x`, the candidate squares to `x` or to `−x`.** -/
theorem candidate_sq (X : K) (hX : IsSquare X) :
    (X ^ ((FieldDag.modulus + 3) / 8)) ^ 2 = X ∨ (X ^ ((FieldDag.modulus + 3) / 8)) ^ 2 = -X := by
  have h4 := (candidate_fourth_iff X).mpr hX
  have hprod : ((X ^ ((FieldDag.modulus + 3) / 8)) ^ 2 - X) * ((X ^ ((FieldDag.modulus + 3) / 8)) ^ 2 + X) = 0 := by
    linear_combination h4
  rcases mul_eq_zero.mp hprod with h | h
  · left; linear_combination h
  · right; linear_combination h

/-! ### The program `EdwardsAffine.recipient` -/

section Recipient
open FieldDag EdwardsAffine

/-- `y = (u − 1)/(u + 1)` (value form). -/
def recY (U : F) : F := (U - ofNat 1) * inverse (U + ofNat 1)

/-- `x² = 121666·(y² − 1)/(121666 − 121665·y²)` (value form), the value `recipient` square-roots. -/
def recXX (U : F) : F :=
  ofNat 121666 * (recY U * recY U - ofNat 1) * inverse (ofNat 121666 - ofNat 121665 * (recY U * recY U))

/-- The candidate as `recipient` computes it: `t = xx^(2²⁵¹ − 1)` by 250 square-and-multiply
steps, `c = t²`. -/
def recCand (X : F) : F :=
  (power X (2 ^ 250) * power X (2 ^ 250 - 1)) * (power X (2 ^ 250) * power X (2 ^ 250 - 1))

theorem eval_mul (input : ℕ → F) (a b : Expr) : (mul a b).eval input = a.eval input * b.eval input := rfl
theorem eval_add (input : ℕ → F) (a b : Expr) : (add a b).eval input = a.eval input + b.eval input := rfl
theorem eval_sub (input : ℕ → F) (a b : Expr) : (sub a b).eval input = a.eval input - b.eval input := rfl
theorem eval_div (input : ℕ → F) (a b : Expr) :
    (EdwardsAffine.div a b).eval input = a.eval input * inverse (b.eval input) := rfl
theorem eval_const (input : ℕ → F) (n : ℕ) : (Expr.const n).eval input = ofNat n := rfl

/-- The 250-step fold of `recipient`, on values. -/
theorem eval_foldl_square_mul (input : ℕ → F) (e : Expr) : ∀ (l : List ℕ) (t : Expr),
    toZMod ((l.foldl (fun t _ => mul (mul t t) e) t).eval input) =
      toZMod (t.eval input) ^ (2 ^ l.length) * toZMod (e.eval input) ^ (2 ^ l.length - 1)
  | [], t => by simp
  | a :: l, t => by
    rw [List.foldl_cons, eval_foldl_square_mul input e l, List.length_cons, eval_mul, eval_mul,
      toZMod_mul, toZMod_mul]
    have h1 : 2 ^ (l.length + 1) - 1 = 2 ^ l.length + (2 ^ l.length - 1) := by
      rw [pow_succ]; have := Nat.one_le_two_pow (n := l.length); omega
    rw [h1, pow_add, pow_succ]
    generalize 2 ^ l.length = m
    generalize m - 1 = k
    ring

theorem eval_foldl_square_mul_F (input : ℕ → F) (e : Expr) (l : List ℕ) (t : Expr) :
    (l.foldl (fun t _ => mul (mul t t) e) t).eval input =
      power (t.eval input) (2 ^ l.length) * power (e.eval input) (2 ^ l.length - 1) := by
  apply toZMod_injective
  rw [eval_foldl_square_mul, toZMod_mul, toZMod_power, toZMod_power]

/-- **What `recipient` computes**, as values: `x`, `y` and the check. -/
theorem recipient_eval (u : Expr) (input : ℕ → F) :
    (recipient u).1.1.eval input =
        recCand (recXX (u.eval input)) * (ofNat sqrtMinusOne +
          (recCand (recXX (u.eval input)) * recCand (recXX (u.eval input)) + recXX (u.eval input)) *
            inverse (ofNat 2 * recXX (u.eval input)) * ofNat (modulus + 1 - sqrtMinusOne)) ∧
      (recipient u).1.2.eval input = recY (u.eval input) ∧
      (recipient u).2.eval input =
        (recCand (recXX (u.eval input)) * recCand (recXX (u.eval input)) - recXX (u.eval input)) *
          (recCand (recXX (u.eval input)) * recCand (recXX (u.eval input)) + recXX (u.eval input)) := by
  simp only [recipient, eval_mul, eval_add, eval_sub, eval_div, eval_const, eval_foldl_square_mul_F,
    List.length_range]
  exact ⟨rfl, rfl, rfl⟩

theorem toZMod_recCand (X : F) : toZMod (recCand X) = toZMod X ^ ((modulus + 3) / 8) := by
  rw [recCand, toZMod_mul, toZMod_mul, toZMod_power, toZMod_power, ← pow_add, ← pow_add]
  congr 1

/-- **`recipient`'s check value is zero exactly when its `x²` is a square** (so, with `y` the
Edwards `y` of the Montgomery `u`, exactly when `u` lifts to the curve rather than its twist,
given the formulas — H-GROUP for that reading). -/
theorem recipient_check_zero_iff (u : Expr) (input : ℕ → F) :
    (recipient u).2.eval input = ofNat 0 ↔ ∃ r : F, r * r = recXX (u.eval input) := by
  rw [(recipient_eval u input).2.2, exists_mul_self_iff, ← toZMod_eq_iff, toZMod_ofNat_zero,
    toZMod_mul, toZMod_sub, toZMod_add, toZMod_mul, toZMod_recCand, ← candidate_fourth_iff]
  generalize toZMod (recXX (u.eval input)) = X
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

theorem cast_one_sub_sqrtMinusOne :
    ((modulus + 1 - sqrtMinusOne : ℕ) : K) = 1 - (sqrtMinusOne : K) := by
  rw [Nat.cast_sub (by decide), Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]

/-- **When the check passes, `recipient`'s `x` is a square root of its `x²`:** `x·x = xx`. -/
theorem recipient_x_mul_self (u : Expr) (input : ℕ → F) (h : (recipient u).2.eval input = ofNat 0) :
    (recipient u).1.1.eval input * (recipient u).1.1.eval input = recXX (u.eval input) := by
  have hsq := (exists_mul_self_iff _).mp ((recipient_check_zero_iff u input).mp h)
  rw [(recipient_eval u input).1]
  apply toZMod_injective
  simp only [toZMod_mul, toZMod_add, toZMod_recCand, toZMod_inverse, toZMod_ofNat,
    cast_one_sub_sqrtMinusOne]
  have hs := zmod_sqrtMinusOne_sq
  generalize toZMod (recXX (u.eval input)) = X at hsq ⊢
  generalize ((sqrtMinusOne : ℕ) : K) = s at hs ⊢
  have h2 : ((2 : ℕ) : K) = 2 := by norm_num
  rw [h2]
  by_cases hX : X = 0
  · subst hX
    rw [zero_pow (show (modulus + 3) / 8 ≠ 0 by decide)]
    ring
  · rcases candidate_sq X hsq with hc | hc
    · generalize X ^ ((modulus + 3) / 8) = c at hc ⊢
      have hb : (c * c + X) * (2 * X)⁻¹ = 1 := by
        rw [← pow_two, hc]; field_simp [two_ne_zero_K]; ring
      rw [hb]
      linear_combination hc
    · generalize X ^ ((modulus + 3) / 8) = c at hc ⊢
      have hb : (c * c + X) * (2 * X)⁻¹ = 0 := by
        rw [← pow_two, hc, neg_add_cancel, zero_mul]
      rw [hb]
      linear_combination (-1 : K) * X * hs + s * s * hc

end Recipient

/-! ### The hinted lift (`EdwardsHinted.liftOpen` / `liftPoint`) -/

section Lift
open FieldDag

/-- **The selection rule of the lift** (H-QR in use): for `q ≠ 0`, `r ≠ 0`, the opened
`w = q·r²·(1 + b)` is a square iff (`q` is a square iff `b = 0`). So the private validity
"`q` is a square" is `sel xor b` for the public `sel = [w is a square]`. -/
theorem lift_select (q r : F) (bit : Bool) (hq : q ≠ ofNat 0) (hr : r ≠ ofNat 0) :
    (∃ s : F, s * s = q * r * r * (ofNat 1 + X25519.bitValue bit)) ↔
      ((∃ s : F, s * s = q) ↔ bit = false) := by
  rw [exists_mul_self_iff, exists_mul_self_iff, toZMod_mul, toZMod_mul, toZMod_mul,
    toZMod_one_add_bitValue]
  have hQ := toZMod_ne_zero hq
  have hR := toZMod_ne_zero hr
  generalize toZMod q = Q at hQ ⊢
  generalize toZMod r = R at hR ⊢
  have hRR : IsSquare (R * R) := ⟨R, rfl⟩
  have hRR0 : R * R ≠ 0 := mul_ne_zero hR hR
  have hQRR : IsSquare (Q * R * R) ↔ IsSquare Q := by
    rw [mul_assoc, isSquare_mul_iff hQ hRR0]; simp [hRR]
  cases bit
  · simp [hQRR]
  · simp only [if_true]
    rw [isSquare_mul_iff (mul_ne_zero (mul_ne_zero hQ hR) hR) two_ne_zero_K, hQRR]
    simp [zmod_two_not_square]

/-- **`liftOpen`'s first output (the opened `w`), for the parties' bits `a`, `a'`:** it is a square
iff (`q` is a square iff `a xor a' = 0`), where `q = u·(u² + 486662·u + 1)` and `r` is the shared
mask (`q, r ≠ 0`). Stated through `EdwardsHinted.liftOpen_eval`. -/
theorem liftOpen_square_iff (input : ℕ → F) (a a' : Bool)
    (h2 : input 2 = X25519.bitValue a) (h3 : input 3 = X25519.bitValue a')
    (hq : input 0 * (input 0 * input 0 + ofNat 486662 * input 0 + ofNat 1) ≠ ofNat 0)
    (hr : input 1 ≠ ofNat 0) :
    (∃ s : F, s * s = ((EdwardsHinted.liftOpen ()).map (Expr.eval input)).headD (ofNat 0)) ↔
      ((∃ s : F, s * s = input 0 * (input 0 * input 0 + ofNat 486662 * input 0 + ofNat 1)) ↔
        (a ^^ a') = false) := by
  rw [EdwardsHinted.liftOpen_eval]
  simp only [List.headD_cons]
  have hb : input 2 + input 3 - ofNat 2 * (input 2 * input 3) = X25519.bitValue (a ^^ a') := by
    rw [h2, h3]; exact X25519.xorBit_value a a'
  rw [hb]
  exact lift_select _ _ _ hq hr

/-- The fiber of `(r, b) ↦ q·r²·(1 + b)` over any `w` has exactly two points (`q ≠ 0`). -/
theorem lift_fiber_card (q w : F) (hq : q ≠ ofNat 0) :
    (Finset.univ.filter (fun rb : F × Bool => q * rb.1 * rb.1 * (ofNat 1 + X25519.bitValue rb.2) = w)).card = 2 := by
  classical
  have hQ := toZMod_ne_zero hq
  -- membership, in `ZMod p`
  have key : ∀ (r : F) (b : Bool), q * r * r * (ofNat 1 + X25519.bitValue b) = w ↔
      toZMod q * toZMod r * toZMod r * (if b then 2 else 1) = toZMod w := by
    intro r b
    rw [← toZMod_eq_iff, toZMod_mul, toZMod_mul, toZMod_mul, toZMod_one_add_bitValue]
  have hc0 : ∀ b : Bool, ((if b then 2 else 1) : K) ≠ 0 := by
    intro b; cases b
    · simp
    · simpa using two_ne_zero_K
  by_cases hw : toZMod w = 0
  · have hset : Finset.univ.filter (fun rb : F × Bool => q * rb.1 * rb.1 * (ofNat 1 + X25519.bitValue rb.2) = w) =
        {(ofNat 0, false), (ofNat 0, true)} := by
      ext ⟨r, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq, key, hw]
      have hr0 : toZMod r = 0 ↔ r = ofNat 0 := by rw [← toZMod_ofNat_zero, toZMod_eq_iff]
      simp only [mul_eq_zero, hQ, hc0 b, false_or, or_false, or_self, hr0]
      cases b <;> simp
    rw [hset, Finset.card_pair]
    simp
  · -- pick the bit b0 and a root S of w / (q·(1 + b0))
    have hW := hw
    generalize hWdef : toZMod w = W at hW key
    generalize hQdef : toZMod q = Q at hQ key
    obtain ⟨b0, S, hS, hS0⟩ : ∃ (b0 : Bool) (S : K), W * Q⁻¹ * (if b0 then 2 else 1 : K)⁻¹ = S * S ∧
        ∀ b : Bool, IsSquare (W * Q⁻¹ * (if b then 2 else 1 : K)⁻¹) → b = b0 := by
      have hWQ : W * Q⁻¹ ≠ 0 := mul_ne_zero hW (inv_ne_zero hQ)
      have h2i : (2 : K)⁻¹ ≠ 0 := inv_ne_zero two_ne_zero_K
      have hsq2 : IsSquare (W * Q⁻¹ * 2⁻¹) ↔ ¬ IsSquare (W * Q⁻¹) := by
        rw [isSquare_mul_iff hWQ h2i, isSquare_inv]
        simp [zmod_two_not_square]
      by_cases hsq : IsSquare (W * Q⁻¹)
      · obtain ⟨S, hS⟩ := hsq
        refine ⟨false, S, by simpa using hS, ?_⟩
        intro b hb
        cases b
        · rfl
        · simp only [if_true] at hb
          exact absurd ⟨S, hS⟩ (hsq2.mp hb)
      · obtain ⟨S, hS⟩ := hsq2.mpr hsq
        refine ⟨true, S, by simpa using hS, ?_⟩
        intro b hb
        cases b
        · simp at hb; exact absurd hb hsq
        · rfl
    have hS0' : S ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hS
      rcases mul_eq_zero.mp hS with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact hW h'
        · exact inv_ne_zero hQ h'
      · exact inv_ne_zero (hc0 b0) h
    have hSneg : S ≠ -S := by
      intro h
      apply hS0'
      have h2 : (2 : K) * S = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h two_ne_zero_K
      · exact h
    -- the fiber is {(s, b0), (-s, b0)} for s = toZMod.symm S
    have mem : ∀ (r : F) (b : Bool), q * r * r * (ofNat 1 + X25519.bitValue b) = w ↔
        b = b0 ∧ (toZMod r = S ∨ toZMod r = -S) := by
      intro r b
      rw [key]
      have hR : ∀ R : K, Q * R * R * (if b then 2 else 1 : K) = W ↔ R * R = W * Q⁻¹ * (if b then 2 else 1 : K)⁻¹ := by
        intro R
        have hc := hc0 b
        generalize (if b then (2 : K) else 1) = c at hc ⊢
        constructor
        · intro h
          rw [← h]
          have e : Q * R * R * c * Q⁻¹ * c⁻¹ = R * R * (Q * Q⁻¹) * (c * c⁻¹) := by ring
          rw [e, mul_inv_cancel₀ hQ, mul_inv_cancel₀ hc, mul_one, mul_one]
        · intro h
          rw [mul_assoc Q R R, h]
          have e : Q * (W * Q⁻¹ * c⁻¹) * c = W * (Q * Q⁻¹) * (c⁻¹ * c) := by ring
          rw [e, mul_inv_cancel₀ hQ, inv_mul_cancel₀ hc, mul_one, mul_one]
      rw [hR]
      constructor
      · intro h
        have hb : b = b0 := hS0 b ⟨toZMod r, h.symm⟩
        subst hb
        exact ⟨rfl, mul_self_eq_mul_self_iff.mp (h.trans hS)⟩
      · rintro ⟨rfl, h | h⟩ <;> rw [h, hS] <;> ring
    have hset : Finset.univ.filter (fun rb : F × Bool => q * rb.1 * rb.1 * (ofNat 1 + X25519.bitValue rb.2) = w) =
        {(toZMod.symm S, b0), (toZMod.symm (-S), b0)} := by
      ext ⟨r, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq, mem]
      have e1 : r = toZMod.symm S ↔ toZMod r = S := by
        constructor
        · intro h; rw [h, RingEquiv.apply_symm_apply]
        · intro h; rw [← h, RingEquiv.symm_apply_apply]
      have e2 : r = toZMod.symm (-S) ↔ toZMod r = -S := by
        constructor
        · intro h; rw [h, RingEquiv.apply_symm_apply]
        · intro h; rw [← h, RingEquiv.symm_apply_apply]
      rw [e1, e2]
      tauto
    rw [hset, Finset.card_pair]
    intro h
    simp only [Prod.mk.injEq, and_true] at h
    exact hSneg (toZMod.symm.injective h)

/-- **The lift's opened value is uniform** (P-HINT(b), as a probability statement): for
`q ≠ 0`, with `r` uniform in F and `b` a uniform bit, `w = q·r²·(1 + b)` is uniform on F. So it
does not depend on `q` (nor on `u`, as long as `q ≠ 0`). -/
theorem lift_opened_uniform (q : F) (hq : q ≠ ofNat 0) :
    PMF.map (fun rb : F × Bool => q * rb.1 * rb.1 * (ofNat 1 + X25519.bitValue rb.2))
      (PMF.uniformOfFintype (F × Bool)) = PMF.uniformOfFintype F := by
  classical
  apply map_uniform_of_fiber_card _ 2 (fun w => lift_fiber_card q w hq)
  rw [Fintype.card_prod, Fintype.card_bool, mul_comm]

/-- The same when `b = a xor a'` for the honest party's uniform bit `a` and any bit `a'` of the
other party (the program XORs the two parties' bits). -/
theorem lift_opened_uniform_xor (q : F) (hq : q ≠ ofNat 0) (a' : Bool) :
    PMF.map (fun ra : F × Bool => q * ra.1 * ra.1 * (ofNat 1 + X25519.bitValue (ra.2 ^^ a')))
      (PMF.uniformOfFintype (F × Bool)) = PMF.uniformOfFintype F := by
  let σ : F × Bool ≃ F × Bool := Equiv.prodCongr (Equiv.refl F)
    ⟨fun a => a ^^ a', fun a => a ^^ a', fun a => by simp, fun a => by simp⟩
  have hf : (fun ra : F × Bool => q * ra.1 * ra.1 * (ofNat 1 + X25519.bitValue (ra.2 ^^ a'))) =
      (fun rb : F × Bool => q * rb.1 * rb.1 * (ofNat 1 + X25519.bitValue rb.2)) ∘ σ := rfl
  rw [hf, ← PMF.map_comp, map_uniform_equiv, lift_opened_uniform q hq]

end Lift

end TlsMpcProofs
