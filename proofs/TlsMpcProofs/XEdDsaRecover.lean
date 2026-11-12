import TlsMpcProofs.QuadraticResidue

/-!
# XEdDSA `recover`: the square root through `X25519.powBits`

`Signal.XEdDsaField.recover` (the `xeddsa-recover` field program, evaluated with
`X25519.concrete`; `XEdDsaField.compiled_output_correct` links the compiled artifact to
`run X25519.concrete true input = recover X25519.concrete (input 0)`) computes, from a Montgomery
`u`:

  y = (u − 1)/(u + 1),  v = d·y² + 1,  xx = (y² − 1)/v,  c = xx^((p+3)/8),
  x = c if c² = xx else c·√−1,  valid = [u + 1 ≠ 0]·[v ≠ 0]·[x² = xx].

Every power is computed by `X25519.powBits` (255-step square-and-multiply over the big-endian
bits of the exponent), every zero test by `zero x = 1 − x^(p−1)`, every inverse by
`X25519.inverse`. Proved here:

* **`powBits` is the power** (`toZMod_powBits`): `powBits x acc bits = acc^(2^|bits|) · x^(value
  of bits)`; hence `exponent x n = x^n` for `n < 2²⁵⁵` (`exponent_eq_power`),
  `X25519.inverse = FieldDag.inverse` (`x25519_inverse_eq`), and `zero x` is the indicator of
  `x = 0` (`zero_eq_ite`), all for the concrete field.
* **What `recover` computes** (`recover_eq`): `[valid, x, y]` with the value forms `xedValid`,
  `xedX`, `xedY` below (and `run X25519.concrete true input = recover X25519.concrete (input 0)`,
  `run_recovery_eq`).
* **The same square-root correctness as for `EdwardsAffine.recipient`**, for
  `recover X25519.concrete u = [valid, x, y]`:
  `valid` is `0` or `1` (`recover_valid_zero_or_one`); `valid = 1` iff `u + 1 ≠ 0`, `v ≠ 0`
  and `xx` is a square (`recover_valid_iff`); whenever `xx` is a square, `x·x = xx`
  (`recover_x_mul_self`), so in particular when `valid = 1` (`recover_x_mul_self_of_valid`);
  and `y` is `(u − 1)/(u + 1)` (`recover_y`). (Stronger than `recipient_x_mul_self`, whose
  hypothesis is that the check passed; here the root is correct whenever one exists.)

Not stated: that `(x, y)` is on the Edwards curve or is the image of the Montgomery point (that
reading needs H-GROUP's formulas), the sign of `x` (not normalised by `recover`, as its docstring
says), and anything about `doubleScalar`.
-/

namespace TlsMpcProofs
open TlsMpc FieldDag

/-! ### `powBits` computes the power -/

/-- Big-endian value of a bit list, starting from the accumulator `n`. -/
def bitsValue : ℕ → List Bool → ℕ
  | n, [] => n
  | n, b :: rest => bitsValue (2 * n + b.toNat) rest

theorem bitsValue_eq (n : ℕ) (l : List Bool) : bitsValue n l = n * 2 ^ l.length + bitsValue 0 l := by
  induction l generalizing n with
  | nil => simp [bitsValue]
  | cons b rest ih =>
    show bitsValue (2 * n + b.toNat) rest = n * 2 ^ (rest.length + 1) + bitsValue (2 * 0 + b.toNat) rest
    rw [ih (2 * n + b.toNat), ih (2 * 0 + b.toNat), pow_succ]
    ring

/-- The bits `testBit n (k−1), …, testBit n 0` (as `exponent` and `inverseBits` list them) have
value `n mod 2^k`. -/
theorem bitsValue_testBits (n k : ℕ) :
    bitsValue 0 ((List.range k).reverse.map (fun i => n.testBit i)) = n % 2 ^ k := by
  induction k with
  | zero => simp [bitsValue, Nat.mod_one]
  | succ k ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons]
    show bitsValue (2 * 0 + (n.testBit k).toNat) _ = _
    rw [bitsValue_eq, List.length_map, List.length_reverse, List.length_range, ih]
    rw [Nat.toNat_testBit, Nat.mod_pow_succ]
    ring

theorem concrete_add (a b : F) : X25519.concrete.add a b = a + b := rfl
theorem concrete_sub (a b : F) : X25519.concrete.sub a b = a - b := rfl
theorem concrete_mul (a b : F) : X25519.concrete.mul a b = a * b := rfl
theorem concrete_const (n : ℕ) : X25519.concrete.const n = ofNat n := rfl

/-- **`X25519.powBits` on the concrete field is the power:**
`powBits x acc bits = acc^(2^|bits|) · x^(big-endian value of bits)`. -/
theorem toZMod_powBits (x acc : F) (bits : List Bool) :
    toZMod (X25519.powBits X25519.concrete x acc bits) =
      toZMod acc ^ (2 ^ bits.length) * toZMod x ^ bitsValue 0 bits := by
  induction bits generalizing acc with
  | nil => simp [X25519.powBits, bitsValue]
  | cons b rest ih =>
    have e : 2 ^ (rest.length + 1) = 2 ^ rest.length + 2 ^ rest.length := by rw [pow_succ]; ring
    rw [List.length_cons, e, pow_add]
    cases b
    · show toZMod (X25519.powBits X25519.concrete x (acc * acc) rest) = _ * _ * toZMod x ^ bitsValue 0 rest
      rw [ih, toZMod_mul, mul_pow]
    · show toZMod (X25519.powBits X25519.concrete x (acc * acc * x) rest) = _ * _ * toZMod x ^ bitsValue 1 rest
      rw [ih, bitsValue_eq 1 rest, one_mul, toZMod_mul, toZMod_mul, mul_pow, mul_pow, pow_add]
      ring

/-- **`XEdDsaField.exponent x n` is `x^n`** for `n < 2²⁵⁵` (all exponents it is used with). -/
theorem exponent_eq_power (x : F) (n : ℕ) (hn : n < 2 ^ 255) :
    Signal.XEdDsaField.exponent X25519.concrete x n = power x n := by
  apply toZMod_injective
  have hb : bitsValue 0 ((List.range 255).reverse.map n.testBit) = n := by
    rw [bitsValue_testBits n 255, Nat.mod_eq_of_lt hn]
  rw [Signal.XEdDsaField.exponent, toZMod_powBits, hb, concrete_const, toZMod_ofNat_one, one_pow,
    one_mul, toZMod_power]

/-- **`X25519.inverse` on the concrete field is `FieldDag.inverse`** (`x^(p−2)`). -/
theorem x25519_inverse_eq (x : F) : X25519.inverse X25519.concrete x = inverse x := by
  apply toZMod_injective
  have hb : bitsValue 0 X25519.inverseBits = modulus - 2 := by
    rw [X25519.inverseBits, bitsValue_testBits, Nat.mod_eq_of_lt (show modulus - 2 < 2 ^ 255 by decide)]
  rw [X25519.inverse, toZMod_powBits, hb, concrete_const, toZMod_ofNat_one, one_pow, one_mul,
    inverse, toZMod_power]

/-- `x^(p−1)` in `ZMod p` is the indicator of `x ≠ 0`. -/
theorem zmod_pow_sub_one (X : K) : X ^ (modulus - 1) = if X = 0 then 0 else 1 := by
  split_ifs with h
  · rw [h, zero_pow (show modulus - 1 ≠ 0 by decide)]
  · exact ZMod.pow_card_sub_one_eq_one h

/-- **`XEdDsaField.zero x` is the indicator of `x = 0`.** -/
theorem toZMod_zero_ind (x : F) :
    toZMod (Signal.XEdDsaField.zero X25519.concrete x) = if toZMod x = 0 then 1 else 0 := by
  rw [Signal.XEdDsaField.zero, concrete_sub, concrete_const, toZMod_sub, toZMod_ofNat_one,
    exponent_eq_power _ _ (show modulus - 1 < 2 ^ 255 by decide), toZMod_power, zmod_pow_sub_one]
  split_ifs <;> ring

/-- The indicator of `x = 0` in `F`. -/
def ind (x : F) : F := if x = ofNat 0 then ofNat 1 else ofNat 0

theorem toZMod_ind (x : F) : toZMod (ind x) = if toZMod x = 0 then 1 else 0 := by
  have hx : toZMod x = 0 ↔ x = ofNat 0 := by rw [← toZMod_ofNat_zero, toZMod_eq_iff]
  rw [ind]
  by_cases h : x = ofNat 0
  · rw [if_pos (hx.mpr h), if_pos h, toZMod_ofNat_one]
  · rw [if_neg (fun h' => h (hx.mp h')), if_neg h, toZMod_ofNat_zero]

theorem zero_eq_ind (x : F) : Signal.XEdDsaField.zero X25519.concrete x = ind x := by
  apply toZMod_injective
  rw [toZMod_zero_ind, toZMod_ind]

theorem zero_eq_ite (x : F) :
    Signal.XEdDsaField.zero X25519.concrete x = if x = ofNat 0 then ofNat 1 else ofNat 0 := by
  apply toZMod_injective
  rw [toZMod_zero_ind]
  have hx : toZMod x = 0 ↔ x = ofNat 0 := by rw [← toZMod_ofNat_zero, toZMod_eq_iff]
  by_cases h : x = ofNat 0
  · rw [if_pos (hx.mpr h), if_pos h, toZMod_ofNat_one]
  · rw [if_neg (fun h' => h (hx.mp h')), if_neg h, toZMod_ofNat_zero]

/-! ### `recover`, as values -/

section Recover
open Signal.XEdDsaField

/-- `y = (u − 1)/(u + 1)`. -/
def xedY (U : F) : F := (U - ofNat 1) * inverse (U + ofNat 1)

/-- `v = d·y² + 1`. -/
def xedV (U : F) : F := ofNat d * (xedY U * xedY U) + ofNat 1

/-- `xx = (y² − 1)/v`, the value `recover` square-roots. -/
def xedXX (U : F) : F := (xedY U * xedY U - ofNat 1) * inverse (xedV U)

/-- The candidate `c = xx^((p+3)/8)`. -/
def xedCand (U : F) : F := power (xedXX U) ((modulus + 3) / 8)

/-- `x = c` if `c² = xx`, else `c·√−1` (as `recover`'s `select` computes it). -/
def xedX (U : F) : F :=
  xedCand U * ofNat sqrtM1 + ind (xedCand U * xedCand U - xedXX U) * (xedCand U - xedCand U * ofNat sqrtM1)

/-- `valid = [u + 1 ≠ 0]·[v ≠ 0]·[x² = xx]`, written as `recover` computes it. -/
def xedValid (U : F) : F :=
  (ofNat 1 - ind (U + ofNat 1)) * ((ofNat 1 - ind (xedV U)) * ind (xedX U * xedX U - xedXX U))

/-- **What `recover` computes on the concrete field:** `[valid, x, y]`. -/
theorem recover_eq (U : F) : recover X25519.concrete U = [xedValid U, xedX U, xedY U] := by
  simp only [recover, concrete_add, concrete_sub, concrete_mul, concrete_const, X25519.select,
    x25519_inverse_eq, zero_eq_ind, exponent_eq_power _ _ (show (modulus + 3) / 8 < 2 ^ 255 by decide),
    xedValid, xedX, xedCand, xedXX, xedV, xedY]

/-- The `xeddsa-recover` program (`run … true`) is `recover` of input 0. -/
theorem run_recovery_eq (input : ℕ → F) :
    Signal.XEdDsaField.run X25519.concrete true input = recover X25519.concrete (input 0) := by
  simp only [Signal.XEdDsaField.run, ↓reduceIte]

/-- The outputs `[valid, x, y]` of `recover`, by name. (Stated through list injectivity on
purpose: a definitional unfolding such as `[a, b, c][2]? = some c` next to these terms makes
Lean's defeq checker unfold `power` with a 255-bit exponent.) -/
theorem recover_components (U valid x y : F) (h : recover X25519.concrete U = [valid, x, y]) :
    valid = xedValid U ∧ x = xedX U ∧ y = xedY U := by
  rw [recover_eq] at h
  simp only [List.cons.injEq, and_true] at h
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- **`recover`'s `y` is `(u − 1)/(u + 1)`.** -/
theorem recover_y (U valid x y : F) (h : recover X25519.concrete U = [valid, x, y]) : y = xedY U :=
  (recover_components U valid x y h).2.2

theorem zmod_sqrtM1_sq : ((sqrtM1 : ℕ) : K) * (sqrtM1 : ℕ) = -1 := by
  rw [sqrtM1_eq_sqrtMinusOne]; exact zmod_sqrtMinusOne_sq

/-- **When `xx` is a square, `recover`'s `x` is a square root of it** (the candidate argument
for p ≡ 5 mod 8, as for `recipient`). -/
theorem xedX_mul_self (U : F) (hsq : ∃ r : F, r * r = xedXX U) : xedX U * xedX U = xedXX U := by
  have hS := (exists_mul_self_iff _).mp hsq
  have hcand : toZMod (xedCand U) = toZMod (xedXX U) ^ ((modulus + 3) / 8) := by
    rw [xedCand, toZMod_power]
  have hz : ∀ a : F, a = ofNat 0 ↔ toZMod a = 0 := by
    intro a; rw [← toZMod_ofNat_zero, toZMod_eq_iff]
  apply toZMod_injective
  rw [xedX, ind]
  by_cases h : xedCand U * xedCand U - xedXX U = ofNat 0
  · rw [if_pos h]
    have h' := (hz _).mp h
    rw [toZMod_sub, toZMod_mul] at h'
    simp only [toZMod_mul, toZMod_add, toZMod_sub, toZMod_ofNat_one]
    linear_combination h'
  · rw [if_neg h]
    have h' : toZMod (xedCand U) * toZMod (xedCand U) - toZMod (xedXX U) ≠ 0 := by
      intro h'; apply h; rw [hz, toZMod_sub, toZMod_mul]; exact h'
    have hs : toZMod (ofNat sqrtM1) * toZMod (ofNat sqrtM1) = -1 := by
      rw [toZMod_ofNat]; exact zmod_sqrtM1_sq
    simp only [toZMod_mul, toZMod_add, toZMod_sub, toZMod_ofNat_zero]
    rw [hcand] at h' ⊢
    generalize toZMod (xedXX U) = X at hS h' ⊢
    generalize toZMod (ofNat sqrtM1) = s at hs ⊢
    rcases candidate_sq X hS with hc | hc
    · exact absurd (by rw [← pow_two, hc, sub_self] :
        X ^ ((modulus + 3) / 8) * X ^ ((modulus + 3) / 8) - X = 0) h'
    · generalize X ^ ((modulus + 3) / 8) = c at hc ⊢
      linear_combination (-1 : K) * X * hs + s * s * hc

/-- **`recover`'s `x` is a square root of `xx` whenever `xx` is a square.** -/
theorem recover_x_mul_self (U valid x y : F) (h : recover X25519.concrete U = [valid, x, y])
    (hsq : ∃ r : F, r * r = xedXX U) : x * x = xedXX U := by
  rw [(recover_components U valid x y h).2.1]; exact xedX_mul_self U hsq

theorem eq_zero_iff_toZMod (x : F) : x = ofNat 0 ↔ toZMod x = 0 := by
  rw [← toZMod_ofNat_zero, toZMod_eq_iff]

/-- The product of indicators `recover` uses for `valid` is `0` or `1`. -/
theorem ind_prod_zero_or_one (a b c : F) :
    (ofNat 1 - ind a) * ((ofNat 1 - ind b) * ind c) = ofNat 1 ∨
      (ofNat 1 - ind a) * ((ofNat 1 - ind b) * ind c) = ofNat 0 := by
  have key : toZMod ((ofNat 1 - ind a) * ((ofNat 1 - ind b) * ind c)) = 1 ∨
      toZMod ((ofNat 1 - ind a) * ((ofNat 1 - ind b) * ind c)) = 0 := by
    rw [toZMod_mul, toZMod_mul, toZMod_sub, toZMod_sub, toZMod_ind, toZMod_ind, toZMod_ind,
      toZMod_ofNat_one]
    split_ifs <;> simp
  rcases key with h | h
  · left; apply toZMod_injective; rw [h, toZMod_ofNat_one]
  · right; apply toZMod_injective; rw [h, toZMod_ofNat_zero]

/-- The product of indicators is `1` iff `a ≠ 0`, `b ≠ 0`, `c = 0`. -/
theorem ind_prod_eq_one (a b c : F) :
    (ofNat 1 - ind a) * ((ofNat 1 - ind b) * ind c) = ofNat 1 ↔
      a ≠ ofNat 0 ∧ b ≠ ofNat 0 ∧ c = ofNat 0 := by
  refine Iff.trans (toZMod_eq_iff _ _).symm ?_
  rw [toZMod_mul, toZMod_mul, toZMod_sub, toZMod_sub, toZMod_ind, toZMod_ind, toZMod_ind,
    toZMod_ofNat_one, ne_eq, ne_eq, eq_zero_iff_toZMod a, eq_zero_iff_toZMod b, eq_zero_iff_toZMod c]
  by_cases h1 : toZMod a = 0 <;> by_cases h2 : toZMod b = 0 <;> by_cases h3 : toZMod c = 0 <;>
    simp [h1, h2, h3]

/-- **`recover`'s validity output is `0` or `1`.** -/
theorem recover_valid_zero_or_one (U valid x y : F) (h : recover X25519.concrete U = [valid, x, y]) :
    valid = ofNat 1 ∨ valid = ofNat 0 := by
  rw [(recover_components U valid x y h).1, xedValid]
  exact ind_prod_zero_or_one _ _ _

/-- **`recover`'s validity output is `1` exactly when `u + 1 ≠ 0`, `v ≠ 0` and `xx` is a
square** (otherwise it is `0`). -/
theorem recover_valid_iff (U valid x y : F) (h : recover X25519.concrete U = [valid, x, y]) :
    valid = ofNat 1 ↔ U + ofNat 1 ≠ ofNat 0 ∧ xedV U ≠ ofNat 0 ∧ ∃ r : F, r * r = xedXX U := by
  rw [(recover_components U valid x y h).1]
  have hiff : xedX U * xedX U - xedXX U = ofNat 0 ↔ ∃ r : F, r * r = xedXX U := by
    constructor
    · intro h
      refine ⟨xedX U, ?_⟩
      apply toZMod_injective
      have h' := congrArg toZMod h
      rw [toZMod_sub, toZMod_ofNat_zero] at h'
      exact sub_eq_zero.mp h'
    · intro h
      rw [xedX_mul_self U h]
      apply toZMod_injective
      rw [toZMod_sub, sub_self, toZMod_ofNat_zero]
  rw [xedValid, ind_prod_eq_one, hiff]

/-- **When `valid = 1`, `x` is a square root of `xx`.** -/
theorem recover_x_mul_self_of_valid (U valid x y : F) (h : recover X25519.concrete U = [valid, x, y])
    (hv : valid = ofNat 1) : x * x = xedXX U :=
  recover_x_mul_self U valid x y h ((recover_valid_iff U valid x y h).mp hv).2.2

end Recover

end TlsMpcProofs
