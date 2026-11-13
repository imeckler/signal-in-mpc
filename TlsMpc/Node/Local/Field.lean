import TlsMpc.Node.Engine
import TlsMpc.EdwardsAffine

/-!
# Local arithmetic over p = 2^255 − 19 (what a node computes in the clear)

REORGANIZATION_PLAN.md stage S11, `Local/Field.lean`. Replaces, for the Lean flows, the OpenSSL
bignum arithmetic of `split_ecdh.h` (`LocalCurve`) and `hinted_points.h` (`LocalField`): inverses,
square roots, the Legendre symbol, and the 32-byte little-endian encoding. A node runs these on
PUBLIC values and on its OWN secrets only (its scalar, its mask points); nothing here is a protocol.

The field is `FieldDag.F` (`Fin (2^255 − 19)`), the field of every field program, so a value computed
here is literally the value a program input or output denotes. Every exponentiation is square and
multiply (`FieldDagV3.powFast`, about 255 squarings): no unary power is ever evaluated.

PROVED (no hypothesis):
  * `pow_eq`, `inv_eq`: the fast power and inverse are `FieldDag.power` / `FieldDag.inverse`, the
    definitions the programs' `div` and the V3 evaluator use (`FieldDagV3.powFast_eq`).
  * `sqrt_sq`: a root `sqrt` returns squares to its argument (the candidate is checked); the
    converse (every square has a root found) is Euler's criterion, proved in the Mathlib package
    (`proofs/` `euler_criterion`), not here.
  * `sqrtM1_sq`: the constant √−1 squares to −1 (`decide` on one product).
  * `ofBytes_toBytes`, `toBytes_length`: the encoding round-trips on canonical values.
  * `isSquare_zero`, `legendre_cases`: the Legendre symbol's values.
No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Local.Field

open TlsMpc.FieldDag (F modulus ofNat power inverse)
open TlsMpc.Node.Engine (Bytes le fromLE)

/-- `x^n` by square and multiply. -/
def pow (x : F) (n : Nat) : F := TlsMpc.FieldDag.V3.powFast x n

theorem pow_eq (x : F) (n : Nat) : pow x n = power x n := TlsMpc.FieldDag.V3.powFast_eq x n

/-- The inverse by Fermat (`x^(p−2)`, zero for zero), by square and multiply. -/
def inv (x : F) : F := TlsMpc.FieldDag.V3.inverseFast x

theorem inv_eq (x : F) : inv x = inverse x := TlsMpc.FieldDag.V3.inverseFast_eq x

/-- `a / b` (`a · b^(p−2)`), as the programs' `div`. -/
def div (a b : F) : F := a * inv b

theorem div_eq (a b : F) : div a b = a * inverse b := by rw [div, inv_eq]

/-! ## Squares -/

/-- Euler's criterion's power `x^((p−1)/2)`: 1 for a nonzero square, −1 for a non-square (with
`FieldInverse`; the Mathlib package proves the criterion). -/
def euler (x : F) : F := pow x ((modulus - 1) / 2)

/-- The Legendre symbol, as the integer the C++ `BN_kronecker` returns: 0, 1 or −1. -/
def legendre (x : F) : Int := if x = 0 then 0 else if euler x = ofNat 1 then 1 else -1

/-- Whether `x` is a square (0 counts as one), by Euler's criterion. -/
def isSquare (x : F) : Bool := x == 0 || euler x == ofNat 1

theorem isSquare_zero : isSquare 0 = true := by simp [isSquare]

theorem legendre_cases (x : F) : legendre x = 0 ∨ legendre x = 1 ∨ legendre x = -1 := by
  unfold legendre
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- √−1 = 2^((p−1)/4) (`EdwardsAffine.sqrtMinusOne`). -/
def sqrtM1 : F := ofNat TlsMpc.EdwardsAffine.sqrtMinusOne

theorem sqrtM1_sq : sqrtM1 * sqrtM1 = 0 - ofNat 1 := by decide

/-- A square root for p ≡ 5 (mod 8): the candidate `c = x^((p+3)/8)` squares to `±x`; return `c`,
`c·√−1`, or `none` when `x` is not a square (neither candidate checks). -/
def sqrt (x : F) : Option F :=
  let c := pow x ((modulus + 3) / 8)
  if c * c = x then some c
  else if c * c = 0 - x then some (c * sqrtM1)
  else none

theorem neg_mul_neg (a b : F) : (0 - a) * (0 - b) = a * b := by grind

theorem mul_ofNat_one (a : F) : a * ofNat 1 = a := by
  have h1 : (ofNat 1 : F) = 1 := rfl
  rw [h1]
  grind

theorem neg_mul_neg_one (a : F) : (0 - a) * (0 - ofNat 1) = a := by
  rw [neg_mul_neg, mul_ofNat_one]

/-- **A root squares to its argument.** -/
theorem sqrt_sq (x r : F) (h : sqrt x = some r) : r * r = x := by
  unfold sqrt at h
  dsimp only at h
  split at h
  · next hc => simp only [Option.some.injEq] at h; subst h; exact hc
  · split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst h
      have e : pow x ((modulus + 3) / 8) * sqrtM1 * (pow x ((modulus + 3) / 8) * sqrtM1) =
          (pow x ((modulus + 3) / 8) * pow x ((modulus + 3) / 8)) * (sqrtM1 * sqrtM1) := by grind
      rw [e, hc, sqrtM1_sq, neg_mul_neg_one]
    · cases h

/-- The root with the given parity of its canonical value (`x` or `p − x`). -/
def withParity (r : F) (odd : Bool) : F := if (r.val % 2 == 1) == odd then r else 0 - r

theorem withParity_sq (r : F) (odd : Bool) : withParity r odd * withParity r odd = r * r := by
  unfold withParity
  split
  · rfl
  · grind

/-! ## The 32-byte little-endian encoding -/

/-- A field element as 32 little-endian bytes (its canonical value). -/
def toBytes (x : F) : Bytes := le 32 x.val

theorem toBytes_length (x : F) : (toBytes x).length = 32 := TlsMpc.Node.Engine.length_le 32 x.val

/-- 32 little-endian bytes as a field element, when canonical (below p). -/
def ofBytes (b : Bytes) : Option F :=
  if h : b.length = 32 ∧ fromLE b < modulus then some ⟨fromLE b, h.2⟩ else none

theorem modulus_lt : modulus < 256 ^ 32 := by
  show 2 ^ 255 - 19 < 256 ^ 32
  decide

theorem ofBytes_toBytes (x : F) : ofBytes (toBytes x) = some x := by
  have hl := toBytes_length x
  have hv : fromLE (toBytes x) = x.val := by
    rw [toBytes, TlsMpc.Node.Engine.fromLE_le]
    exact Nat.mod_eq_of_lt (Nat.lt_trans x.isLt modulus_lt)
  have hlt : fromLE (toBytes x) < modulus := by rw [hv]; exact x.isLt
  unfold ofBytes
  rw [dif_pos ⟨hl, hlt⟩]
  exact congrArg some (Fin.ext hv)

/-- The value of little-endian bytes (any length), reduced mod p. -/
def ofBytesReduced (b : Bytes) : F := ofNat (fromLE b)

#print axioms sqrt_sq
#print axioms ofBytes_toBytes

end TlsMpc.Node.Local.Field
