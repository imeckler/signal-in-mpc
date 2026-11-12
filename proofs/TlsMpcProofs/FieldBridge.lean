import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import TlsMpc.FieldDag
import TlsMpc.X25519

/-!
# The main package's field is `ZMod p`

`TlsMpc.FieldDag.F` is `Fin modulus` (`modulus = 2²⁵⁵ − 19`) with Lean core's `Fin` arithmetic;
`ofNat`, `power` and `inverse` are the main package's own definitions, and `X25519.concrete` packs
the same operations for the curve formulas. This file shows that all of them are `ZMod p`
arithmetic through one ring isomorphism `toZMod`, so a proof can move a statement into `ZMod p`
(where Mathlib's number theory lives) and back.

Nothing here assumes `p` is prime except `toZMod_inverse`, which takes the primality fact as an
instance argument (discharged in `TlsMpcProofs.Prime25519`).
-/

namespace TlsMpcProofs
open TlsMpc

/-- The main package's field, as a ring isomorphism to Mathlib's `ZMod p`. -/
def toZMod : FieldDag.F ≃+* ZMod FieldDag.modulus := ZMod.finEquiv FieldDag.modulus

/-- The core `Fin` operations used by the main package are the ring operations `toZMod` respects. -/
theorem toZMod_add (a b : FieldDag.F) : toZMod (a + b) = toZMod a + toZMod b := map_add toZMod a b
theorem toZMod_sub (a b : FieldDag.F) : toZMod (a - b) = toZMod a - toZMod b := map_sub toZMod a b
theorem toZMod_mul (a b : FieldDag.F) : toZMod (a * b) = toZMod a * toZMod b := map_mul toZMod a b
theorem toZMod_neg (a : FieldDag.F) : toZMod (-a) = -toZMod a := map_neg toZMod a

theorem toZMod_injective : Function.Injective toZMod := toZMod.injective

theorem toZMod_eq_iff (a b : FieldDag.F) : toZMod a = toZMod b ↔ a = b := toZMod.injective.eq_iff

/-- The main package's constants: `ofNat n` is `n mod p`. -/
theorem toZMod_ofNat (n : ℕ) : toZMod (FieldDag.ofNat n) = (n : ZMod FieldDag.modulus) := by
  induction n with
  | zero =>
    have h : FieldDag.ofNat 0 = 0 := Fin.ext (by simp [FieldDag.ofNat, Fin.ofNat])
    rw [h, map_zero, Nat.cast_zero]
  | succ n ih =>
    have h : FieldDag.ofNat (n + 1) = FieldDag.ofNat n + 1 := by
      apply Fin.ext
      simp only [FieldDag.ofNat, Fin.ofNat, Fin.val_add]
      have h1 : (1 : FieldDag.F).val = 1 := rfl
      rw [h1, Nat.mod_add_mod]
    rw [h, map_add, ih, map_one, Nat.cast_succ]

theorem toZMod_zero : toZMod (0 : FieldDag.F) = 0 := map_zero toZMod
theorem toZMod_one : toZMod (1 : FieldDag.F) = 1 := map_one toZMod

/-- The main package's `power` (a linear recursion) is the power in `ZMod p`. -/
theorem toZMod_power (x : FieldDag.F) (n : ℕ) : toZMod (FieldDag.power x n) = toZMod x ^ n := by
  induction n with
  | zero => simp [FieldDag.power, toZMod_ofNat]
  | succ n ih =>
    show toZMod (x * FieldDag.power x n) = _
    rw [toZMod_mul, ih, pow_succ, mul_comm]

/-- The main package's `inverse` (Fermat: `x^(p−2)`, zero at zero) is the field inverse of
`ZMod p`, given that `p` is prime. -/
theorem toZMod_inverse [Fact (Nat.Prime FieldDag.modulus)] (x : FieldDag.F) :
    toZMod (FieldDag.inverse x) = (toZMod x)⁻¹ := by
  rw [FieldDag.inverse, toZMod_power]
  by_cases hx : toZMod x = 0
  · rw [hx, inv_zero, zero_pow]
    decide
  · have h := ZMod.pow_card_sub_one_eq_one hx
    have hp : FieldDag.modulus - 1 = (FieldDag.modulus - 2) + 1 := by decide
    rw [hp, pow_succ] at h
    exact eq_inv_of_mul_eq_one_left h

/-- `X25519.concrete` (the operations every curve formula is evaluated with) is `F`'s arithmetic. -/
theorem concrete_ops :
    X25519.concrete.add = (· + ·) ∧ X25519.concrete.sub = (· - ·) ∧
      X25519.concrete.mul = (· * ·) ∧ X25519.concrete.const = FieldDag.ofNat :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Fast modular exponentiation, evaluated by the kernel

`powModAux` is square-and-multiply on `Nat` with structural recursion on a fuel argument, so the
kernel evaluates it with its GMP-accelerated `Nat` operations (`decide +kernel`, no
`native_decide`). -/

/-- Square-and-multiply over `fuel` bits of `e`, most significant first. -/
def powModAux (b e m : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | k + 1 => if e % 2 = 1 then (powModAux b (e / 2) m k ^ 2 % m) * b % m
             else powModAux b (e / 2) m k ^ 2 % m

/-- `b ^ e mod m` for `e < 2²⁵⁶`. -/
def powMod (b e m : ℕ) : ℕ := powModAux b e m 256

theorem powModAux_cast (b e m k : ℕ) (he : e < 2 ^ k) :
    ((powModAux b e m k : ℕ) : ZMod m) = (b : ZMod m) ^ e := by
  induction k generalizing e with
  | zero =>
    have : e = 0 := by omega
    subst this; simp [powModAux, ZMod.natCast_mod]
  | succ k ih =>
    have he' : e / 2 < 2 ^ k := by
      rw [pow_succ] at he; omega
    have hsplit : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
    simp only [powModAux]
    split_ifs with h
    · simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, ih (e / 2) he']
      conv_rhs => rw [hsplit, h, pow_add, pow_mul, pow_one]
      ring
    · have h0 : e % 2 = 0 := by omega
      simp only [ZMod.natCast_mod, Nat.cast_pow, ih (e / 2) he']
      conv_rhs => rw [hsplit, h0, add_zero, pow_mul]
      ring

/-- A power in `ZMod m` computed by `powMod` (exponent below `2²⁵⁶`). -/
theorem zmod_pow_eq_powMod {m : ℕ} (b e : ℕ) (he : e < 2 ^ 256) :
    (b : ZMod m) ^ e = ((powMod b e m : ℕ) : ZMod m) :=
  (powModAux_cast b e m 256 he).symm

end TlsMpcProofs
