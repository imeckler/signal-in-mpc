import TlsMpc.FieldDag
import TlsMpc.X25519

/-!
Field-side programs used when bits enter the prime field: a bitness check, the
XOR of two bit shares, and the recomposition of 255 bits against a reference.
They are `FieldDag` expressions, compiled by its validated compiler.

What is proved: on bit inputs the check value is zero and the XOR is the XOR;
the recomposition expression is Horner evaluation minus the reference. The
converse of the bitness check (a zero product forces a bit) needs the field to
have no zero divisors and is not mechanised here.
-/
namespace TlsMpc.FieldBits
open FieldDag

/-- `b * (b - 1)`: zero when `b` is a bit. Input 0. -/
def bitCheck : Expr := .bin .mul (.input 0) (.bin .sub (.input 0) (.const 1))

/-- `a + b - 2ab`. Inputs 0 and 1. -/
def bitXor : Expr := X25519.xorBit X25519.symbolic (.input 0) (.input 1)

/-- Horner form of `Σ 2^i · bit_i` over the given expressions, most significant last. -/
def horner : List Expr → Expr
  | [] => .const 0
  | b :: rest => .bin .add b (.bin .mul (.const 2) (horner rest))

def hornerValue : List F → F
  | [] => ofNat 0
  | b :: rest => b + ofNat 2 * hornerValue rest

/-- `Σ_{i<255} 2^i · input i  −  input 255`: zero when the bits recompose to the reference. -/
def recompose : Expr :=
  .bin .sub (horner ((List.range 255).map Expr.input)) (.input 255)

/-- `x·r` then `z·r` (inputs 0, 1, 2): both coordinates of a projective pair
scaled by the same mask, so that `z·r` can be opened and inverted in the clear. -/
def maskPair : List Expr := [.bin .mul (.input 0) (.input 2), .bin .mul (.input 1) (.input 2)]

theorem maskPair_eval (input : Nat → F) :
    maskPair.map (Expr.eval input) = [input 0 * input 2, input 1 * input 2] := rfl

theorem bitCheck_bit (input : Nat → F) (b : Bool) (h : input 0 = X25519.bitValue b) :
    bitCheck.eval input = 0 := by
  simp only [bitCheck, Expr.eval, Bin.eval, h]
  cases b <;> decide

theorem bitXor_bits (input : Nat → F) (a b : Bool)
    (ha : input 0 = X25519.bitValue a) (hb : input 1 = X25519.bitValue b) :
    bitXor.eval input = X25519.bitValue (a ^^ b) := by
  have h := X25519.xorBit_map (X25519.evaluationHom input) (.input 0) (.input 1)
  rw [bitXor, h]
  simp only [Expr.eval, ha, hb]
  exact X25519.xorBit_value a b

theorem horner_eval (input : Nat → F) (bits : List Expr) :
    (horner bits).eval input = hornerValue (bits.map (Expr.eval input)) := by
  induction bits with
  | nil => rfl
  | cons b rest ih => simp only [horner, Expr.eval, Bin.eval, List.map_cons, hornerValue, ih]

theorem recompose_eval (input : Nat → F) :
    recompose.eval input = hornerValue ((List.range 255).map input) - input 255 := by
  simp only [recompose, Expr.eval, Bin.eval, horner_eval, List.map_map]
  rfl

#print axioms bitCheck_bit
#print axioms bitXor_bits
#print axioms recompose_eval

end TlsMpc.FieldBits
