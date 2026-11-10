import Std.Tactic.BVDecide

/-!
Addition modulo a public modulus on bit lists (least significant bit first),
generic in the bit type so the same definition runs on `Bool` and compiles to a
circuit. Used to recombine two additive shares of a stored per-contact scalar
(`TlsMpc/HybridKernels.lean`, `contactKey`).

One AND per bit in each of the three passes: the sum, the comparison with the
modulus (as the carry out of adding `2^(n+1) − modulus`), and the selection.

Status: checked exhaustively at small widths below (`decide`). The general
statement `toNat (modAdd m a b) = (toNat a + toNat b) % m` for inputs below the
modulus is not yet proved.
-/
namespace TlsMpc.ModAdd
open Std.Tactic.BVDecide

structure Bits (B : Type) where
  xor : B → B → B
  and : B → B → B
  zero : B
  one : B

def boolBits : Bits Bool := ⟨(· ^^ ·), (· && ·), false, true⟩
def exprBits : Bits (BVExpr 1) :=
  ⟨fun a b => .bin a .xor b, fun a b => .bin a .and b, .const 0#1, .const 1#1⟩

/-- Ripple addition of equal-length lists: sum bits and the carry out. -/
def addBits (o : Bits B) : List B → List B → B → List B × B
  | a :: as, b :: bs, c =>
      let rest := addBits o as bs (o.xor c (o.and (o.xor a c) (o.xor b c)))
      (o.xor (o.xor a b) c :: rest.1, rest.2)
  | _, _, c => ([], c)

/-- Ripple addition of a public constant: sum bits and the carry out. -/
def addConst (o : Bits B) : List B → List Bool → B → List B × B
  | a :: as, k :: ks, c =>
      let both := o.and a c
      let either := o.xor a c
      let rest := addConst o as ks (if k then o.xor either both else both)
      ((if k then o.xor either o.one else either) :: rest.1, rest.2)
  | _, _, c => ([], c)

def natBits (width value : Nat) : List Bool := (List.range width).map value.testBit

/-- `(a + b) mod modulus` for `a, b < modulus ≤ 2^n`, `n` the common length. -/
def modAdd (o : Bits B) (modulus : Nat) (a b : List B) : List B :=
  let sum := addBits o a b o.zero
  let wide := sum.1 ++ [sum.2]
  let reduced := addConst o wide (natBits wide.length (2 ^ wide.length - modulus)) o.zero
  ((wide.zip reduced.1).take a.length).map (fun pair => o.xor pair.1 (o.and reduced.2 (o.xor pair.1 pair.2)))

def toNat : List Bool → Nat
  | [] => 0
  | bit :: rest => bit.toNat + 2 * toNat rest

/-- Exhaustive at width 4 for a prime, a power of two and an even modulus. -/
example : ∀ a b : Fin 11, toNat (modAdd boolBits 11 (natBits 4 a) (natBits 4 b)) = (a.val + b.val) % 11 := by decide
example : ∀ a b : Fin 16, toNat (modAdd boolBits 16 (natBits 4 a) (natBits 4 b)) = (a.val + b.val) % 16 := by decide
example : ∀ a b : Fin 10, toNat (modAdd boolBits 10 (natBits 4 a) (natBits 4 b)) = (a.val + b.val) % 10 := by decide
/-- Exhaustive at width 5 for a prime just below the top. -/
example : ∀ a b : Fin 31, toNat (modAdd boolBits 31 (natBits 5 a) (natBits 5 b)) = (a.val + b.val) % 31 := by decide

/-! ### Bytes -/

def byteBits (byte : BVExpr 8) : List (BVExpr 1) := (List.range 8).map (fun i => .extract i 1 byte)

def packBits : (n : Nat) → (Nat → BVExpr 1) → BVExpr n
  | 0, _ => .const 0#0
  | n + 1, bit => .append (bit n) (packBits n bit) (by omega)

def bitsByte (bits : List (BVExpr 1)) : BVExpr 8 := packBits 8 (fun i => bits.getD i (.const 0#1))

def chunks : Nat → List (BVExpr 1) → List (List (BVExpr 1))
  | 0, _ => []
  | count + 1, bits => bits.take 8 :: chunks count (bits.drop 8)

/-- Modular addition of two little-endian byte strings of equal length. -/
def modAddBytes (modulus : Nat) (a b : List (BVExpr 8)) : List (BVExpr 8) :=
  (chunks a.length (modAdd exprBits modulus (a.flatMap byteBits) (b.flatMap byteBits))).map bitsByte

end TlsMpc.ModAdd
