import Std.Tactic.BVDecide

/-!
Addition modulo a public modulus on bit lists (least significant bit first),
generic in the bit type so the same definition runs on `Bool` and compiles to a
circuit. Used to recombine two additive shares of a stored per-contact scalar
(`TlsMpc/HybridKernels.lean`, `contactKey`).

One AND per bit in each of the three passes: the sum, the comparison with the
modulus (as the carry out of adding `2^(n+1) − modulus`), and the selection.

Proved on `Bool` (`modAdd_spec`): for equal-length inputs below the modulus,
`toNat (modAdd m a b) = (toNat a + toNat b) % m`. Not proved: that the circuit
instance (`exprBits`) evaluates to the `Bool` instance, and the byte packing
(`modAddBytes`); the exported kernel is checked numerically against a
reference by `check_contact_kernels.py`.
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

/-! ### Correctness on `Bool` -/

theorem toNat_lt : ∀ l : List Bool, toNat l < 2 ^ l.length
  | [] => by simp [toNat]
  | x :: xs => by
      have ih := toNat_lt xs
      simp only [toNat, List.length_cons, Nat.pow_succ]
      cases x <;> simp <;> omega

theorem toNat_append_single (l : List Bool) (b : Bool) :
    toNat (l ++ [b]) = toNat l + 2 ^ l.length * b.toNat := by
  induction l with
  | nil => simp [toNat]
  | cons x xs ih =>
      simp only [List.cons_append, toNat, ih, List.length_cons, Nat.pow_succ]
      generalize 2 ^ xs.length = P
      cases b <;> simp <;> omega

theorem toNat_take : ∀ (l : List Bool) (n : Nat), toNat (l.take n) = toNat l % 2 ^ n
  | _, 0 => by simp [toNat, Nat.mod_one]
  | [], n + 1 => by simp [toNat]
  | x :: xs, n + 1 => by
      have ih := toNat_take xs n
      simp only [List.take_succ_cons, toNat, ih, Nat.pow_succ]
      have pos : 0 < 2 ^ n := Nat.pow_pos (by decide)
      generalize 2 ^ n = P at pos ⊢
      generalize toNat xs = t
      have split := Nat.div_add_mod t P
      have small := Nat.mod_lt t pos
      have bit : x.toNat < 2 := by cases x <;> decide
      have value : x.toNat + 2 * t = (P * 2) * (t / P) + (x.toNat + 2 * (t % P)) := by
        have : 2 * t = 2 * (P * (t / P) + t % P) := by rw [split]
        rw [Nat.mul_add] at this
        have assoc : 2 * (P * (t / P)) = P * 2 * (t / P) := by
          rw [← Nat.mul_assoc, Nat.mul_comm 2 P]
        omega
      rw [value, Nat.mul_add_mod]
      exact (Nat.mod_eq_of_lt (by omega)).symm

theorem addBits_spec : ∀ (a b : List Bool) (c : Bool), a.length = b.length →
    (addBits boolBits a b c).1.length = a.length ∧
      toNat (addBits boolBits a b c).1 + 2 ^ a.length * (addBits boolBits a b c).2.toNat =
        toNat a + toNat b + c.toNat
  | [], [], c, _ => by simp [addBits, toNat]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: xs, y :: ys, c, h => by
      have ih := addBits_spec xs ys (boolBits.xor c (boolBits.and (boolBits.xor x c) (boolBits.xor y c)))
        (by simpa using h)
      obtain ⟨len, sum⟩ := ih
      simp only [addBits, toNat, List.length_cons, Nat.pow_succ]
      refine ⟨by simp [len], ?_⟩
      generalize (addBits boolBits xs ys _).1 = low at sum ⊢
      generalize (addBits boolBits xs ys _).2 = carry at sum ⊢
      generalize 2 ^ xs.length = P at sum ⊢
      generalize toNat low = l at sum ⊢
      generalize toNat xs = p at sum ⊢
      generalize toNat ys = q at sum ⊢
      cases x <;> cases y <;> cases c <;> cases carry <;> simp [boolBits] at sum ⊢ <;> omega

theorem addConst_spec : ∀ (a : List Bool) (k : List Bool) (c : Bool), a.length = k.length →
    (addConst boolBits a k c).1.length = a.length ∧
      toNat (addConst boolBits a k c).1 + 2 ^ a.length * (addConst boolBits a k c).2.toNat =
        toNat a + toNat k + c.toNat
  | [], [], c, _ => by simp [addConst, toNat]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: xs, y :: ys, c, h => by
      have ih := addConst_spec xs ys
        (if y then boolBits.xor (boolBits.xor x c) (boolBits.and x c) else boolBits.and x c) (by simpa using h)
      obtain ⟨len, sum⟩ := ih
      simp only [addConst, toNat, List.length_cons, Nat.pow_succ]
      refine ⟨by simp [len], ?_⟩
      generalize (addConst boolBits xs ys _).1 = low at sum ⊢
      generalize (addConst boolBits xs ys _).2 = carry at sum ⊢
      generalize 2 ^ xs.length = P at sum ⊢
      generalize toNat low = l at sum ⊢
      generalize toNat xs = p at sum ⊢
      generalize toNat ys = q at sum ⊢
      cases x <;> cases y <;> cases c <;> cases carry <;> simp [boolBits] at sum ⊢ <;> omega

theorem natBits_length (width value : Nat) : (natBits width value).length = width := by
  simp [natBits]

theorem toNat_natBits : ∀ (width value : Nat), toNat (natBits width value) = value % 2 ^ width
  | 0, value => by simp [natBits, toNat, Nat.mod_one]
  | width + 1, value => by
      have ih := toNat_natBits width value
      have step : natBits (width + 1) value = natBits width value ++ [value.testBit width] := by
        simp [natBits, List.range_succ]
      rw [step, toNat_append_single, ih, natBits_length, Nat.mod_pow_succ, Nat.toNat_testBit]

theorem select_true : ∀ (wide reduced : List Bool), wide.length = reduced.length →
    (wide.zip reduced).map (fun pair => boolBits.xor pair.1 (boolBits.and true (boolBits.xor pair.1 pair.2))) = reduced
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      have ih := select_true xs ys (by simpa using h)
      simp only [List.zip_cons_cons, List.map_cons, ih]
      cases x <;> cases y <;> rfl

theorem select_false : ∀ (wide reduced : List Bool), wide.length = reduced.length →
    (wide.zip reduced).map (fun pair => boolBits.xor pair.1 (boolBits.and false (boolBits.xor pair.1 pair.2))) = wide
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      have ih := select_false xs ys (by simpa using h)
      simp only [List.zip_cons_cons, List.map_cons, ih]
      cases x <;> cases y <;> rfl

/-- The circuit computes addition modulo `modulus` on inputs below it. -/
theorem modAdd_spec (modulus : Nat) (a b : List Bool) (lengths : a.length = b.length)
    (positive : 0 < modulus) (fits : modulus ≤ 2 ^ a.length)
    (aBound : toNat a < modulus) (bBound : toNat b < modulus) :
    toNat (modAdd boolBits modulus a b) = (toNat a + toNat b) % modulus := by
  obtain ⟨sumLength, sumValue⟩ := addBits_spec a b boolBits.zero lengths
  have wideLength : ((addBits boolBits a b boolBits.zero).1 ++ [(addBits boolBits a b boolBits.zero).2]).length
      = a.length + 1 := by simp [sumLength]
  have wideValue : toNat ((addBits boolBits a b boolBits.zero).1 ++ [(addBits boolBits a b boolBits.zero).2])
      = toNat a + toNat b := by
    rw [toNat_append_single, sumLength, sumValue]
    show _ = _ + _ + 0
    rfl
  simp only [modAdd]
  generalize (addBits boolBits a b boolBits.zero).1 ++ [(addBits boolBits a b boolBits.zero).2] = wide
    at wideLength wideValue ⊢
  obtain ⟨reducedLength, reducedValue⟩ :=
    addConst_spec wide (natBits wide.length (2 ^ wide.length - modulus)) boolBits.zero (by rw [natBits_length])
  have reducedBound := toNat_lt (addConst boolBits wide (natBits wide.length (2 ^ wide.length - modulus)) boolBits.zero).1
  rw [reducedLength] at reducedBound
  rw [toNat_natBits] at reducedValue
  generalize addConst boolBits wide (natBits wide.length (2 ^ wide.length - modulus)) boolBits.zero = reduced
    at reducedLength reducedValue reducedBound ⊢
  have zero : boolBits.zero.toNat = 0 := rfl
  rw [wideLength, wideValue, zero, Nat.pow_succ] at reducedValue
  rw [wideLength, Nat.pow_succ] at reducedBound
  rw [List.map_take, toNat_take]
  generalize 2 ^ a.length = P at fits reducedValue reducedBound ⊢
  have constant : (P * 2 - modulus) % (P * 2) = P * 2 - modulus := Nat.mod_eq_of_lt (by omega)
  rw [constant] at reducedValue
  cases carry : reduced.2 with
  | true =>
      rw [carry] at reducedValue
      simp only [Bool.toNat_true, Nat.mul_one, Nat.add_zero] at reducedValue
      rw [select_true wide reduced.1 reducedLength.symm]
      have atLeast : modulus ≤ toNat a + toNat b := by omega
      rw [Nat.mod_eq_sub_mod atLeast, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  | false =>
      rw [carry] at reducedValue
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at reducedValue
      rw [select_false wide reduced.1 reducedLength.symm, wideValue]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

#print axioms modAdd_spec

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
