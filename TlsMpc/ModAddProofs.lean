import TlsMpc.ModAdd

/-!
Refinement of the modular-addition circuit (`TlsMpc/ModAdd.lean`).

* `modAdd_map`: `modAdd` commutes with any homomorphism of its bit operations;
  `modAdd_eval` is the instance for circuit expressions: evaluating each output
  expression of `modAdd exprBits` gives the bit `modAdd boolBits` computes on
  the evaluated inputs.
* `modAddBytes_value`: for byte strings of equal length whose little-endian
  values are below the modulus (and the modulus fits in that many bytes), the
  little-endian value of the evaluated `modAddBytes` is the sum modulo the
  modulus. The arithmetic is `modAdd_spec`; this file adds only the circuit
  homomorphism and the byte packing.
* `modAddBytes_eval`: the same as an equation between byte lists, for use in a
  kernel proof: the evaluated output is the little-endian encoding `leBytes` of
  the reduced sum.
-/
namespace TlsMpc.ModAdd
open Std.Tactic.BVDecide

/-! ### The circuit is generic in its bit operations -/

structure Hom (a : Bits B) (b : Bits B') (f : B → B') : Prop where
  xor : ∀ x y, f (a.xor x y) = b.xor (f x) (f y)
  and : ∀ x y, f (a.and x y) = b.and (f x) (f y)
  zero : f a.zero = b.zero
  one : f a.one = b.one

/-- The value of a one-bit expression under an assignment. -/
def bitOf (assign : BVExpr.Assignment) (e : BVExpr 1) : Bool := (e.eval assign).getLsbD 0

theorem evaluationHom (assign : BVExpr.Assignment) : Hom exprBits boolBits (bitOf assign) := by
  constructor
  · intro x y
    show (x.eval assign ^^^ y.eval assign).getLsbD 0 = _
    exact BitVec.getLsbD_xor
  · intro x y
    show (x.eval assign &&& y.eval assign).getLsbD 0 = _
    exact BitVec.getLsbD_and
  · show (0#1).getLsbD 0 = false
    decide
  · show (1#1).getLsbD 0 = true
    decide

section Refinement
variable {a : Bits B} {b : Bits B'} {f : B → B'} (h : Hom a b f)
include h

theorem addBits_map (xs ys : List B) (c : B) :
    (addBits a xs ys c).1.map f = (addBits b (xs.map f) (ys.map f) (f c)).1 ∧
      f (addBits a xs ys c).2 = (addBits b (xs.map f) (ys.map f) (f c)).2 := by
  induction xs generalizing ys c with
  | nil => cases ys <;> exact ⟨rfl, rfl⟩
  | cons x xs ih =>
      cases ys with
      | nil => exact ⟨rfl, rfl⟩
      | cons y ys =>
          have step := ih ys (a.xor c (a.and (a.xor x c) (a.xor y c)))
          simp only [h.xor, h.and] at step
          simp only [addBits, List.map_cons, h.xor]
          rw [step.1, step.2]
          exact ⟨rfl, rfl⟩

theorem addConst_map (xs : List B) (ks : List Bool) (c : B) :
    (addConst a xs ks c).1.map f = (addConst b (xs.map f) ks (f c)).1 ∧
      f (addConst a xs ks c).2 = (addConst b (xs.map f) ks (f c)).2 := by
  induction xs generalizing ks c with
  | nil => cases ks <;> exact ⟨rfl, rfl⟩
  | cons x xs ih =>
      cases ks with
      | nil => exact ⟨rfl, rfl⟩
      | cons k ks =>
          cases k with
          | false =>
              have step := ih ks (a.and x c)
              simp only [h.and] at step
              simp only [addConst, List.map_cons, h.xor, Bool.false_eq_true, ↓reduceIte]
              rw [step.1, step.2]
              exact ⟨rfl, rfl⟩
          | true =>
              have step := ih ks (a.xor (a.xor x c) (a.and x c))
              simp only [h.xor, h.and] at step
              simp only [addConst, List.map_cons, h.xor, h.one, ↓reduceIte]
              rw [step.1, step.2]
              exact ⟨rfl, rfl⟩

/-- `modAdd` commutes with a homomorphism of the bit operations. -/
theorem modAdd_map (modulus : Nat) (xs ys : List B) :
    (modAdd a modulus xs ys).map f = modAdd b modulus (xs.map f) (ys.map f) := by
  have sum := addBits_map h xs ys a.zero
  rw [h.zero] at sum
  have wide : ((addBits a xs ys a.zero).1 ++ [(addBits a xs ys a.zero).2]).map f =
      (addBits b (xs.map f) (ys.map f) b.zero).1 ++ [(addBits b (xs.map f) (ys.map f) b.zero).2] := by
    rw [List.map_append, sum.1, List.map_cons, List.map_nil, sum.2]
  simp only [modAdd]
  rw [← wide]
  generalize (addBits a xs ys a.zero).1 ++ [(addBits a xs ys a.zero).2] = w
  have red := addConst_map h w (natBits w.length (2 ^ w.length - modulus)) a.zero
  rw [h.zero] at red
  simp only [List.length_map]
  rw [← red.1, ← red.2, List.map_map, List.zip_map, ← List.map_take, List.map_map]
  apply List.map_congr_left
  intro pair _
  simp [h.xor, h.and]

end Refinement

/-- (a) The circuit instance evaluates to the `Bool` instance. -/
theorem modAdd_eval (assign : BVExpr.Assignment) (modulus : Nat) (a b : List (BVExpr 1)) :
    (modAdd exprBits modulus a b).map (bitOf assign) =
      modAdd boolBits modulus (a.map (bitOf assign)) (b.map (bitOf assign)) :=
  modAdd_map (evaluationHom assign) modulus a b

/-! ### Bit lists -/

theorem toNat_append (l r : List Bool) : toNat (l ++ r) = toNat l + 2 ^ l.length * toNat r := by
  induction l with
  | nil => simp [toNat]
  | cons x xs ih =>
      simp only [List.cons_append, toNat, ih, List.length_cons, Nat.pow_succ]
      rw [Nat.mul_comm (2 ^ xs.length) 2, Nat.mul_assoc 2]
      generalize 2 ^ xs.length * toNat r = q
      omega

theorem modAdd_length (modulus : Nat) (a b : List Bool) (lengths : a.length = b.length) :
    (modAdd boolBits modulus a b).length = a.length := by
  obtain ⟨sumLength, _⟩ := addBits_spec a b boolBits.zero lengths
  have wideLength : ((addBits boolBits a b boolBits.zero).1 ++ [(addBits boolBits a b boolBits.zero).2]).length
      = a.length + 1 := by simp [sumLength]
  simp only [modAdd]
  generalize (addBits boolBits a b boolBits.zero).1 ++ [(addBits boolBits a b boolBits.zero).2] = wide
    at wideLength ⊢
  obtain ⟨reducedLength, _⟩ :=
    addConst_spec wide (natBits wide.length (2 ^ wide.length - modulus)) boolBits.zero (by rw [natBits_length])
  simp only [List.length_map, List.length_take, List.length_zip]
  rw [reducedLength]
  omega

/-! ### Bytes to bits -/

/-- Little-endian value of a byte string. -/
def leValue : List (BitVec 8) → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * leValue rest

/-- Little-endian encoding of a number in a given number of bytes. -/
def leBytes : Nat → Nat → List (BitVec 8)
  | 0, _ => []
  | count + 1, value => BitVec.ofNat 8 value :: leBytes count (value / 256)

theorem leBytes_length : ∀ (count value : Nat), (leBytes count value).length = count
  | 0, _ => rfl
  | count + 1, value => by simp only [leBytes, List.length_cons, leBytes_length count]

/-- A byte string is the encoding of its own value. -/
theorem leBytes_leValue : ∀ bytes : List (BitVec 8), leBytes bytes.length (leValue bytes) = bytes
  | [] => rfl
  | x :: xs => by
      have ih := leBytes_leValue xs
      have small := x.isLt
      have low : BitVec.ofNat 8 (x.toNat + 256 * leValue xs) = x := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        omega
      have high : (x.toNat + 256 * leValue xs) / 256 = leValue xs := by omega
      simp only [List.length_cons, leBytes, leValue]
      rw [low, high, ih]

/-- The encoding has the value it encodes, reduced to the available width. -/
theorem leValue_leBytes : ∀ (count value : Nat), leValue (leBytes count value) = value % 2 ^ (8 * count)
  | 0, value => by simp [leBytes, leValue, Nat.mod_one]
  | count + 1, value => by
      have ih := leValue_leBytes count (value / 256)
      have width : 2 ^ (8 * (count + 1)) = 256 * 2 ^ (8 * count) := by
        have : 8 * (count + 1) = 8 * count + 8 := by omega
        rw [this, Nat.pow_add]
        omega
      simp only [leBytes, leValue, ih, BitVec.toNat_ofNat]
      rw [width, Nat.mod_mul]

theorem bitOf_extract (assign : BVExpr.Assignment) (byte : BVExpr 8) (i : Nat) :
    bitOf assign (.extract i 1 byte) = (byte.eval assign).toNat.testBit i := by
  show ((byte.eval assign).extractLsb' i 1).getLsbD 0 = _
  simp [BitVec.testBit_toNat]

theorem byteBits_map (assign : BVExpr.Assignment) (byte : BVExpr 8) :
    (byteBits byte).map (bitOf assign) = natBits 8 (byte.eval assign).toNat := by
  simp only [byteBits, natBits, List.map_map]
  apply List.map_congr_left
  intro i _
  exact bitOf_extract assign byte i

theorem flatMap_byteBits_length (bytes : List (BVExpr 8)) :
    (bytes.flatMap byteBits).length = 8 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons x xs ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      simp [byteBits]
      omega

/-- The bits fed to the adder have the little-endian value of the bytes. -/
theorem toNat_flatMap (assign : BVExpr.Assignment) (bytes : List (BVExpr 8)) :
    toNat ((bytes.flatMap byteBits).map (bitOf assign)) = leValue (bytes.map (BVExpr.eval assign)) := by
  induction bytes with
  | nil => rfl
  | cons x xs ih =>
      rw [List.flatMap_cons, List.map_append, toNat_append, byteBits_map, toNat_natBits, natBits_length, ih]
      simp only [List.map_cons, leValue]
      have small := (x.eval assign).isLt
      omega

/-! ### Bits to bytes -/

theorem bit_toNat (x : BitVec 1) : x.toNat = (x.getLsbD 0).toNat := by
  have all : ∀ x : BitVec 1, x.toNat = (x.getLsbD 0).toNat := by decide
  exact all x

theorem eval_append_cast (left : BVExpr l) (right : BVExpr r) (h : w = l + r)
    (assign : BVExpr.Assignment) :
    (BVExpr.append left right h).eval assign = (left.eval assign ++ right.eval assign).cast h.symm := by
  cases h
  rfl

theorem packBits_toNat (assign : BVExpr.Assignment) (bit : Nat → BVExpr 1) : ∀ n : Nat,
    ((packBits n bit).eval assign).toNat = toNat ((List.range n).map (fun i => bitOf assign (bit i)))
  | 0 => by
      have empty : ∀ x : BitVec 0, x.toNat = 0 := by decide
      rw [empty]
      rfl
  | n + 1 => by
      have ih := packBits_toNat assign bit n
      have low := ((packBits n bit).eval assign).isLt
      have top := bit_toNat ((bit n).eval assign)
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, toNat_append_single, List.length_map,
        List.length_range, ← ih]
      simp only [packBits, eval_append_cast, BitVec.toNat_cast, BitVec.toNat_append]
      rw [← Nat.shiftLeft_add_eq_or_of_lt low, Nat.shiftLeft_eq, top]
      show _ = _ + 2 ^ n * (((bit n).eval assign).getLsbD 0).toNat
      rw [Nat.mul_comm]
      omega

theorem range_getD_map (l : List α) (d : α) (g : α → β) (n : Nat) (len : l.length = n) :
    (List.range n).map (fun i => g (l.getD i d)) = l.map g := by
  subst len
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < l.length := by simpa using h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem bitsByte_toNat (assign : BVExpr.Assignment) (bits : List (BVExpr 1)) (len : bits.length = 8) :
    ((bitsByte bits).eval assign).toNat = toNat (bits.map (bitOf assign)) := by
  show ((packBits 8 (fun i => bits.getD i (.const 0#1))).eval assign).toNat = _
  rw [packBits_toNat]
  exact congrArg toNat (range_getD_map bits _ (bitOf assign) 8 len)

theorem chunks_length : ∀ (count : Nat) (bits : List (BVExpr 1)), (chunks count bits).length = count
  | 0, _ => rfl
  | count + 1, bits => by simp only [chunks, List.length_cons, chunks_length count]

/-- Repacking `8 * count` bits gives bytes with the bits' value. -/
theorem chunks_value (assign : BVExpr.Assignment) : ∀ (count : Nat) (bits : List (BVExpr 1)),
    bits.length = 8 * count →
    leValue (((chunks count bits).map bitsByte).map (BVExpr.eval assign)) = toNat (bits.map (bitOf assign))
  | 0, bits, len => by
      have empty : bits = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst empty
      rfl
  | count + 1, bits, len => by
      have ih := chunks_value assign count (bits.drop 8) (by rw [List.length_drop]; omega)
      have head := bitsByte_toNat assign (bits.take 8) (by rw [List.length_take]; omega)
      have split : bits.map (bitOf assign) =
          (bits.take 8).map (bitOf assign) ++ (bits.drop 8).map (bitOf assign) := by
        rw [← List.map_append, List.take_append_drop]
      have width : min 8 bits.length = 8 := by omega
      rw [split, toNat_append, ← head, ← ih]
      simp only [chunks, List.map_cons, leValue, List.length_map, List.length_take, width]

/-! ### The byte-level adder -/

theorem modAddBytes_length (modulus : Nat) (a b : List (BVExpr 8)) :
    (modAddBytes modulus a b).length = a.length := by
  simp only [modAddBytes, List.length_map, chunks_length]

/-- (b) The little-endian value of the evaluated byte-level sum. -/
theorem modAddBytes_value (assign : BVExpr.Assignment) (modulus : Nat) (a b : List (BVExpr 8))
    (lengths : a.length = b.length) (fits : modulus ≤ 2 ^ (8 * a.length))
    (aBound : leValue (a.map (BVExpr.eval assign)) < modulus)
    (bBound : leValue (b.map (BVExpr.eval assign)) < modulus) :
    leValue ((modAddBytes modulus a b).map (BVExpr.eval assign)) =
      (leValue (a.map (BVExpr.eval assign)) + leValue (b.map (BVExpr.eval assign))) % modulus := by
  have la := flatMap_byteBits_length a
  have lb := flatMap_byteBits_length b
  have bitLengths : ((a.flatMap byteBits).map (bitOf assign)).length =
      ((b.flatMap byteBits).map (bitOf assign)).length := by
    rw [List.length_map, List.length_map, la, lb, lengths]
  have outLength : (modAdd exprBits modulus (a.flatMap byteBits) (b.flatMap byteBits)).length = 8 * a.length := by
    have same := congrArg List.length (modAdd_eval assign modulus (a.flatMap byteBits) (b.flatMap byteBits))
    rw [List.length_map, modAdd_length modulus _ _ bitLengths, List.length_map, la] at same
    exact same
  have positive : 0 < modulus := by omega
  unfold modAddBytes
  rw [chunks_value assign a.length _ outLength, modAdd_eval,
    modAdd_spec modulus _ _ bitLengths positive (by rw [List.length_map, la]; exact fits)
      (by rw [toNat_flatMap]; exact aBound) (by rw [toNat_flatMap]; exact bBound),
    toNat_flatMap, toNat_flatMap]

/-- The evaluated byte-level sum, as bytes: the little-endian encoding of the
sum of the two values modulo the modulus. -/
theorem modAddBytes_eval (assign : BVExpr.Assignment) (modulus : Nat) (a b : List (BVExpr 8))
    (lengths : a.length = b.length) (fits : modulus ≤ 2 ^ (8 * a.length))
    (aBound : leValue (a.map (BVExpr.eval assign)) < modulus)
    (bBound : leValue (b.map (BVExpr.eval assign)) < modulus) :
    (modAddBytes modulus a b).map (BVExpr.eval assign) =
      leBytes a.length
        ((leValue (a.map (BVExpr.eval assign)) + leValue (b.map (BVExpr.eval assign))) % modulus) := by
  have value := modAddBytes_value assign modulus a b lengths fits aBound bBound
  have shape := leBytes_leValue ((modAddBytes modulus a b).map (BVExpr.eval assign))
  rw [value, List.length_map, modAddBytes_length] at shape
  exact shape.symm

#print axioms modAdd_eval
#print axioms modAddBytes_value
#print axioms modAddBytes_eval
#print axioms leValue_leBytes

end TlsMpc.ModAdd
