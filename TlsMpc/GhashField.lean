import TlsMpc.GhashShares

/-!
The field laws for the repository's GHASH multiplication
(`Ghash.multiply Ghash.concrete`): `GhashShares.Laws`, i.e. commutativity and
associativity, with no hypothesis.

The proof is structural (no enumeration, no bit-blasting). Write `T` for
`Ghash.nextPower Ghash.concrete` ("multiply by x and reduce"). The multiply is

    mul x h = ⊕ᵢ xᵢ · Tⁱ h          (xᵢ = bit 127 − i of x)

so `mul x` is a polynomial in the additive map `T`. Three facts suffice:

* `mul_apply`: `mul x` commutes with every additive map that commutes with `T`.
  `T` itself is such a map, hence so is every `mul y` (`mulCommuting`), which
  gives `mul_left_comm : mul z (mul x y) = mul x (mul z y)`.
* `mul_one`: `mul x one = x` for `one = 2^127` (the polynomial 1 in GCM's bit
  order): `Tⁱ one` is the single bit `127 − i` for `i < 128`, because the
  reduction is not triggered before the bit reaches position 0.
* Then `mul x y = mul x (mul y one) = mul y (mul x one) = mul y x`, and
  associativity follows from commutativity and `mul_left_comm`.

No property of the reduction constant is used: the laws hold for the quotient
by any degree-128 polynomial. That the constant is GCM's is a matter of the
definition of `Ghash.reduction` (0xe1 followed by 120 zero bits, as in
NIST SP 800-38D), not of these theorems.
-/
namespace TlsMpc.GhashField
open Ghash GhashShares

/-- The selection in the multiply loop: the masked table entry is the entry
itself when the bit of `x` is set and zero otherwise. -/
theorem maskBit_eq (x : W) (k : Nat) :
    concrete.maskBit x k = if x.getLsbD k then BitVec.allOnes 128 else 0#128 := by
  show BitVec.replicate 128 (x.extractLsb' k 1) = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_replicate, Nat.mod_one, BitVec.getLsbD_extractLsb']
  have h' : i < 1 * 128 := by omega
  cases hb : x.getLsbD k
  · simp [hb]
  · simp only [↓reduceIte, BitVec.getLsbD_allOnes, Nat.add_zero, hb]
    simp [h', hi]

theorem mask_and (x v : W) (k : Nat) :
    concrete.and (concrete.maskBit x k) v = if x.getLsbD k then v else 0#128 := by
  show concrete.maskBit x k &&& v = _
  rw [maskBit_eq]
  cases x.getLsbD k
  · exact BitVec.zero_and
  · exact BitVec.allOnes_and

/-- An additive map that commutes with multiplication by x. -/
structure Commuting (F : W → W) : Prop where
  additive : ∀ a b, F (a ^^^ b) = F a ^^^ F b
  next : ∀ v, F (nextPower concrete v) = nextPower concrete (F v)

theorem Commuting.zero {F : W → W} (c : Commuting F) : F 0 = 0 := by
  have h := c.additive 0 0
  rw [BitVec.xor_self] at h
  have : F 0 ^^^ F 0 = F 0 := h.symm
  rw [BitVec.xor_self] at this
  exact this.symm

theorem powers_commuting {F : W → W} (c : Commuting F) (n : Nat) (v : W) :
    powers concrete n (F v) = (powers concrete n v).map F := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      show F v :: powers concrete n (nextPower concrete (F v)) =
        F v :: (powers concrete n (nextPower concrete v)).map F
      rw [← c.next, ih]

theorem loop_commuting {F : W → W} (c : Commuting F) (x : W) (table : List W) (i : Nat) (z : W) :
    multiplyLoop concrete x (table.map F) i (F z) = F (multiplyLoop concrete x table i z) := by
  induction table generalizing i z with
  | nil => rfl
  | cons v rest ih =>
      show multiplyLoop concrete x (rest.map F) (i + 1)
          (F z ^^^ concrete.and (concrete.maskBit x (127 - i)) (F v)) =
        F (multiplyLoop concrete x rest (i + 1) (z ^^^ concrete.and (concrete.maskBit x (127 - i)) v))
      rw [← ih, c.additive, mask_and, mask_and]
      have z0 : F 0#128 = 0#128 := c.zero
      cases hb : x.getLsbD (127 - i) <;> simp [z0]

/-- `multiply x` commutes with every additive map that commutes with `T`. -/
theorem mul_apply {F : W → W} (c : Commuting F) (x y : W) :
    multiply concrete x (F y) = F (multiply concrete x y) := by
  show multiplyLoop concrete x (powers concrete 128 (F y)) 0 0 =
    F (multiplyLoop concrete x (powers concrete 128 y) 0 0)
  rw [powers_commuting c, ← loop_commuting c, c.zero]

theorem nextCommuting : Commuting (nextPower concrete) :=
  ⟨nextPower_additive, fun _ => rfl⟩

theorem mulCommuting (x : W) : Commuting (multiply concrete x) :=
  ⟨fun a b => multiply_key_additive x a b, fun v => mul_apply nextCommuting x v⟩

theorem mul_left_comm (x y z : W) :
    multiply concrete z (multiply concrete x y) = multiply concrete x (multiply concrete z y) :=
  mul_apply (mulCommuting x) z y

/-! ### The unit -/

/-- The field's 1: the polynomial 1 is the most significant bit in GCM's order. -/
def one : W := BitVec.twoPow 128 127

/-- Below the top position, multiplication by x is a plain shift. -/
theorem next_twoPow (k : Nat) (h : k + 1 < 128) :
    nextPower concrete (BitVec.twoPow 128 (k + 1)) = BitVec.twoPow 128 k := by
  show (BitVec.twoPow 128 (k + 1)).extractLsb' 1 128 ^^^
      concrete.and (concrete.maskBit (BitVec.twoPow 128 (k + 1)) 0) (BitVec.ofNat 128 reduction) = _
  have low : (BitVec.twoPow 128 (k + 1)).getLsbD 0 = false := by simp
  rw [mask_and, low]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : decide (k + 1 = 1 + i) = decide (k = i) := by
    rw [decide_eq_decide]
    omega
  have h2 : k < 128 := by omega
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_twoPow, h1]
  simp [hi, h, h2]

theorem loop_one (x : W) : ∀ (n i : Nat) (z : W), i + n = 128 →
    (∀ j, z.getLsbD j = (x.getLsbD j && decide (128 - i ≤ j))) →
    multiplyLoop concrete x (powers concrete n (BitVec.twoPow 128 (127 - i))) i z = x
  | 0, i, z, hn, hz => by
      show z = x
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [hz j]
      have : 128 - i ≤ j := by omega
      simp [this]
  | n + 1, i, z, hn, hz => by
      have table : powers concrete n (nextPower concrete (BitVec.twoPow 128 (127 - i))) =
          powers concrete n (BitVec.twoPow 128 (127 - (i + 1))) := by
        cases n with
        | zero => rfl
        | succ m =>
            have e : 127 - i = (127 - (i + 1)) + 1 := by omega
            rw [e, next_twoPow _ (by omega)]
      show multiplyLoop concrete x (powers concrete n (nextPower concrete (BitVec.twoPow 128 (127 - i)))) (i + 1)
          (z ^^^ concrete.and (concrete.maskBit x (127 - i)) (BitVec.twoPow 128 (127 - i))) = x
      rw [table]
      apply loop_one x n (i + 1) _ (by omega)
      intro j
      rw [mask_and, BitVec.getLsbD_xor, hz j]
      by_cases hj : j = 127 - i
      · subst hj
        have h1 : ¬ (128 - i ≤ 127 - i) := by omega
        have h2 : 128 - (i + 1) ≤ 127 - i := by omega
        cases hb : x.getLsbD (127 - i) <;> simp [BitVec.getLsbD_twoPow, h1, h2]
        omega
      · have h3 : decide (128 - (i + 1) ≤ j) = decide (128 - i ≤ j) := by
          rw [decide_eq_decide]
          omega
        have h4 : ¬ (127 - i = j) := fun h => hj h.symm
        rw [h3]
        cases hb : x.getLsbD (127 - i) <;> simp [BitVec.getLsbD_twoPow, h4]

/-- `one` is a right unit. -/
theorem mul_one (x : W) : multiply concrete x one = x :=
  loop_one x 128 0 0 rfl (by
    intro j
    simp
    intro h
    exact BitVec.lt_of_getLsbD h)

/-! ### The laws -/

theorem mul_comm (x y : W) : multiply concrete x y = multiply concrete y x := by
  have h := mul_left_comm y one x
  rw [mul_one, mul_one] at h
  exact h

theorem one_mul (x : W) : multiply concrete one x = x := by
  rw [mul_comm, mul_one]

theorem mul_assoc (x y z : W) :
    multiply concrete (multiply concrete x y) z = multiply concrete x (multiply concrete y z) := by
  rw [mul_comm (multiply concrete x y) z, mul_left_comm, mul_comm z y]

/-- Hypothesis (1) of `HybridKernel.shared_halves_are_ghash`, discharged. -/
theorem laws : Laws (multiply concrete) := ⟨mul_comm, mul_assoc⟩

/-- Multiplication is additive in both arguments. -/
theorem mul_left_additive (a b c : W) :
    multiply concrete (a ^^^ b) c = multiply concrete a c ^^^ multiply concrete b c :=
  left_additive _ laws multiply_key_additive a b c

/-- Each party may square its own share. -/
theorem square_shares (a b : W) :
    multiply concrete (a ^^^ b) (a ^^^ b) = multiply concrete a a ^^^ multiply concrete b b :=
  square_additive _ laws multiply_key_additive a b

#print axioms laws
#print axioms mul_one
#print axioms mul_left_comm
#print axioms square_shares

end TlsMpc.GhashField
