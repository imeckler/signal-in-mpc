import TlsMpcProofs.QuadraticResidue
import TlsMpc.GhashShares
import TlsMpc.MaskedAgreement
import TlsMpc.WordMask

/-!
# Hiding as probability (REORGANIZATION_PLAN.md section 7.0, Security.lean section 8)

Each bijection-form hiding statement becomes a distributional one through `Uniform.lean`'s
`hiding_of_bijection` / `uniform_of_bijective`: with the honest party's mask uniform, what the
other party sees has the same distribution (`PMF.map view (uniformOfFintype _)`) whatever the
secret, and usually is exactly uniform.

Worked example: `ghash_share_hides_dist`, derived from the main package's own bijection
`GhashShares.share_views_equal` (the bijection behind `ghash_share_hides`). The others are short
applications of the same lemma.
-/

namespace TlsMpcProofs
open TlsMpc PMF

/-- `BitVec n` is finite: it is `Fin (2^n)`. -/
instance bitVecFintype (n : ℕ) : Fintype (BitVec n) :=
  Fintype.ofEquiv (Fin (2 ^ n))
    { toFun := BitVec.ofFin, invFun := BitVec.toFin, left_inv := fun _ => rfl, right_inv := fun _ => rfl }

/-- XOR with a fixed word, as a bijection. -/
def xorEquiv {n : ℕ} (d : BitVec n) : BitVec n ≃ BitVec n where
  toFun m := m ^^^ d
  invFun m := m ^^^ d
  left_inv m := by simp [BitVec.xor_assoc]
  right_inv m := by simp [BitVec.xor_assoc]

/-! ### P-GHASH(d): a key-power share hides the power (`ghash_share_hides`) -/

/-- **The masked key power B sees has the same distribution for any two key powers** when A's
mask is uniform. From the main package's `GhashShares.share_views_equal` (the bijection
`mask ↦ mask ⊕ key ⊕ other`). -/
theorem ghash_share_hides_dist (key other : GhashShares.W) :
    PMF.map (fun mask => key ^^^ mask) (uniformOfFintype GhashShares.W) =
      PMF.map (fun mask => other ^^^ mask) (uniformOfFintype GhashShares.W) :=
  hiding_of_bijection (fun k mask => k ^^^ mask) key other (xorEquiv (key ^^^ other))
    (GhashShares.share_views_equal key other)

/-- **It is in fact uniform** on 128-bit words, whatever the key power. -/
theorem ghash_share_uniform (key : GhashShares.W) :
    PMF.map (fun mask => key ^^^ mask) (uniformOfFintype GhashShares.W) = uniformOfFintype GhashShares.W := by
  have h : (fun mask : GhashShares.W => key ^^^ mask) = xorEquiv key := by
    funext mask; simp [xorEquiv, BitVec.xor_comm]
  rw [h, map_uniform_equiv]

/-! ### Ceremony masking (`ceremony_masked_hides`, same expression) -/

/-- **The ceremony's masked byte `word ⊕ (other ⊕ m)` is uniform for a uniform mask `m`**,
whatever `word` and `other`. Same expression as `Security.ceremony_masked_hides`; not linked by
import, because `TlsMpc.CeremonyProofs` pulls in the receive kernels' proofs (see README). -/
theorem ceremony_masked_uniform (word other : BitVec 8) :
    PMF.map (fun m => word ^^^ (other ^^^ m)) (uniformOfFintype (BitVec 8)) = uniformOfFintype (BitVec 8) := by
  have h : (fun m : BitVec 8 => word ^^^ (other ^^^ m)) = xorEquiv (word ^^^ other) := by
    funext m
    show word ^^^ (other ^^^ m) = m ^^^ (word ^^^ other)
    rw [← BitVec.xor_assoc, BitVec.xor_comm]
  rw [h, map_uniform_equiv]

/-! ### P-RAND(b), P-PAIR/P-B2F(b): XOR with the honest party's uniform value -/

/-- **P-RAND(b) distributional:** `r ⊕ v` is uniform for a uniform `r`, whatever `v` the other
party chose (under `idealCommit`, `v` cannot depend on `r`). -/
theorem joint_random_uniform {n : ℕ} (v : BitVec n) :
    PMF.map (fun r => r ^^^ v) (uniformOfFintype (BitVec n)) = uniformOfFintype (BitVec n) :=
  map_uniform_equiv (xorEquiv v)

/-- **P-B2F(b) distributional:** the opened bit `o = x ⊕ ρ` is uniform for a uniform `ρ`,
whatever `x`. -/
theorem bit_open_uniform (x : Bool) :
    PMF.map (fun ρ => x ^^ ρ) (uniformOfFintype Bool) = uniformOfFintype Bool :=
  uniform_of_bijective _ ⟨fun a b h => by simpa using h, fun o => ⟨x ^^ o, by simp⟩⟩

/-! ### P-W2F(b), P-F2W(b), P-INV(c): field masks -/

theorem wordMask_P_eq : WordMask.P = FieldDag.modulus := by decide

/-- **P-W2F(b) distributional:** the opened `c = (u mod p + r) mod p` (the `into-field`
circuit's output, `wordMask_intoField_val`) is uniform on `[0, p)` for a uniform mask
`r ∈ [0, p)`, whatever the word `u`. -/
theorem word_to_field_open_uniform (u : ℕ) :
    PMF.map (fun r : FieldDag.F => (u % WordMask.P + r.val) % WordMask.P) (uniformOfFintype FieldDag.F) =
      PMF.map (fun r : FieldDag.F => r.val) (uniformOfFintype FieldDag.F) := by
  have h : (fun r : FieldDag.F => (u % WordMask.P + r.val) % WordMask.P) =
      (fun r : FieldDag.F => r.val) ∘ (Equiv.addLeft (FieldDag.ofNat u)) := by
    funext r
    simp only [Function.comp_apply, Equiv.coe_addLeft, Fin.val_add, wordMask_P_eq]
    rfl
  rw [h, ← PMF.map_comp, map_uniform_equiv]

/-- **P-F2W(b) distributional:** the opened `c = v − f` is uniform for a uniform field mask `f`,
whatever `v`. -/
theorem field_to_word_open_uniform (v : FieldDag.F) :
    PMF.map (fun f : FieldDag.F => v - f) (uniformOfFintype FieldDag.F) = uniformOfFintype FieldDag.F :=
  map_uniform_equiv (Equiv.subLeft v)

/-- **P-INV(c) distributional:** for `b ≠ 0`, the opened `o = b·m` is uniform for a uniform
mask `m` (so a nonzero denominator reveals nothing). -/
theorem masked_inverse_open_uniform (b : FieldDag.F) (hb : b ≠ FieldDag.ofNat 0) :
    PMF.map (fun m : FieldDag.F => b * m) (uniformOfFintype FieldDag.F) = uniformOfFintype FieldDag.F := by
  apply uniform_of_bijective
  apply Finite.injective_iff_bijective.mp
  intro m m' h
  have h' := congrArg toZMod h
  rw [toZMod_mul, toZMod_mul] at h'
  exact toZMod_injective (mul_left_cancel₀ (toZMod_ne_zero hb) h')

/-! ### Masked points (`maskedAgreement_mask_hides`; P-HINT(c) under H-GROUP) -/

/-- **The opened masked point `R + maskA + maskB` has the same distribution for any two `R`**
when the honest party's `maskB` is uniform on a finite commutative group. From the main
package's `MaskedAgreement.mask_hides`. For the curve this needs H-GROUP (the formulas form a
group), which stays a hypothesis: `G` is any finite commutative group here. -/
theorem maskedAgreement_mask_hides_dist {G : Type} [AddCommGroup G] [Fintype G] [Nonempty G]
    (R other maskA : G) :
    PMF.map (fun maskB => MaskedAgreement.opened R maskA maskB) (uniformOfFintype G) =
      PMF.map (fun maskB => MaskedAgreement.opened other maskA maskB) (uniformOfFintype G) :=
  hiding_of_bijection (fun P maskB => MaskedAgreement.opened P maskA maskB) R other
    (Equiv.addRight (R - other)) (fun maskB => by
      rw [MaskedAgreement.mask_hides R other maskA maskB]
      simp only [Equiv.coe_addRight, MaskedAgreement.opened]
      abel)

/-- **P-HINT(c) distributional (H-GROUP as the hypothesis "a finite commutative group"):** the
opened `Z = P + M_A + M_B` is uniform when the honest party's `M_B` is uniform, whatever `P` and
`M_A`. -/
theorem hinted_Z_uniform {G : Type} [AddCommGroup G] [Fintype G] [Nonempty G] (P maskA : G) :
    PMF.map (fun maskB => MaskedAgreement.opened P maskA maskB) (uniformOfFintype G) = uniformOfFintype G := by
  have h : (fun maskB => MaskedAgreement.opened P maskA maskB) = Equiv.addLeft (P + maskA) := by
    funext maskB; rfl
  rw [h, map_uniform_equiv]

end TlsMpcProofs
