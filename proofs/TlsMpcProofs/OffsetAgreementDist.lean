import TlsMpcProofs.Uniform
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel

/-!
# The offset agreement's public key, as probability

The main package's `OffsetAgreement.public_key_independent` (restated in `TlsMpc/Security.lean`)
is the bijection form: `initial·B + offset·B = other·B + (offset + initial − other)·B` with
integer scalars. Integers carry no uniform distribution, so here the scalars live in `ZMod ℓ`,
`ℓ` the order of the group, acting by `k·B := k.val • B` (well defined because `ℓ·B = 0`).

**H-GROUP stays the hypothesis**: `G` is any finite commutative group (`AddCommGroup G`,
`Fintype G`) of order `ℓ`; nothing here proves that the Edwards formulas form such a group.

* `offset_public_key_independent`: with the offset uniform in `ZMod ℓ`, the published key
  `initial·B + offset·B` has the **same distribution for any two initial scalars** (any finite
  commutative group of order `ℓ`; primality not needed).
* `offset_public_key_uniform`: if moreover `ℓ` is prime and `B ≠ 0`, the published key is
  **uniform on `G`** (so it reveals nothing about `initial`). Keys of several messages:
  `OffsetSampling.offset_public_keys_independent` / `_uniform`.

The deployed offset, drawn from `[0, 2²⁵²)` rather than uniformly modulo `ℓ`, is treated in
`OffsetSampling.lean` (statistical distance `< 2⁻¹²⁷` for the Ed25519 order). Not proved: that the
offsets are independent of everything else (`idealCommit`).
-/

namespace TlsMpcProofs.OffsetAgreement
open PMF

variable {G : Type} [AddCommGroup G] [Fintype G]

/-- Multiplying by `m` and by `m mod |G|` agree (`|G|·B = 0`). -/
theorem nsmul_mod_card (B : G) (m : ℕ) : (m % Fintype.card G) • B = m • B := by
  rw [← mod_addOrderOf_nsmul B (m % Fintype.card G), Nat.mod_mod_of_dvd _ (addOrderOf_dvd_card),
    mod_addOrderOf_nsmul]

variable {ℓ : ℕ} [NeZero ℓ]

/-- Scalars mod `ℓ = |G|` act additively: `(a + b)·B = a·B + b·B`. -/
theorem val_add_nsmul (hℓ : Fintype.card G = ℓ) (B : G) (a b : ZMod ℓ) :
    (a + b).val • B = a.val • B + b.val • B := by
  have h := nsmul_mod_card B (a.val + b.val)
  rw [hℓ] at h
  rw [ZMod.val_add, h, add_nsmul]

/-- The published key for the initial scalar `initial` and the offset `offset`:
`initial·B + offset·B`. -/
def publicKey (B : G) (initial offset : ZMod ℓ) : G := initial.val • B + offset.val • B

/-- **`offsetAgreement_public_key_independent` as probability** (H-GROUP as the hypothesis
"`G` is a finite commutative group of order `ℓ`"): with the offset uniform modulo `ℓ`, the
published key has the same distribution for any two initial scalars. -/
theorem offset_public_key_independent (hℓ : Fintype.card G = ℓ) (B : G) (initial other : ZMod ℓ) :
    PMF.map (publicKey B initial) (uniformOfFintype (ZMod ℓ)) =
      PMF.map (publicKey B other) (uniformOfFintype (ZMod ℓ)) :=
  hiding_of_bijection (fun s offset => publicKey B s offset) initial other
    (Equiv.addRight (initial - other)) (fun offset => by
      simp only [publicKey, Equiv.coe_addRight]
      have h := val_add_nsmul hℓ B (offset + (initial - other)) other
      rw [show offset + (initial - other) + other = offset + initial by ring] at h
      rw [val_add_nsmul hℓ B offset initial] at h
      rw [add_comm (initial.val • B), h]
      abel)

/-- In a group of prime order `ℓ`, `k ↦ k·B` is injective on `ZMod ℓ` for `B ≠ 0`. -/
theorem val_nsmul_injective [Fact ℓ.Prime] (hℓ : Fintype.card G = ℓ) (B : G) (hB : B ≠ 0) :
    Function.Injective (fun k : ZMod ℓ => k.val • B) := by
  have hord : addOrderOf B = ℓ := by
    have hdvd : addOrderOf B ∣ ℓ := by rw [← hℓ]; exact addOrderOf_dvd_card
    rcases (Nat.dvd_prime (Fact.out : ℓ.Prime)).mp hdvd with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hB
    · exact h
  intro a b hab
  simp only at hab
  have h := val_add_nsmul hℓ B (a - b) b
  rw [sub_add_cancel, ← hab] at h
  have h0 : (a - b).val • B = 0 := by
    have := congrArg (· - b.val • B) h
    simpa using this.symm
  have hdvd : addOrderOf B ∣ (a - b).val := addOrderOf_dvd_of_nsmul_eq_zero h0
  rw [hord] at hdvd
  have hlt : (a - b).val < ℓ := ZMod.val_lt (a - b)
  have hz : (a - b).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
  rw [ZMod.val_eq_zero, sub_eq_zero] at hz
  exact hz

/-- **The published key is uniform on `G`** when `|G| = ℓ` is prime and `B ≠ 0` (any initial
scalar), the offset uniform modulo `ℓ`. -/
theorem offset_public_key_uniform [Fact ℓ.Prime] (hℓ : Fintype.card G = ℓ) (B : G) (hB : B ≠ 0)
    (initial : ZMod ℓ) :
    PMF.map (publicKey B initial) (uniformOfFintype (ZMod ℓ)) = uniformOfFintype G := by
  haveI : Nonempty G := ⟨0⟩
  apply uniform_of_bijective
  have hinj : Function.Injective (publicKey B initial) := by
    intro a b hab
    simp only [publicKey] at hab
    exact val_nsmul_injective hℓ B hB (add_left_cancel hab)
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨hinj, by rw [ZMod.card, hℓ]⟩

end TlsMpcProofs.OffsetAgreement
