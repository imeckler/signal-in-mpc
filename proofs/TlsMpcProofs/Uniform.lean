import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
# Uniform distributions pushed through functions

The reusable step from the "bijection on the randomness" form of hiding
(REORGANIZATION_PLAN.md section 7.0) to the distributional form: if the honest party's randomness
`ρ` is uniform and, for any two secrets, a bijection on `ρ` carries one view to the other, then the
view has the same distribution (`PMF.map view (uniformOfFintype R)`) for both secrets.
-/

namespace TlsMpcProofs
open PMF

/-- A bijection carries the uniform distribution to the uniform distribution. -/
theorem map_uniform_equiv {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) : PMF.map e (uniformOfFintype α) = uniformOfFintype β := by
  classical
  ext b
  rw [PMF.map_apply, tsum_fintype]
  simp only [uniformOfFintype_apply]
  rw [Equiv.sum_comp e (fun y => if b = y then (Fintype.card α : ENNReal)⁻¹ else 0),
    Finset.sum_ite_eq]
  simp [Fintype.card_congr e]

/-- **Hiding from a bijection on the randomness.** If `view s r = view s' (σ r)` for a bijection
`σ` of the randomness, the view has the same distribution under `s` and `s'` when `r` is uniform. -/
theorem hiding_of_bijection {S R V : Type*} [Fintype R] [Nonempty R] (view : S → R → V)
    (s s' : S) (σ : R ≃ R) (h : ∀ r, view s r = view s' (σ r)) :
    PMF.map (view s) (uniformOfFintype R) = PMF.map (view s') (uniformOfFintype R) := by
  have hv : view s = view s' ∘ σ := funext h
  rw [hv, ← PMF.map_comp, map_uniform_equiv]

/-- The same, quantified: a family of bijections (one per pair of secrets) makes the view's
distribution independent of the secret. -/
theorem hiding_of_bijections {S R V : Type*} [Fintype R] [Nonempty R] (view : S → R → V)
    (h : ∀ s s', ∃ σ : R ≃ R, ∀ r, view s r = view s' (σ r)) (s s' : S) :
    PMF.map (view s) (uniformOfFintype R) = PMF.map (view s') (uniformOfFintype R) := by
  obtain ⟨σ, hσ⟩ := h s s'
  exact hiding_of_bijection view s s' σ hσ

/-- If the view is, for the given secret, a bijection of the randomness onto the view space,
the view is exactly uniform. -/
theorem uniform_of_bijective {R V : Type*} [Fintype R] [Nonempty R] [Fintype V] [Nonempty V]
    (f : R → V) (hf : Function.Bijective f) : PMF.map f (uniformOfFintype R) = uniformOfFintype V :=
  map_uniform_equiv (Equiv.ofBijective f hf)

/-- Pushing the uniform distribution through a function whose every fiber has exactly `k`
points (so `|α| = k·|β|`) gives the uniform distribution. -/
theorem map_uniform_of_fiber_card {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [DecidableEq β] (f : α → β) (k : ℕ)
    (hfib : ∀ b, (Finset.univ.filter (fun a => f a = b)).card = k)
    (hcard : Fintype.card α = k * Fintype.card β) :
    PMF.map f (uniformOfFintype α) = uniformOfFintype β := by
  have hk : k ≠ 0 := by
    intro hk
    rw [hk, zero_mul] at hcard
    exact Fintype.card_ne_zero hcard
  ext b
  rw [PMF.map_apply, tsum_fintype]
  simp only [uniformOfFintype_apply]
  have hterm : ∀ a, (if b = f a then (Fintype.card α : ENNReal)⁻¹ else 0) =
      (if f a = b then 1 else 0) * (Fintype.card α : ENNReal)⁻¹ := by
    intro a
    by_cases h : f a = b
    · simp [h]
    · have h' : ¬ b = f a := fun e => h e.symm
      simp [h, h']
  simp_rw [hterm]
  rw [← Finset.sum_mul, Finset.sum_boole, hfib, hcard, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl (by exact_mod_cast hk)) (Or.inl (ENNReal.natCast_ne_top k)),
    ← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast hk) (ENNReal.natCast_ne_top k), one_mul]

end TlsMpcProofs
