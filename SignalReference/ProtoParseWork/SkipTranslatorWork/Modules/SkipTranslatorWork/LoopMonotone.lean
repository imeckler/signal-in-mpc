import Aeneas

/-! Additional kernel theorem only: the pinned loop implementation is unchanged. -/
namespace Aeneas.Std
open Lean.Order

theorem loop_body_order {α : Type u} {β : Type v}
    (f g : α → Result (ControlFlow α β)) (hfg : f ⊑ g) : loop f ⊑ loop g := by
  apply loop.fixpoint_induct f (fun rec => ∀ x, rec x ⊑ loop g x)
  · exact admissible_pi_apply (fun x value => value ⊑ loop g x)
      (fun _ => admissible_flatOrder _ FlatOrder.rel.bot)
  · intro rec ih x
    dsimp only
    rw [loop.eq_1 g x]
    have flat : ∀ {a b : Result (ControlFlow α β)}, a ⊑ b → a = .div ∨ a = b := by
      intro a b h
      cases h with
      | bot => exact Or.inl rfl
      | refl => exact Or.inr rfl
    rcases flat (hfg x) with h | h
    · rw [h]
      exact FlatOrder.rel.bot
    · rw [h]
      cases hg : g x with
      | div => exact FlatOrder.rel.refl
      | fail e => exact FlatOrder.rel.refl
      | ok step =>
        cases step with
        | cont next => exact ih next
        | done value => exact FlatOrder.rel.refl

@[partial_fixpoint_monotone]
theorem monotone_loop_body {α : Type u} {β : Type v}
    {γ : Sort w} [PartialOrder γ]
    (f : γ → α → Result (ControlFlow α β)) (x : α)
    (hf : monotone f) : monotone (fun p => loop (f p) x) := by
  intro p q hpq
  exact loop_body_order (f p) (f q) (hf p q hpq) x
end Aeneas.Std
