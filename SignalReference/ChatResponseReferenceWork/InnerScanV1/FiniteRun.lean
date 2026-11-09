import ChatResponseReferenceWork.InnerScanV1.DriverReference
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerScanV1
/-- Finite execution evidence retains outer failures and divergence. A `div`
leaf records the actual step's explicit divergence; it is not ordinary Err. -/
inductive FiniteRun {S R : Type} (body : S → Result (ControlFlow S R)) :
    S → Result R → Prop where
  | done {state result} (step : body state = .ok (.done result)) :
      FiniteRun body state (.ok result)
  | fail {state error} (step : body state = .fail error) :
      FiniteRun body state (.fail error)
  | div {state} (step : body state = .div) : FiniteRun body state .div
  | next {state after result} (step : body state = .ok (.cont after))
      (rest : FiniteRun body after result) : FiniteRun body state result

theorem finite_run_actual {S R : Type} {body : S → Result (ControlFlow S R)}
    {state result} (run : FiniteRun body state result) :
    loop body state = result := by
  induction run with
  | done step => rw [loop.eq_1,step]
  | fail step => rw [loop.eq_1,step]
  | div step => rw [loop.eq_1,step]
  | next step rest ih => rw [loop.eq_1,step]; exact ih

/-- Successful continuation strictly decreases a natural measure. This proves
finite execution without a step-termination premise: `Result.fail/div` remain
terminal observed outcomes. The parser instantiation must separately prove the
continuation decrease from actual key and field consumption. -/
theorem finite_run_exists {S R : Type} (body : S → Result (ControlFlow S R))
    (measure : S → Nat)
    (decreases : ∀ before after, body before = .ok (.cont after) →
      measure after < measure before) (state : S) :
    ∃ result, FiniteRun body state result := by
  have bounded : ∀ n, ∀ state, measure state = n → ∃ result, FiniteRun body state result := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro state size
      cases step : body state with
      | fail error => exact ⟨_,.fail step⟩
      | div => exact ⟨_,.div step⟩
      | ok flow =>
        cases flow with
        | done result => exact ⟨_,.done step⟩
        | cont after =>
          obtain ⟨result,rest⟩ := ih (measure after) (size ▸ decreases state after step) after rfl
          exact ⟨result,.next step rest⟩
  exact bounded (measure state) state rfl
#print axioms finite_run_actual
#print axioms finite_run_exists
end ChatResponseReference.InnerScanV1
