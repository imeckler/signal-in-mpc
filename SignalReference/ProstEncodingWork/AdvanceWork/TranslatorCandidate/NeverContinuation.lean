import Aeneas

namespace LibSignalReference.Candidate.NeverContinuation

open Aeneas Aeneas.Std

/-- Eliminate only the impossible successful return. Failure and divergence
are the original call's results, not newly chosen outcomes. -/
def eliminate {α : Type} (result : Result Never) : Result α :=
  Aeneas.Std.bind result (fun impossible => nomatch impossible)

theorem bind_eq_eliminate {α : Type} (result : Result Never)
    (continuation : Never → Result α) :
    Aeneas.Std.bind result continuation = eliminate result := by
  cases result with
  | ok impossible => cases impossible
  | fail error => rfl
  | div => rfl

/-- An unreachable panic tail is valid only after retaining the actual call
to an uninhabited result. This does not identify the call with panic. -/
theorem unreachable_panic_tail {α : Type} (result : Result Never) :
    (do let _ ← result; (Result.fail .panic : Result α)) = eliminate result := by
  exact bind_eq_eliminate result _

theorem eliminate_failure {α : Type} (error : Error) :
    eliminate (Result.fail error : Result Never) = (Result.fail error : Result α) := rfl

theorem eliminate_divergence {α : Type} :
    eliminate (Result.div : Result Never) = (Result.div : Result α) := rfl

theorem unreachable_tail_preserves_failure {α : Type} (error : Error) :
    (do let _ ← (Result.fail error : Result Never);
        (Result.fail .panic : Result α)) = Result.fail error := rfl

theorem unreachable_tail_preserves_divergence {α : Type} :
    (do let _ ← (Result.div : Result Never);
        (Result.fail .panic : Result α)) = Result.div := rfl

end LibSignalReference.Candidate.NeverContinuation
