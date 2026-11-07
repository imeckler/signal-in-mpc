import ProstEncodingWork.AdvanceWork.TranslatorCandidate.NeverContinuation
import ProstEncodingWork.AdvanceWork.TranslatorCandidate.Generated.Candidate.Regressions.Funs

namespace LibSignalReference.Candidate.NeverRegressionProofs

open Aeneas Aeneas.Std
open NeverContinuation

theorem call_eq {T : Type} (dictionary : NeverRegression.Stops T) (value : T) :
    NeverRegression.call dictionary value = eliminate (dictionary.stop value) := by
  exact unreachable_panic_tail _

theorem guarded_eq {T : Type} (dictionary : NeverRegression.Stops T) (value : T)
    (proceed : Bool) :
    NeverRegression.guarded dictionary value proceed =
      if proceed then .ok 7#u8 else eliminate (dictionary.stop value) := by
  cases proceed
  · exact unreachable_panic_tail _
  · rfl

theorem call_failure {T : Type} (dictionary : NeverRegression.Stops T) (value : T)
    (error : Error) (h : dictionary.stop value = .fail error) :
    NeverRegression.call dictionary value = .fail error := by
  rw [call_eq, h, eliminate_failure]

theorem call_divergence {T : Type} (dictionary : NeverRegression.Stops T) (value : T)
    (h : dictionary.stop value = .div) :
    NeverRegression.call dictionary value = .div := by
  rw [call_eq, h, eliminate_divergence]

theorem guarded_success {T : Type} (dictionary : NeverRegression.Stops T) (value : T) :
    NeverRegression.guarded dictionary value true = .ok 7#u8 := rfl

theorem guarded_failure {T : Type} (dictionary : NeverRegression.Stops T) (value : T)
    (error : Error) (h : dictionary.stop value = .fail error) :
    NeverRegression.guarded dictionary value false = .fail error := by
  rw [guarded_eq, h]
  rfl

theorem guarded_divergence {T : Type} (dictionary : NeverRegression.Stops T) (value : T)
    (h : dictionary.stop value = .div) :
    NeverRegression.guarded dictionary value false = .div := by
  rw [guarded_eq, h]
  rfl

theorem actual_panic_call : NeverRegression.panic_caller = .fail .panic := rfl

end LibSignalReference.Candidate.NeverRegressionProofs
