import ChatResponseReferenceWork.StreamingV1.MessageErrorLoop
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- A diagnostic stamp cannot turn an ordinary error, allocation failure or
divergence into Ok. Exact output value/cursor remain in the inverse relation. -/
theorem stamped_field_success {T B : Type} (frame : InnerResponseV1.Frame)
    (status : core.result.Result Unit InnerResponseV1.Error) (value next : T) (before after : B)
    (observed : (do let result ← InnerResponseV1.stamp frame status; .ok (result,value,before)) = .ok (.Ok (),next,after)) :
    status = .Ok () ∧ value = next ∧ before = after := by
  cases status with
  | Ok unit =>
    have same := Result.ok.inj observed
    exact ⟨rfl,congrArg (fun x => x.2.1) same,congrArg (fun x => x.2.2) same⟩
  | Err error =>
    unfold InnerResponseV1.stamp at observed
    cases pushed : SchemaV1.Diagnostic.push error frame with
    | fail error => simp only [pushed,bind_tc_fail] at observed; cases observed
    | div => simp only [pushed,bind_tc_div] at observed; cases observed
    | ok nextError => simp only [pushed,bind_tc_ok] at observed; cases observed

#print axioms stamped_field_success
end ChatResponseReference.StreamingV1
