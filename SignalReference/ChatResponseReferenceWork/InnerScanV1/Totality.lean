import ChatResponseReferenceWork.InnerScanV1.StepReference
import ChatResponseReferenceWork.InnerScanV1.FieldConsumption
import ChatResponseReferenceWork.InnerScanV1.FiniteRun
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerScanV1
open ActualInnerScanV1

theorem step_decreases (ctx : prost.encoding.DecodeContext) (state next : Message)
    (before after : Slice U8)
    (continued : stepSpec ctx state before = .ok (.cont (next,after))) :
    after.length < before.length := by
  by_cases nonempty : 0 < before.length
  · obtain ⟨key,middle,keyRun,actualKey,bound,strict⟩ := key_total before
    cases key with
    | Err error => simp [stepSpec,nonempty,actualKey] at continued
    | Ok pair =>
      rcases pair with ⟨tag,wire⟩
      have keyStrict := strict (tag,wire) rfl
      simp only [stepSpec,if_pos nonempty,actualKey,bind_tc_ok] at continued
      dsimp! only at continued
      cases fieldRun : InnerResponseV1.fieldSpec (fieldBuf sliceBuf) state tag
          (ActualResponseBytesV1.fromSkipWire wire) middle ctx with
      | fail error => simp [fieldRun] at continued
      | div => simp [fieldRun] at continued
      | ok output =>
        rcases output with ⟨status,value,suffix⟩
        have fieldBound := field_consumption state value tag
          (ActualResponseBytesV1.fromSkipWire wire) middle suffix ctx status fieldRun
        cases status with
        | Err error => simp [fieldRun] at continued
        | Ok unit =>
          simp [fieldRun] at continued
          rcases continued with ⟨rfl,rfl⟩
          exact fieldBound.trans_lt keyStrict
  · simp [stepSpec,nonempty] at continued

/-- Actual complete inner-response scan has a finite execution on every valid
contiguous slice. The outcome retains ordinary Err, allocation/model fail and
explicit divergence. No primitive correctness, termination or finite trace
premise is supplied. This theorem does not yet relate the scan to TLS streaming. -/
theorem actual_scan_finite (ctx : prost.encoding.DecodeContext) (state : Message) (before : Slice U8) :
    ∃ result,
      FiniteRun (fun pair : Message × Slice U8 => stepSpec ctx pair.1 pair.2) (state,before) result ∧
      prost.message.Message.merge.default_loop schema sliceBuf state before ctx = result := by
  obtain ⟨result,run⟩ := finite_run_exists
    (fun pair : Message × Slice U8 => stepSpec ctx pair.1 pair.2)
    (fun pair => pair.2.length)
    (by intro old next step; exact step_decreases ctx old.1 next.1 old.2 next.2 step)
    (state,before)
  refine ⟨result,run,?_⟩
  unfold prost.message.Message.merge.default_loop
  have bodies : (fun pair : Message × Slice U8 =>
      prost.message.Message.merge.default_loop.body schema sliceBuf ctx pair.1 pair.2) =
      (fun pair : Message × Slice U8 => stepSpec ctx pair.1 pair.2) := by
    funext pair
    exact step_reference ctx pair.1 pair.2
  rw [bodies]
  exact finite_run_actual run
#print axioms step_decreases
#print axioms actual_scan_finite
end ChatResponseReference.InnerScanV1
