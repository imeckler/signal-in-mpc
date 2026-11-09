import ChatResponseReferenceWork.InnerScanV1.DriverReference
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerScanV1
open ActualInnerScanV1
/-- Operational one-step normal form, retaining every field state/suffix and
outer fail/div before owned observation. -/
noncomputable def stepSpec (ctx : prost.encoding.DecodeContext) (state : Message) (before : Slice U8) :
    Result (ControlFlow (Message × Slice U8)
      (core.result.Result Unit prost.error.DecodeError × Message)) := do
  if 0 < before.length then
    let (key,middle) ← prost.encoding.decode_key sliceBuf before
    match key with
    | .Err error => .ok (.done (.Err error,state))
    | .Ok (tag,wire) =>
      let (status,next,after) ← InnerResponseV1.fieldSpec (fieldBuf sliceBuf) state tag wire middle ctx
      match status with
      | .Err error => .ok (.done (.Err error,next))
      | .Ok _ => .ok (.cont (next,after))
  else .ok (.done (.Ok (),state))

theorem step_reference (ctx : prost.encoding.DecodeContext) (state : Message) (before : Slice U8) :
    prost.message.Message.merge.default_loop.body schema sliceBuf ctx state before =
      stepSpec ctx state before := by
  by_cases nonempty : 0 < before.length
  · unfold prost.message.Message.merge.default_loop.body stepSpec
    rw [show sliceBuf.has_remaining before = .ok true from by simp [sliceBuf,nonempty]]
    simp only [bind_tc_ok,if_true,nonempty]
    cases keyRun : prost.encoding.decode_key sliceBuf before with
    | fail error => simp only [keyRun,bind_tc_fail]
    | div => simp only [keyRun,bind_tc_div]
    | ok pair =>
      rcases pair with ⟨key,middle⟩
      simp only [keyRun,bind_tc_ok]
      cases key with
      | Err error => rfl
      | Ok pair =>
        rcases pair with ⟨tag,wire⟩
        dsimp! only
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,clone_ctx,actual_fields]
        cases fieldRun : InnerResponseV1.fieldSpec (fieldBuf sliceBuf) state tag wire middle ctx with
        | fail error => rfl
        | div => rfl
        | ok pair => rcases pair with ⟨status,next,after⟩; cases status <;> rfl
  · simp [prost.message.Message.merge.default_loop.body,stepSpec,sliceBuf,nonempty]
#print axioms step_reference
end ChatResponseReference.InnerScanV1
