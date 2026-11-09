import ChatResponseReferenceWork.StreamingV1.MessageSuccessNative
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- Actual successful Prost response callback exposes its actual generated key
and field calls, rather than assuming those native outcomes for scan induction. -/
theorem actual_callback_success_calls (source next : InnerResponseV1.Message) (before after : Slice U8)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext)
    (observed : SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Ok (),(),next,after)) :
    ∃ tag wire middle,
      ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,wire),middle) ∧
      ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag wire middle ctx = .ok (.Ok (),next,after) := by
  change (do
    let (result,value,suffix,closure) ← ActualSubmessageV1.Raw.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut
      SubmessageV1.schema SubmessageV1.sliceBuf () (source,before,ctx)
    .ok (result,closure,value,suffix)) = _ at observed
  unfold ActualSubmessageV1.Raw.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut at observed
  dsimp! only at observed
  obtain ⟨key,middle,_,actualKey,_,_⟩ := InnerScanV1.key_total before
  rw [SubmessageV1.key_exact,actualKey] at observed
  cases key with
  | Err error =>
    simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at observed
    cases observed
  | Ok pair =>
    rcases pair with ⟨tag,wire⟩
    simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at observed
    dsimp! only at observed
    simp only [bind_tc_ok] at observed
    change (do let (r,value,suffix,closure) ←
                 (do let (r,value,suffix) ← ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag (ActualResponseBytesV1.fromSkipWire wire) middle ctx
                     .ok (r,value,suffix,()))
               .ok (r,closure,value,suffix)) = _ at observed
    cases fieldRun : ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag (ActualResponseBytesV1.fromSkipWire wire) middle ctx with
    | fail error => rw [fieldRun] at observed; cases observed
    | div => rw [fieldRun] at observed; cases observed
    | ok output =>
      rcases output with ⟨status,value,suffix⟩
      rw [fieldRun] at observed
      cases status with
      | Err error => cases observed
      | Ok unit =>
        have same := Result.ok.inj observed
        have valueEq : value = next := congrArg (fun x => x.2.2.1) same
        have cursorEq : suffix = after := congrArg (fun x => x.2.2.2) same
        refine ⟨tag,ActualResponseBytesV1.fromSkipWire wire,middle,actualKey,?_⟩
        rw [←valueEq,←cursorEq]
        exact fieldRun

#print axioms actual_callback_success_calls
end ChatResponseReference.StreamingV1
