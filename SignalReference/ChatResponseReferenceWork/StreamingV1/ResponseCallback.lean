import ChatResponseReferenceWork.StreamingV1.KnownKeyCacheReady
import ChatResponseReferenceWork.SubmessageV1.InnerScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- Actual parent-buffer submessage callback composes the actual generated key
and field calls with exact borrow restoration, ordinary status, message/suffix. -/
theorem actual_response_callback (source next : InnerResponseV1.Message) (before middle after : Slice U8)
    (tag : U32) (wire : ActualInnerScanV1.prost.encoding.wire_type.WireType)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext)
    (status : core.result.Result Unit ActualInnerResponseV1.prost.error.DecodeError)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,wire),middle))
    (fieldRun : ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag wire middle ctx = .ok (status,next,after)) :
    SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (status,(),next,after) := by
  change (do
    let (result,value,suffix,closure) ← ActualSubmessageV1.Raw.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut
      SubmessageV1.schema SubmessageV1.sliceBuf () (source,before,ctx)
    .ok (result,closure,value,suffix)) = _
  unfold ActualSubmessageV1.Raw.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut
  dsimp! only
  rw [SubmessageV1.key_exact,keyRun]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  simp only [bind_tc_ok]
  change (do let (r,value,suffix,closure) ←
               (do let (r,value,suffix) ← ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag wire middle ctx
                   .ok (r,value,suffix,()))
             .ok (r,closure,value,suffix)) = _
  rw [fieldRun]
  rfl

#print axioms actual_response_callback
end ChatResponseReference.StreamingV1
