import ChatResponseReferenceWork.StreamingV1.MessageInvalidIteration
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

theorem actual_response_step_error (source next : InnerResponseV1.Message) (before after : Slice U8)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (limit : Usize)
    (error : ActualSubmessageV1.prost.error.DecodeError)
    (more : limit.val < before.length)
    (called : SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Err error,(),next,after)) :
    SubmessageV1.body ctx limit (source,before,()) = .ok (.done (.Err error,next,after)) := by
  unfold SubmessageV1.body ActualSubmessageV1.prost.encoding.merge_loop_loop.body
  rw [show ActualSubmessageV1.Mut0T.Insts.BytesBufBuf_implBuf.remaining SubmessageV1.sliceBuf before = .ok before.len from rfl]
  simp only [bind_tc_ok]
  have moreScalar : before.len > limit := by scalar_tac
  rw [if_pos moreScalar]
  rw [show ActualSubmessageV1.prost.encoding.DecodeContext.Insts.CoreCloneClone.clone ctx = .ok ctx from InnerScanV1.clone_ctx ctx]
  simp only [bind_tc_ok]
  have restored : FnMutBorrowV1.toTrait
      ((ActualSubmessageV1.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut
        SubmessageV1.schema SubmessageV1.sliceBuf).raw () (source,before,ctx)) = .ok (.Err error,(),next,after) := called
  rw [restored]
  rfl

theorem actual_message_invalid_loop_step (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle afterLength : Slice U8)
    (native : U64) (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (limit : Usize)
    (limitExact : limit.val = before.length-remaining)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (physical : native.val ≤ afterLength.length)
    (fits : before.length-remaining ≤ (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val).length)
    (accepted : Utf8.accepts ((copiedString afterLength native).val.map (fun byte => byte.bv)) = false)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok ((3#u32),.LengthDelimited),middle))
    (lengthRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,afterLength)) :
    ∃ error,
      SubmessageV1.body ctx limit (source,before,()) =
        .ok (.done (.Err error,{source with message := some (alloc.vec.Vec.new U8)},LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val)) ∧
      error.inner.description = invalidMessageError.inner.description ∧ error.inner.stack.val = [diagnosticFrame2] ∧
      (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨error,called,errorKind,errorStack,rejected⟩ := actual_message_invalid_iteration outer source state before middle afterLength native ctx budget remaining
    boundary cache positive physical fits accepted keyRun lengthRun
  exact ⟨error,actual_response_step_error source _ before _ ctx limit error (by rw [limitExact]; have := boundary.physical; omega) called,
    errorKind,errorStack,rejected⟩

#print axioms actual_response_step_error
#print axioms actual_message_invalid_loop_step
end ChatResponseReference.StreamingV1
