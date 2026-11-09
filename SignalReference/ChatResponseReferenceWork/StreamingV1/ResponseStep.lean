import ChatResponseReferenceWork.StreamingV1.ScalarIteration
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- Actual Prost parent-limit loop advances after its actual callback succeeds.
This preserves the real buffer, message and closure restoration ABI. -/
theorem actual_response_step_next (source next : InnerResponseV1.Message) (before after : Slice U8)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (limit : Usize)
    (more : limit.val < before.length)
    (called : SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Ok (),(),next,after)) :
    SubmessageV1.body ctx limit (source,before,()) = .ok (.cont (next,after,())) := by
  unfold SubmessageV1.body ActualSubmessageV1.prost.encoding.merge_loop_loop.body
  rw [show ActualSubmessageV1.Mut0T.Insts.BytesBufBuf_implBuf.remaining SubmessageV1.sliceBuf before = .ok before.len from rfl]
  simp only [bind_tc_ok]
  have moreScalar : before.len > limit := by scalar_tac
  rw [if_pos moreScalar]
  rw [show ActualSubmessageV1.prost.encoding.DecodeContext.Insts.CoreCloneClone.clone ctx = .ok ctx from InnerScanV1.clone_ctx ctx]
  simp only [bind_tc_ok]
  have restored : FnMutBorrowV1.toTrait
      ((ActualSubmessageV1.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut
        SubmessageV1.schema SubmessageV1.sliceBuf).raw () (source,before,ctx)) = .ok (.Ok (),(),next,after) := called
  rw [restored]
  rfl

#print axioms actual_response_step_next
end ChatResponseReference.StreamingV1
