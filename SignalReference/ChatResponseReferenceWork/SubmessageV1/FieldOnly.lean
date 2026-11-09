import ChatResponseReferenceWork.SubmessageV1.Replayed.Funs
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.SubmessageV1
open ActualSubmessageV1

theorem raw_field_only {M B : Type} (first second : prost.message.Message M)
    (bi : bytes.buf.buf_impl.Buf B) (fields : @first.merge_field = @second.merge_field) :
    Raw.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut first bi =
      Raw.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut second bi := by
  unfold Raw.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut
  rw [fields]

theorem operation_field_only {M B : Type} (first second : prost.message.Message M)
    (bi : bytes.buf.buf_impl.Buf B) (fields : @first.merge_field = @second.merge_field) :
    prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut first bi =
      prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut second bi := by
  unfold prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut
  rw [raw_field_only first second bi fields]

theorem callback_field_only {M B : Type} (first second : prost.message.Message M)
    (bi : bytes.buf.buf_impl.Buf B) (fields : @first.merge_field = @second.merge_field) :
    prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError first bi =
      prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError second bi := by
  have once : prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnOnceTupleMutMMutBDecodeContextResultTupleDecodeError.call_once first bi =
      prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnOnceTupleMutMMutBDecodeContextResultTupleDecodeError.call_once second bi := by
    unfold prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnOnceTupleMutMMutBDecodeContextResultTupleDecodeError.call_once
    rw [operation_field_only first second bi fields]
  unfold prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError
    prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnOnceTupleMutMMutBDecodeContextResultTupleDecodeError
  rw [once,operation_field_only first second bi fields]

/-- The actual submessage computation depends only on merge_field. Unused
encoding/clear dictionary slots cannot introduce effects into this parse. -/
theorem merge_field_only {M B : Type} (first second : prost.message.Message M)
    (bi : bytes.buf.buf_impl.Buf B) (fields : @first.merge_field = @second.merge_field)
    (wire : prost.encoding.wire_type.WireType) (state : M) (before : B) (ctx : prost.encoding.DecodeContext) :
    prost.encoding.message.merge first bi wire state before ctx =
      prost.encoding.message.merge second bi wire state before ctx := by
  unfold prost.encoding.message.merge
  rw [callback_field_only first second bi fields]
#print axioms raw_field_only
#print axioms merge_field_only
end ChatResponseReference.SubmessageV1
