import ChatResponseReferenceWork.SubmessageV1.Replayed.Funs
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.SubmessageV1
open ActualSubmessageV1

theorem actual_closure_projection {M B : Type} (mi : prost.message.Message M)
    (bi : bytes.buf.buf_impl.Buf B) (closure : prost.encoding.message.merge.closure M B)
    (args : M × B × prost.encoding.DecodeContext) :
    FnMutBorrowV1.toRaw
      (((prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut mi bi) :
        prost.encoding.message.merge.closure M B → (M × B × prost.encoding.DecodeContext) →
          Result (core.result.Result Unit prost.error.DecodeError × prost.encoding.message.merge.closure M B × M × B)) closure args) =
      Raw.prost.encoding.message.merge.closure.Insts.CoreOpsFunctionFnMutTupleMutMMutBDecodeContextResultTupleDecodeError.call_mut mi bi closure args :=
  FnMutBorrowV1.field_exact _ _ _

def decodeError (kind : prost.error.DecodeErrorKind) : prost.error.DecodeError :=
  ⟨⟨kind,alloc.vec.Vec.new (Str × Str)⟩⟩
theorem wrong_wire {M B : Type} (mi : prost.message.Message M) (bi : bytes.buf.buf_impl.Buf B)
    (wire : prost.encoding.wire_type.WireType) (value : M) (before : B) (ctx : prost.encoding.DecodeContext)
    (wrong : wire ≠ .LengthDelimited) :
    prost.encoding.message.merge mi bi wire value before ctx =
      .ok (.Err (decodeError (.UnexpectedWireType wire .LengthDelimited)),value,before) := by
  cases wire <;> first | exact False.elim (wrong rfl) | rfl

theorem recursion_zero {M B : Type} (mi : prost.message.Message M) (bi : bytes.buf.buf_impl.Buf B)
    (value : M) (before : B) :
    prost.encoding.message.merge mi bi .LengthDelimited value before ⟨0#u32⟩ =
      .ok (.Err (decodeError .RecursionLimitReached),value,before) := rfl

/-- Exact parent-buffer semantics: passing the child end is detected after the
previous field callback, retaining that callback's message and suffix. -/
theorem delimited_overrun {T F B : Type}
    (callback : FnMutBorrowV1.BorrowFnMut F T B prost.encoding.DecodeContext (core.result.Result Unit prost.error.DecodeError))
    (bi : bytes.buf.buf_impl.Buf B) (ctx : prost.encoding.DecodeContext)
    (limit remaining : Usize) (value : T) (before : B) (closure : F)
    (read : bi.remaining before = .ok remaining) (overrun : remaining < limit) :
    prost.encoding.merge_loop_loop.body callback bi ctx limit value before closure =
      .ok (.done (.Err (decodeError .DelimitedLengthExceeded),value,before)) := by
  have notMore : ¬ remaining > limit := by scalar_tac
  have different : remaining ≠ limit := by scalar_tac
  have notMoreVal : ¬ limit.val < remaining.val := by scalar_tac
  have differentVal : remaining.val ≠ limit.val := by scalar_tac
  simp [prost.encoding.merge_loop_loop.body,Mut0T.Insts.BytesBufBuf_implBuf.remaining,read,notMore,different,notMoreVal,differentVal,
    core.convert.IntoFrom.into,prost.error.DecodeError.Insts.CoreConvertFromDecodeErrorKind,
    prost.error.DecodeError.Insts.CoreConvertFromDecodeErrorKind.from,decodeError]

theorem delimited_exact_end {T F B : Type}
    (callback : FnMutBorrowV1.BorrowFnMut F T B prost.encoding.DecodeContext (core.result.Result Unit prost.error.DecodeError))
    (bi : bytes.buf.buf_impl.Buf B) (ctx : prost.encoding.DecodeContext)
    (limit : Usize) (value : T) (before : B) (closure : F)
    (read : bi.remaining before = .ok limit) :
    prost.encoding.merge_loop_loop.body callback bi ctx limit value before closure =
      .ok (.done (.Ok (),value,before)) := by
  simp [prost.encoding.merge_loop_loop.body,Mut0T.Insts.BytesBufBuf_implBuf.remaining,read]
#print axioms actual_closure_projection
#print axioms wrong_wire
#print axioms recursion_zero
#print axioms delimited_overrun
#print axioms delimited_exact_end
end ChatResponseReference.SubmessageV1
