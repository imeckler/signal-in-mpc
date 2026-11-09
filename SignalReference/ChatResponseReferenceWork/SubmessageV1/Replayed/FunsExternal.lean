import ChatResponseReferenceWork.SubmessageV1.Replayed.Types
import ChatResponseReferenceWork.FnMutBorrowV1.Projection
import ChatResponseReferenceWork.InnerResponseV1.BufferBridge
open Aeneas Aeneas.Std Result
namespace ActualSubmessageV1
/-- Actual shared/mutable forwarding projected through the established safe
contiguous buffer operation; no ignored backward mutation. -/
def Mut0T.Insts.BytesBufBuf_implBuf.remaining {T : Type} (inst : bytes.buf.buf_impl.Buf T) :
    T → Result Usize := inst.remaining
noncomputable abbrev prost.encoding.varint.decode_varint {T : Type} (inst : bytes.buf.buf_impl.Buf T) :=
  ActualInnerResponseV1.prost.encoding.varint.decode_varint inst
abbrev prost.encoding.wire_type.check_wire_type := ActualResponseBytesV1.prost.encoding.wire_type.check_wire_type
abbrev prost.encoding.DecodeContext.Insts.CoreCloneClone.clone :=
  ActualInnerScanV1.prost.encoding.DecodeContext.Insts.CoreCloneClone.clone
noncomputable def prost.encoding.decode_key {T : Type} (inst : bytes.buf.buf_impl.Buf T) :
    T → Result (core.result.Result (U32 × prost.encoding.wire_type.WireType) prost.error.DecodeError × T) :=
  ActualInnerScanV1.prost.encoding.decode_key
    ⟨inst.remaining,inst.chunk,inst.advance,fun value => do
      let count ← inst.remaining value
      .ok (count > 0#usize)⟩
end ActualSubmessageV1
