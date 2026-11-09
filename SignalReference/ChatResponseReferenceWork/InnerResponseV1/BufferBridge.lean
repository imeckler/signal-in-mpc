import ChatResponseReferenceWork.InnerResponseV1.Replayed.Types
open Aeneas Aeneas.Std Result
namespace ActualInnerResponseV1
/-- Scope: canonical contiguous input; allocation/content is the inherited model. -/
def toBytesBuf {B : Type} (inst : bytes.buf.buf_impl.Buf B) : ActualResponseBytesV1.bytes.buf.buf_impl.Buf B :=
  let base : ActualResponseBytesV1.bytes.buf.buf_impl.Buf B :=
    ⟨inst.remaining,inst.chunk,inst.advance,fun _ _ => .fail .undef⟩
  {base with copy_to_bytes := ActualResponseBytesV1.bytes.buf.buf_impl.Buf.copy_to_bytes.default base}
noncomputable abbrev prost.encoding.varint.decode_varint {B : Type} (inst : bytes.buf.buf_impl.Buf B) :=
  ActualResponseBytesV1.prost.encoding.varint.decode_varint (toBytesBuf inst)
abbrev prost.encoding.wire_type.check_wire_type := ActualResponseBytesV1.prost.encoding.wire_type.check_wire_type
abbrev prost.error.DecodeError.Insts.CoreConvertFromDecodeErrorKind := ActualResponseBytesV1.prost.error.DecodeError.Insts.CoreConvertFromDecodeErrorKind
end ActualInnerResponseV1
