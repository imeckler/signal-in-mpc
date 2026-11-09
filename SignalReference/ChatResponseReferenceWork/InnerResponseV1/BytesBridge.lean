import ChatResponseReferenceWork.InnerResponseV1.BufferBridge
open Aeneas Aeneas.Std Result
namespace ActualInnerResponseV1
def fromBytesBuf {B : Type} (inst : ActualResponseBytesV1.bytes.buf.buf_impl.Buf B) : bytes.buf.buf_impl.Buf B :=
  ⟨inst.remaining,inst.chunk,inst.advance⟩
def bytesAdapter {T : Type} (inst : prost.encoding.BytesAdapter T) : ActualResponseBytesV1.prost.encoding.BytesAdapter T :=
  ⟨⟨inst.sealedBytesAdapterInst.coredefaultDefaultInst,
    inst.sealedBytesAdapterInst.len,
    fun native => inst.sealedBytesAdapterInst.replace_with (fromBytesBuf native),
    fun _ _ _ => .fail .undef⟩⟩
noncomputable def prost.encoding.bytes.merge {T B : Type} (adapter : prost.encoding.BytesAdapter T)
    (inst : bytes.buf.buf_impl.Buf B) :=
  ActualResponseBytesV1.prost.encoding.bytes.merge (bytesAdapter adapter) (toBytesBuf inst)
noncomputable def bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with {B : Type}
    (inst : bytes.buf.buf_impl.Buf B) :=
  ActualResponseBytesV1.bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with (toBytesBuf inst)
abbrev bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.len :=
  ActualResponseBytesV1.bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.len
def bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.append_to {B : Type}
    (_ : bytes.buf.buf_mut.BufMut B) (_ : bytes.bytes.Bytes) (_ : B) : Result B := .fail .undef
abbrev bytes.bytes.Bytes.Insts.CoreDefaultDefault.default :=
  ActualResponseBytesV1.bytes.bytes.Bytes.Insts.CoreDefaultDefault.default
end ActualInnerResponseV1
