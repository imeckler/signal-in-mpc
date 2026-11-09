import ChatResponseReferenceWork.OuterEnvelopeV1.Callbacks
import ChatResponseReferenceWork.InnerResponseV1.Replayed.FunsExternal
open Aeneas Aeneas.Std Result
noncomputable section
namespace ActualOuterEnvelopeV1
abbrev P.Insts.CoreOpsFunctionFnOnceTupleI32.call_once (value : Result I32) (_ : Unit) := value
def core.option.Option.as_ref {T : Type} (value : Option T) : Result (Option T) := .ok value
def core.option.Option.map_or {T U F : Type} (inst : core.ops.function.FnOnce F T U)
    (value : Option T) (fallback : U) (closure : F) : Result U :=
  match value with | none => .ok fallback | some value => inst.call_once closure value
def core.option.Option.Insts.CoreDefaultDefault.default (T : Type) : Result (Option T) := .ok none
def innerBytesAdapter {T : Type} (inst : prost.encoding.BytesAdapter T) : ActualInnerResponseV1.prost.encoding.BytesAdapter T :=
  ⟨⟨inst.sealedBytesAdapterInst.coredefaultDefaultInst,inst.sealedBytesAdapterInst.len,
     inst.sealedBytesAdapterInst.replace_with,fun _ _ _ => .fail .undef⟩⟩
noncomputable def prost.encoding.bytes.merge {T B : Type} (adapter : prost.encoding.BytesAdapter T)
    (inst : bytes.buf.buf_impl.Buf B) := ActualInnerResponseV1.prost.encoding.bytes.merge (innerBytesAdapter adapter) inst
abbrev P.Insts.CoreOpsFunctionFnOnceTupleU64.call_once := @ActualInnerResponseV1.P.Insts.CoreOpsFunctionFnOnceTupleU64.call_once
abbrev P.Insts.CoreOpsFunctionFnOnceTupleU32.call_once := @ActualInnerResponseV1.P.Insts.CoreOpsFunctionFnOnceTupleU32.call_once
abbrev P.Insts.CoreOpsFunctionFnOnceTupleString.call_once := @ActualInnerResponseV1.P.Insts.CoreOpsFunctionFnOnceTupleString.call_once
abbrev P.Insts.CoreOpsFunctionFnOnceTupleBytes.call_once := @ActualInnerResponseV1.P.Insts.CoreOpsFunctionFnOnceTupleBytes.call_once
abbrev core.option.Option.get_or_insert_with := @ActualInnerResponseV1.core.option.Option.get_or_insert_with
abbrev core.result.Result.map_err := @ActualInnerResponseV1.core.result.Result.map_err
abbrev alloc.string.String.Insts.CoreDefaultDefault.default := @ActualInnerResponseV1.alloc.string.String.Insts.CoreDefaultDefault.default
abbrev bytes.bytes.Bytes.Insts.CoreDefaultDefault.default := @ActualInnerResponseV1.bytes.bytes.Bytes.Insts.CoreDefaultDefault.default
abbrev prost.encoding.varint.decode_varint := @ActualInnerResponseV1.prost.encoding.varint.decode_varint
abbrev prost.encoding.wire_type.check_wire_type := @ActualInnerResponseV1.prost.encoding.wire_type.check_wire_type
abbrev prost.encoding.skip_field := @ActualInnerResponseV1.prost.encoding.skip_field
abbrev prost.encoding.uint64.merge := @ActualInnerResponseV1.prost.encoding.uint64.merge
abbrev prost.encoding.uint32.merge := @ActualInnerResponseV1.prost.encoding.uint32.merge
abbrev prost.encoding.string.merge := @ActualInnerResponseV1.prost.encoding.string.merge
abbrev prost.encoding.string.merge_repeated := @ActualInnerResponseV1.prost.encoding.string.merge_repeated
abbrev prost.encoding.message.merge := @ActualSubmessageV1.prost.encoding.message.merge
abbrev bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with := @ActualInnerResponseV1.bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with
abbrev bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.len := @ActualInnerResponseV1.bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.len

/-- Unused encoding/clear slot: fail closed, outside parser observation. -/
def alloc.vec.Vec.clear
  {T : Type} (A : Type) : alloc.vec.Vec T → Result (alloc.vec.Vec T) := by intros; exact .fail .undef

/-- Unused encoding/clear slot: fail closed, outside parser observation. -/
def prost.encoding.string.encode_repeated
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  Std.U32 → Slice String → T0 → Result T0 := by intros; exact .fail .undef

/-- Unused encoding/clear slot: fail closed, outside parser observation. -/
def prost.encoding.uint64.encode
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  Std.U32 → Std.U64 → T0 → Result T0 := by intros; exact .fail .undef

/-- Unused encoding/clear slot: fail closed, outside parser observation. -/
def prost.encoding.uint32.encode
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  Std.U32 → Std.U32 → T0 → Result T0 := by intros; exact .fail .undef

/-- Unused encoding/clear slot: fail closed, outside parser observation. -/
def prost.encoding.uint64.encoded_len
  : Std.U32 → Std.U64 → Result Std.Usize := by intros; exact .fail .undef

/-- Unused encoding/clear slot: fail closed, outside parser observation. -/
def prost.encoding.uint32.encoded_len
  : Std.U32 → Std.U32 → Result Std.Usize := by intros; exact .fail .undef

/-- Unused encoding/clear slot: fail closed, outside parser observation. -/
def prost.encoding.string.encoded_len
  : Std.U32 → String → Result Std.Usize := by intros; exact .fail .undef

/-- Unused encoding/clear slot: fail closed, outside parser observation. -/
def prost.encoding.bytes.encoded_len
  {T0 : Type} (BytesAdapterInst : prost.encoding.BytesAdapter T0) :
  Std.U32 → T0 → Result Std.Usize := by intros; exact .fail .undef

/-- Unused encoding/clear slot: fail closed, outside parser observation. -/
def prost.encoding.string.encoded_len_repeated
  : Std.U32 → Slice String → Result Std.Usize := by intros; exact .fail .undef

/-- Unused encoding/clear slot: fail closed, outside parser observation. -/
def prost.encoding.string.encode
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  Std.U32 → String → T0 → Result T0 := by intros; exact .fail .undef

/-- Unused encoding/clear slot: fail closed, outside parser observation. -/
def bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.append_to
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  bytes.bytes.Bytes → T0 → Result T0 := by intros; exact .fail .undef

/-- Unused encoding/clear slot: fail closed, outside parser observation. -/
def prost.encoding.bytes.encode
  {T0 : Type} {T1 : Type} (BytesAdapterInst : prost.encoding.BytesAdapter T0)
  (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T1) :
  Std.U32 → T0 → T1 → Result T1 := by intros; exact .fail .undef

end ActualOuterEnvelopeV1
