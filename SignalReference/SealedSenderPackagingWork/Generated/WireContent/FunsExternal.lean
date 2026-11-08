import SealedSenderPackagingWork.Generated.WireContent.Types
import SealedSenderPackagingWork.VecPayloadReference
import SignalMessageWork.BytesFieldWork.GeneratedSelected.Funs

/- Actual previously extracted helpers are reused; container operations use the
explicit bounded content boundary. No field/payload/crypto correctness flag or
assumed AES/HMAC function is supplied. -/
namespace SealedSenderPackaging
open Aeneas Aeneas.Std

def core.ops.range.RangeInclusive.contains := @_root_.ProstBytesField.core.ops.range.RangeInclusive.contains

def alloc.vec.Vec.as_slice {T : Type} (_A : Type) (value : Aeneas.Std.alloc.vec.Vec T) : Result (Slice T) :=
  .ok (Aeneas.Std.alloc.vec.Vec.deref value)

def alloc.vec.Vec.Insts.CoreDefaultDefault.default (T : Type) : Result (Aeneas.Std.alloc.vec.Vec T) :=
  .ok (Aeneas.Std.alloc.vec.Vec.new T)

def Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance :=
  SealedSenderAppend.Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance

def Shared0SliceU8.Insts.BytesBufBuf_implBuf.chunk :=
  SealedSenderAppend.Shared0SliceU8.Insts.BytesBufBuf_implBuf.chunk

def Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining :=
  SealedSenderAppend.Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining

def prost.encoding.MIN_TAG : Result U32 := .ok _root_.ProstBytesField.encoding.MIN_TAG

def prost.encoding.MAX_TAG : Result U32 := _root_.ProstBytesField.encoding.MAX_TAG

def forwardSourceBuf {B : Type} (inst : bytes.buf.buf_impl.Buf B) :
    ProstAdapterCandidate.bytes.buf.buf_impl.Buf B where
  remaining := inst.remaining
  chunk := inst.chunk
  advance := inst.advance
  has_remaining := fun buf => do
    let n ← inst.remaining buf
    .ok (n>0#usize)

def alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.replace_with
    {B : Type} (inst : bytes.buf.buf_impl.Buf B) (old : Aeneas.Std.alloc.vec.Vec U8) (buf : B) :
    Result (Aeneas.Std.alloc.vec.Vec U8) :=
  ProstAdapterCandidate.alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.replace_with (forwardSourceBuf inst) old buf

end SealedSenderPackaging
