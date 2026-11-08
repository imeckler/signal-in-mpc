import ChatResponseReferenceWork.BytesContentV1.Replayed.Types
import BytesReferenceWork.Replayed.BufModel
import ProtoParseWork.FullParserV3Work.Skip.Replayed.WrapperReference
namespace ActualResponseBytesV1
open Aeneas Aeneas.Std

@[trait_default, rust_fun "bytes::buf::buf_impl::Buf::get_u8"]
def bytes.buf.buf_impl.Buf.get_u8.default
    {Self : Type} (BufInst : bytes.buf.buf_impl.Buf Self) (buf : Self) : Result (U8 × Self) := do
  let remaining ← BufInst.remaining buf
  if remaining < 1#usize then .fail .panic else do
    let chunk ← BufInst.chunk buf
    let byte ← Slice.index_usize chunk 0#usize
    let next ← BufInst.advance buf 1#usize
    .ok (byte,next)

@[rust_fun "bytes::buf::buf_impl::{bytes::buf::buf_impl::Buf<&'0 mut @T>}::remaining"]
def bytes.buf.buf_impl.Buf.partial_TraitDecl_14.Blanket.remaining
    {T : Type} (BufInst : bytes.buf.buf_impl.Buf T) : T → Result Usize := BufInst.remaining

@[rust_fun "bytes::buf::buf_impl::{bytes::buf::buf_impl::Buf<&'0 mut @T>}::chunk"]
def Mut0T.Insts.BytesBufBuf_implBuf.chunk
    {T : Type} (BufInst : bytes.buf.buf_impl.Buf T) : T → Result (Slice U8) := BufInst.chunk

namespace ContentModel

def take (view : Slice U8) (n : Nat) : Slice U8 :=
  ⟨view.val.take n,by have h := view.property; simp only [List.length_take]; omega⟩
def drop (view : Slice U8) (n : Nat) : Slice U8 :=
  ⟨view.val.drop n,by have h := view.property; simp only [List.length_drop]; omega⟩
def copySlice (view : Slice U8) (n : Usize) : Result (bytes.bytes.Bytes × Slice U8) :=
  if n.val ≤ view.length then .ok (⟨take view n.val⟩,drop view n.val)
  else .fail .panic
end ContentModel

/-- Explicit bounded model: only contiguous Buf instances whose chunk contains
all remaining bytes. No arbitrary segmented or effectful Buf claim. -/
@[trait_default, rust_fun "bytes::buf::buf_impl::Buf::copy_to_bytes"]
def bytes.buf.buf_impl.Buf.copy_to_bytes.default
    {Self : Type} (BufInst : bytes.buf.buf_impl.Buf Self) (buf : Self) (n : Usize) :
    Result (bytes.bytes.Bytes × Self) := do
  let remaining ← BufInst.remaining buf
  if n > remaining then .fail .panic else do
    let view ← BufInst.chunk buf
    let (copied,_) ← ContentModel.copySlice view n
    let next ← BufInst.advance buf n
    .ok (copied,next)

@[rust_fun "bytes::bytes::{bytes::buf::buf_impl::Buf<bytes::bytes::Bytes>}::remaining"]
def bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf.remaining (buf : bytes.bytes.Bytes) : Result Usize :=
  .ok buf.contents.len

@[rust_fun "bytes::bytes::{bytes::buf::buf_impl::Buf<bytes::bytes::Bytes>}::chunk"]
def bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf.chunk (buf : bytes.bytes.Bytes) : Result (Slice U8) :=
  .ok buf.contents

@[rust_fun "bytes::bytes::{bytes::buf::buf_impl::Buf<bytes::bytes::Bytes>}::advance"]
def bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf.advance (buf : bytes.bytes.Bytes) (n : Usize) :
    Result bytes.bytes.Bytes :=
  if n.val ≤ buf.contents.length then .ok ⟨ContentModel.drop buf.contents n.val⟩ else .fail .panic

@[rust_fun "bytes::bytes::{bytes::buf::buf_impl::Buf<bytes::bytes::Bytes>}::copy_to_bytes"]
def bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf.copy_to_bytes (buf : bytes.bytes.Bytes) (n : Usize) :
    Result (bytes.bytes.Bytes × bytes.bytes.Bytes) := do
  let (copied,rest) ← ContentModel.copySlice buf.contents n
  .ok (copied,⟨rest⟩)

end ActualResponseBytesV1


namespace ActualResponseBytesV1
open Aeneas Aeneas.Std
abbrev Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining := LibSignalReference.Candidate.ProstBytesBuf.remaining
abbrev Shared0SliceU8.Insts.BytesBufBuf_implBuf.chunk := LibSignalReference.Candidate.ProstBytesBuf.chunk
abbrev Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance := LibSignalReference.Candidate.ProstBytesBuf.advance
def bytes.bytes.Bytes.Insts.CoreDefaultDefault.default : Result bytes.bytes.Bytes := .ok ⟨⟨[],by simp⟩⟩
def bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.len (value : bytes.bytes.Bytes) : Result Usize := .ok value.contents.len
/-- Unused encoding-only operation fails closed; no decode theorem invokes it. -/
def bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.append_to {B : Type}
    (_ : bytes.buf.buf_mut.BufMut B) (_ : bytes.bytes.Bytes) (_ : B) : Result B := .fail .undef
def fromSkipWire : LoopSupportSkip.encoding.wire_type.WireType → prost.encoding.wire_type.WireType
  | .Varint => .Varint | .SixtyFourBit => .SixtyFourBit | .LengthDelimited => .LengthDelimited
  | .StartGroup => .StartGroup | .EndGroup => .EndGroup | .ThirtyTwoBit => .ThirtyTwoBit

def fromSkipKind : LoopSupportSkip.error.DecodeErrorKind → prost.error.DecodeErrorKind
  | .LengthDelimiterTooLarge => .LengthDelimiterTooLarge
  | .InvalidVarint => .InvalidVarint
  | .RecursionLimitReached => .RecursionLimitReached
  | .InvalidWireType n => .InvalidWireType n
  | .InvalidKey n => .InvalidKey n
  | .InvalidTag => .InvalidTag
  | .UnexpectedWireType a b => .UnexpectedWireType (fromSkipWire a) (fromSkipWire b)
  | .BufferUnderflow => .BufferUnderflow
  | .DelimitedLengthExceeded => .DelimitedLengthExceeded
  | .UnexpectedEndGroupTag => .UnexpectedEndGroupTag
  | .InvalidString => .InvalidString
  | .UnexpectedTypeUrl a b => .UnexpectedTypeUrl a b
  | .Other (.Borrowed s) => .Other (.Borrowed s)
  | .Other (.Owned s) => .Other (.Owned s)

def fromSkipError (e : LoopSupportSkip.error.DecodeError) : prost.error.DecodeError :=
  ⟨⟨fromSkipKind e.inner.description,e.inner.stack⟩⟩

def toSkipBuf {B : Type} (inst : bytes.buf.buf_impl.Buf B) : LoopSupportSkip.bytes.buf.buf_impl.Buf B :=
  let base : LoopSupportSkip.bytes.buf.buf_impl.Buf B := ⟨inst.remaining,inst.chunk,inst.advance,fun _ => .fail .panic⟩
  {base with get_u8 := LoopSupportSkip.bytes.buf.buf_impl.Buf.get_u8.default base}

noncomputable def prost.encoding.varint.decode_varint {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (before : B) : Result ((core.result.Result U64 prost.error.DecodeError) × B) := do
  let (r,after) ← LoopSupportSkip.encoding.varint.decode_varint (toSkipBuf inst) before
  match r with
  | .Ok n => .ok (.Ok n,after)
  | .Err error => .ok (.Err (fromSkipError error),after)
end ActualResponseBytesV1
