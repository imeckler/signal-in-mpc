import ProtoParseWork.FieldReferenceWork.Generated.bytes_step.Types

/-! Candidate external wrappers for bytes1.12.0. These follow the pinned
Buf default get_u8 and mutable-reference forwarding bodies. No decoder body
is supplied here. Buffer-law and safe-access proofs belong to BufModel. -/
namespace ProstBytesCandidate
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
def Mut0T.Insts.BytesBufBuf_implBuf.remaining
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

end ProstBytesCandidate
