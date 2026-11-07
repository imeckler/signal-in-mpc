import SkipTranslatorWork.LoopMonotone
import SkipTranslatorWork.Generated.skip.Types

/-! Candidate external wrappers for bytes1.12.0. These follow the pinned
Buf default get_u8 and mutable-reference forwarding bodies. No decoder body
is supplied here. Buffer-law and safe-access proofs belong to BufModel. -/
namespace LoopSupportSkip
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

/-- Pinned core::result::Result::map: invoke FnOnce only for Ok; propagate Err.
This is a standard external model, not a replacement of any Prost body. -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map"]
def core.result.Result.map {T E U F : Type} (fnInst : core.ops.function.FnOnce F T U)
    (result : core.result.Result T E) (fn : F) : Result (core.result.Result U E) :=
  match result with
  | .Ok value => do
    let mapped ← fnInst.call_once fn value
    .ok (.Ok mapped)
  | .Err error => .ok (.Err error)

end LoopSupportSkip
