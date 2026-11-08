import ProtoParseWork.BytesReferenceWork.Generated.vec_replace_put_body.Types

namespace ProstAdapterCandidate
open Aeneas Aeneas.Std

/-- Content model, scoped to Vec<u8> parsing and successful allocation. Capacity
and allocator state are not observed. Bounds follow the existing Aeneas Vec
model. Rust applicability additionally requires valid buffers and successful
allocation below isize::MAX; these are external model preconditions, not
properties of every model Vec. No arbitrary element sizes or Drop effects. -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::reserve"]
def alloc.vec.Vec.reserve {T : Type} (_A : Type) (vec : alloc.vec.Vec T) (n : Usize) :
    Result (alloc.vec.Vec T) :=
  if vec.length + n.val ≤ Usize.max then .ok vec else .fail .panic

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::clear"]
def alloc.vec.Vec.clear {T : Type} (_A : Type) (_vec : alloc.vec.Vec T) : Result (alloc.vec.Vec T) :=
  .ok (alloc.vec.Vec.new T)

@[trait_default, rust_fun "bytes::buf::buf_impl::Buf::has_remaining"]
def bytes.buf.buf_impl.Buf.has_remaining.default {Self : Type}
    (inst : bytes.buf.buf_impl.Buf Self) (buf : Self) : Result Bool := do
  let n ← inst.remaining buf
  .ok (n > 0#usize)

end ProstAdapterCandidate
