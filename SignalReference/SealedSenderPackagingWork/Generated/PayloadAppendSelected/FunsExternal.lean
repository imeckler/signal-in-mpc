import SealedSenderPackagingWork.Generated.PayloadAppendSelected.Types
import BytesReferenceWork.Replayed.BufModel

/- Functional container boundary, matching the scoped existing Slice/Vec content
models. Allocation success/isize bound, addresses, capacity, aliasing and Drop/
erasure remain external. No AES/HMAC or payload-copy result is supplied here. -/
namespace SealedSenderAppend
open Aeneas Aeneas.Std

def alloc.vec.Vec.as_slice {T : Type} (_A : Type)
    (value : Aeneas.Std.alloc.vec.Vec T) : Result (Slice T) :=
  .ok (Aeneas.Std.alloc.vec.Vec.deref value)

def Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance (view : Slice U8) (n : Usize) : Result (Slice U8) :=
  LibSignalReference.Candidate.ProstBytesBuf.advance view n

end SealedSenderAppend
