import ChatResponseReferenceWork.StringContentV3.ContiguousPut.GeneratedOneStep.Types
import ChatResponseReferenceWork.TypedLoanProjection
import BytesReferenceWork.Replayed.BufModel
import BytesReferenceWork.VecReference
open Aeneas Aeneas.Std Result
namespace ContiguousPutOneStep
open ChatResponseReference.TypedLoanProjection
/-- Same bounded successful-allocation Vec content model as the accepted source
loop. Actual code here is instantiated only at Vec<u8>. -/
def alloc.vec.Vec.reserve {T : Type} (A : Type) (v : alloc.vec.Vec T) (n : Usize) :=
  ProstAdapterCandidate.alloc.vec.Vec.reserve A v n
@[trait_default]
def bytes.buf.buf_impl.Buf.has_remaining.default {B : Type}
    (inst : bytes.buf.buf_impl.Buf B) (s : B) : Result Bool := do
  let n ← inst.remaining s
  .ok (n > 0#usize)
@[trait_default]
def bytes.buf.buf_impl.Buf.has_remaining.partial_Fun_186.default {B : Type}
    (inst : bytes.buf.buf_impl.Buf.partial_TraitDecl_4 B)
    (s : bytes.buf.take.Take.partial_Type_10 B) : Result Bool := do
  let n ← inst.remaining s
  .ok (n > 0#usize)
@[trait_default]
def bytes.buf.buf_impl.Buf.has_remaining.partial_Fun_189.default {B : Type}
    (inst : bytes.buf.buf_impl.Buf.partial_TraitDecl_3 B) (s : B) : Result Bool := do
  let n ← inst.remaining s
  .ok (n > 0#usize)
def bytes.buf.buf_impl.Buf.partial_TraitDecl_3.Blanket.remaining {B : Type}
    (inst : bytes.buf.buf_impl.Buf B) := inst.remaining
def bytes.buf.buf_impl.Buf.partial_TraitDecl_3.Blanket.chunk {B : Type}
    (inst : bytes.buf.buf_impl.Buf B) := inst.chunk
/-- Tagged ABI bridge: standalone calls retain raw auxiliary returns; trait
fields use the proved receiver projection. No arbitrary function is coerced. -/
def bytes.buf.buf_impl.Buf.partial_TraitDecl_3.Blanket.advance {B : Type}
    (inst : bytes.buf.buf_impl.Buf B) : LoanOp B Usize :=
  actualAdvance ⟨inst.remaining,inst.chunk,inst.advance⟩
def bytes.buf.buf_impl.Buf.partial_TraitDecl_3.Blanket.has_remaining {B : Type}
    (inst : bytes.buf.buf_impl.Buf B) := inst.has_remaining
/-- Reuse the accepted safe contiguous slice operations, including the exact
panic-before-update bounds behavior. -/
def Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance :=
  LibSignalReference.Candidate.ProstBytesBuf.advance
def Shared0SliceU8.Insts.BytesBufBuf_implBuf.chunk :=
  LibSignalReference.Candidate.ProstBytesBuf.chunk
def Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining :=
  LibSignalReference.Candidate.ProstBytesBuf.remaining
/-- Executable Take content models follow the native order: limit assertion,
inner advance, then limit subtraction. The raw helper restores its inner loan;
only the stated receiver projection is native observable. -/
def takeAdvanceRaw {B : Type} (inst : bytes.buf.buf_impl.Buf.partial_TraitDecl_3 B)
    (s : bytes.buf.take.Take.partial_Type_10 B) (count : Usize) :
    Result ((bytes.buf.take.Take.partial_Type_10 B) ×
      (bytes.buf.take.Take.partial_Type_10 B → bytes.buf.take.Take.partial_Type_10 B)) := do
  massert (count ≤ s.limit)
  let inner ← inst.advance s.inner count
  let limit ← UScalar.sub s.limit count
  let next : bytes.buf.take.Take.partial_Type_10 B := ⟨inner,limit⟩
  .ok (next,fun final => {next with inner := final.inner})
def bytes.buf.buf_impl.Buf.partial_TraitDecl_4.Blanket.advance {B : Type}
    (inst : bytes.buf.buf_impl.Buf.partial_TraitDecl_3 B) :
    LoanOp (bytes.buf.take.Take.partial_Type_10 B) Usize where
  raw := takeAdvanceRaw inst
  observed := fun s n => do
    let (next,restore) ← takeAdvanceRaw inst s n
    .ok (restore next)
  correspondence := fun _ _ => rfl
def bytes.buf.buf_impl.Buf.partial_TraitDecl_4.Blanket.chunk {B : Type}
    (inst : bytes.buf.buf_impl.Buf.partial_TraitDecl_3 B)
    (s : bytes.buf.take.Take.partial_Type_10 B) : Result (Slice U8) := do
  let chunk ← inst.chunk s.inner
  .ok (ProstBytesCandidate.ContentModel.take chunk s.limit.val)
def bytes.buf.buf_impl.Buf.partial_TraitDecl_4.Blanket.remaining {B : Type}
    (inst : bytes.buf.buf_impl.Buf.partial_TraitDecl_3 B)
    (s : bytes.buf.take.Take.partial_Type_10 B) : Result Usize := do
  let remaining ← inst.remaining s.inner
  .ok (core.cmp.impls.OrdUsize.min remaining s.limit)
end ContiguousPutOneStep
