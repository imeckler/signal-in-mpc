import ChatResponseReferenceWork.BytesContentV1.Replayed.Funs
import ProtoParseWork.FullParserV3Work.Skip.Replayed.Consumption
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.BytesContentV1
open ActualResponseBytesV1
abbrev sliceBuf := Shared0SliceU8.Insts.BytesBufBuf_implBuf
abbrev nativeBuf := bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf

theorem slice_copy (input : Slice U8) (n : Usize) (hn : n.val ≤ input.length) :
    sliceBuf.copy_to_bytes input n = .ok (⟨ContentModel.take input n.val⟩,
      LibSignalReference.Candidate.ProstBytesBuf.drop input n.val) := by
  change (do let remaining ← Result.ok input.len
             if n > remaining then .fail .panic else do
               let chunk ← Result.ok input
               let (copied,_) ← ContentModel.copySlice chunk n
               let next ← LibSignalReference.Candidate.ProstBytesBuf.advance input n
               .ok (copied,next)) = _
  have hnot : ¬n > input.len := by scalar_tac
  simp only [bind_tc_ok,if_neg hnot,ContentModel.copySlice,if_pos hn,
    LibSignalReference.Candidate.ProstBytesBuf.advance,
    if_neg (by omega : ¬input.length < n.val)]

/-- Actual native sealed Bytes replacement consumes a private local buffer and
replaces the old field, with no old-content or backing-allocation dependence. -/
theorem replace_bytes (old value : bytes.bytes.Bytes) :
    bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with nativeBuf old value = .ok value := by
  unfold bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with
  change (do let i ← Result.ok value.contents.len
             let (next,_) ← bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf.copy_to_bytes value i
             .ok next) = _
  simp only [bind_tc_ok]
  unfold bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf.copy_to_bytes ContentModel.copySlice
  rw [if_pos (by simpa only [Slice.len_val] using Nat.le_refl value.contents.length)]
  simp only [bind_tc_ok]
  try dsimp! only
  simp only [bind_tc_ok]
  try dsimp! only
  congr 1
  cases value
  congr 1
  apply Subtype.ext
  simp only [ContentModel.take,Slice.len_val,List.take_length]

#print axioms slice_copy
#print axioms replace_bytes
end ChatResponseReference.BytesContentV1
