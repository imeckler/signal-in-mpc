import BytesReferenceWork.Replayed.BufModel
import ProtoParseWork.FieldReferenceWork.Generated.bytes_step.Funs

namespace LibSignalReference.Candidate.ProstBytesBuf
open Aeneas Aeneas.Std ProstBytesCandidate
set_option maxHeartbeats 400000

theorem copy_slice_spec (view : Slice U8) (n : Usize) (hn : n.val ≤ view.length) :
    sliceBuf.copy_to_bytes view n = Result.ok (⟨ContentModel.take view n.val⟩,drop view n.val) := by
  exact if_pos hn

theorem copy_slice_overflow (view : Slice U8) (n : Usize) (hn : view.length < n.val) :
    sliceBuf.copy_to_bytes view n = Result.fail .panic := by
  exact if_neg (by omega)

theorem copy_contents_partition (view : Slice U8) (n : Nat) :
    (ContentModel.take view n).val ++ (drop view n).val = view.val := List.take_append_drop _ _

theorem copy_contents_length (view : Slice U8) (n : Nat) (hn : n ≤ view.length) :
    (ContentModel.take view n).length = n := by
  simp only [ContentModel.take,Slice.length,List.length_take]
  exact Nat.min_eq_left hn

theorem default_contiguous_copy (view : Slice U8) (n : Usize) (hn : n.val ≤ view.length) :
    bytes.buf.buf_impl.Buf.copy_to_bytes.default sliceBuf view n =
      Result.ok (⟨ContentModel.take view n.val⟩,drop view n.val) := by
  unfold bytes.buf.buf_impl.Buf.copy_to_bytes.default
  change (do
    let remaining ← Result.ok view.len
    if n > remaining then Result.fail .panic else do
      let chunk ← Result.ok view
      let (copied,_) ← ContentModel.copySlice chunk n
      let next ← advance view n
      Result.ok (copied,next)) = _
  have hnot : ¬n > view.len := by scalar_tac
  simp only [bind_tc_ok,if_neg hnot,ContentModel.copySlice,if_pos hn,advance]
  simp only [if_neg (by omega : ¬view.length < n.val),bind_tc_ok]

theorem bytes_copy_spec (view : Slice U8) (n : Usize) (hn : n.val ≤ view.length) :
    bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf.copy_to_bytes ⟨view⟩ n =
      Result.ok (⟨ContentModel.take view n.val⟩,⟨drop view n.val⟩) := by
  simp only [bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf.copy_to_bytes,
    ContentModel.copySlice,if_pos hn,bind_tc_ok]
  rfl

#print axioms copy_slice_spec
#print axioms copy_slice_overflow
#print axioms copy_contents_partition
#print axioms copy_contents_length
#print axioms default_contiguous_copy
#print axioms bytes_copy_spec
end LibSignalReference.Candidate.ProstBytesBuf
