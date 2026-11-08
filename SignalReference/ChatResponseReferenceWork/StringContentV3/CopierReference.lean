import ChatResponseReferenceWork.StringContentV3.Generated.Funs
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.StringContentV3
open ActualStringContentV3
open ChatResponseReference.ContiguousPut
open ChatResponseReference.ContiguousPut.GeneratedReference
/-- Canonical instantiated content semantics of the actual Vec.put call selected
opaque in the String extraction. No arbitrary Buf dictionary claim. -/
theorem put_slice_reference
    (inst : bytes.buf.buf_impl.Buf.partial_TraitDecl_29 (Slice U8))
    (value : alloc.vec.Vec U8) (src : bytes.buf.take.Take.partial_Type_37 (Slice U8)) :
    alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put inst value src =
      if bound : value.length+(view ⟨src.inner,src.limit⟩).length ≤ Usize.max then
        .ok (append value (view ⟨src.inner,src.limit⟩) bound,
          {src with inner := LibSignalReference.Candidate.ProstBytesBuf.drop src.inner (view ⟨src.inner,src.limit⟩).length})
      else .fail .panic := by
  unfold alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put
  simp only [_root_.dite_true]
  rw [put_reference]
  split <;> simp only [bind_tc_ok,bind_tc_fail]
  all_goals dsimp! only
def sliceBuf : bytes.buf.buf_impl.Buf (Slice U8) :=
  ⟨LibSignalReference.Candidate.ProstBytesBuf.remaining,
   LibSignalReference.Candidate.ProstBytesBuf.chunk,
   LibSignalReference.Candidate.ProstBytesBuf.advance,
   fun s n => .ok ⟨s,n⟩⟩
abbrev sourceInst := bytes.buf.buf_impl.Buf.partial_TraitDecl_28.Blanket sliceBuf
abbrev takeInst := bytes.buf.buf_impl.Buf.partial_TraitDecl_29.Blanket sourceInst

theorem replace_slice_reference (old : alloc.vec.Vec U8) (input : Slice U8) (limit : Usize) :
    alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.replace_with takeInst old ⟨input,limit⟩ =
      .ok (LibSignalReference.Candidate.ProstVecAdapter.fromSlice (view ⟨input,limit⟩),
        ⟨LibSignalReference.Candidate.ProstBytesBuf.drop input (view ⟨input,limit⟩).length,limit⟩) := by
  let s : TakeState := ⟨input,limit⟩
  have remain : bytes.buf.buf_impl.Buf.partial_TraitDecl_29.Blanket.remaining sourceInst ⟨input,limit⟩ = .ok (view s).len := by
    change Aeneas.Std.Result.ok (core.cmp.impls.OrdUsize.min input.len limit) = _
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [core.cmp.impls.OrdUsize.min_val,Slice.len_val,view_length,Nat.min_comm,s]
  unfold alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.replace_with alloc.vec.Vec.clear
  simp only [bind_tc_ok]
  rw [remain]
  simp only [bind_tc_ok]
  have reserve : alloc.vec.Vec.reserve Global (alloc.vec.Vec.new U8) (view s).len = .ok (alloc.vec.Vec.new U8) := by
    unfold alloc.vec.Vec.reserve ProstAdapterCandidate.alloc.vec.Vec.reserve
    apply if_pos
    simpa only [alloc.vec.Vec.length,alloc.vec.Vec.new, List.length_nil, Nat.zero_add,Slice.len_val] using (view s).property
  rw [reserve]
  simp only [bind_tc_ok]
  rw [put_slice_reference]
  have bound : (alloc.vec.Vec.new U8).length + (view s).length ≤ Usize.max := by
    simpa only [alloc.vec.Vec.length,alloc.vec.Vec.new,List.length_nil,Nat.zero_add] using (view s).property
  rw [dif_pos bound]
  simp only [bind_tc_ok]
  dsimp! only
  rfl
#print axioms put_slice_reference
#print axioms replace_slice_reference
end ChatResponseReference.StringContentV3
