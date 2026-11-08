import ChatResponseReferenceWork.StringContentV3.ContiguousPut.GeneratedOneStep.Funs
import ChatResponseReferenceWork.StringContentV3.ContiguousPut.CanonicalTake
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.ContiguousPut.GeneratedReference
open ContiguousPutOneStep
open ChatResponseReference.ContiguousPut
abbrev Src := bytes.buf.take.Take.partial_Type_10 (Slice U8)
def encode (s : TakeState) : Src := ⟨s.inner,s.limit⟩
abbrev innerInst := bytes.buf.buf_impl.Buf.partial_TraitDecl_3.Blanket
  Shared0SliceU8.Insts.BytesBufBuf_implBuf
abbrev takeInst := bytes.buf.buf_impl.Buf.partial_TraitDecl_4.Blanket innerInst

theorem remaining_eq (s : TakeState) : takeInst.remaining (encode s) = .ok (view s).len := by
  change Aeneas.Std.Result.ok (core.cmp.impls.OrdUsize.min s.inner.len s.limit) = .ok (view s).len
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [core.cmp.impls.OrdUsize.min_val,Slice.len_val,view_length,Nat.min_comm]
theorem chunk_eq (s : TakeState) : takeInst.chunk (encode s) = .ok (view s) := rfl

theorem sub_limit (limit count : Usize) (bound : count.val ≤ limit.val) :
    UScalar.sub limit count = .ok (subtractLimit limit count) := by
  unfold UScalar.sub
  rw [if_neg (Nat.not_lt.mpr bound)]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [subtractLimit_val]
  change (limit.val-count.val) % 2^UScalarTy.Usize.numBits = limit.val-count.val
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) limit.bv.isLt)

theorem advance_view_raw (s : TakeState) :
    (bytes.buf.buf_impl.Buf.partial_TraitDecl_4.Blanket.advance innerInst)
      (encode s) (view s).len = .ok
        (encode (after s),fun final => {encode (after s) with inner := final.inner}) := by
  have bounds := view_bounds s
  have limit_bound : (view s).len ≤ s.limit := by scalar_tac
  have inner_bound : ¬s.inner.length < (view s).len.val := by simpa only [Slice.len_val] using Nat.not_lt.mpr bounds.2
  change takeAdvanceRaw innerInst (encode s) (view s).len = _
  unfold takeAdvanceRaw
  simp only [encode,limit_bound,massert,if_true,bind_tc_ok]
  change (do
    let inner ← LibSignalReference.Candidate.ProstBytesBuf.advance s.inner (view s).len
    let limit ← UScalar.sub s.limit (view s).len
    let next : Src := ⟨inner,limit⟩
    .ok (next,fun (final : Src) => {next with inner := final.inner})) = _
  unfold LibSignalReference.Candidate.ProstBytesBuf.advance
  rw [if_neg inner_bound]
  simp only [bind_tc_ok]
  rw [sub_limit s.limit (view s).len (by simpa only [Slice.len_val] using bounds.1)]
  rfl
theorem has_remaining_eq (s : TakeState) :
    bytes.buf.buf_impl.Buf.has_remaining.partial_Fun_186.default takeInst (encode s) =
      .ok (decide (0 < (view s).length)) := by
  unfold bytes.buf.buf_impl.Buf.has_remaining.partial_Fun_186.default
  rw [remaining_eq]
  simp only [bind_tc_ok]
  rfl

def append (value : alloc.vec.Vec U8) (chunk : Slice U8)
    (bound : value.length+chunk.length ≤ Usize.max) : alloc.vec.Vec U8 :=
  ⟨value.val++chunk.val,by simpa only [List.length_append] using bound⟩
theorem extend_bound (value : alloc.vec.Vec U8) (chunk : Slice U8)
    (bound : value.length+chunk.length ≤ Usize.max) :
    Aeneas.Std.alloc.vec.Vec.extend_from_slice core.clone.CloneU8 value chunk =
      .ok (append value chunk bound) := by
  unfold Aeneas.Std.alloc.vec.Vec.extend_from_slice
  rw [dif_pos bound]
  have hc : Slice.clone (liftFun1 core.clone.impls.CloneU8.clone) chunk = .ok chunk :=
    LibSignalReference.Candidate.ProstVecAdapter.clone_u8 chunk
  split
  · rename_i next he
    rw [hc] at he
    cases he
    rfl
  · rename_i error he
    rw [hc] at he
    cases he
  · rename_i he
    rw [hc] at he
    cases he
theorem take_ctor (input : Slice U8) (limit : Usize) :
    bytes.buf.buf_impl.Buf.take.partial_Fun_184.default input limit =
      .ok (encode ⟨input,limit⟩,fun (state : Src) => state.inner) := rfl

theorem put_reference (value : alloc.vec.Vec U8) (input : Slice U8) (limit : Usize) :
    put_contiguous_one_step value input limit =
      if bound : value.length+(view ⟨input,limit⟩).length ≤ Usize.max then
        .ok (append value (view ⟨input,limit⟩) bound,
          LibSignalReference.Candidate.ProstBytesBuf.drop input (view ⟨input,limit⟩).length)
      else .fail .panic := by
  let s : TakeState := ⟨input,limit⟩
  unfold put_contiguous_one_step
  rw [take_ctor]
  simp only [bind_tc_ok]
  dsimp! only
  have hr : bytes.buf.buf_impl.Buf.partial_TraitDecl_4.Blanket.remaining innerInst (encode s) =
      .ok (view s).len := remaining_eq s
  rw [hr]
  simp only [bind_tc_ok]
  by_cases bound : value.length+(view s).length ≤ Usize.max
  · rw [dif_pos bound]
    have reserve : alloc.vec.Vec.reserve Global value (view s).len = .ok value := by
      unfold alloc.vec.Vec.reserve ProstAdapterCandidate.alloc.vec.Vec.reserve
      exact if_pos (by simpa only [Slice.len_val] using bound)
    rw [reserve]
    simp only [bind_tc_ok]
    rw [has_remaining_eq s]
    simp only [bind_tc_ok]
    by_cases empty : (view s).length = 0
    · have zero : ¬0 < (view s).length := by omega
      simp only [zero,decide_false,Bool.false_eq_true,if_false]
      have bytes_empty : (view s).val = [] := List.eq_nil_of_length_eq_zero empty
      apply congrArg Result.ok
      apply Prod.ext
      · apply Subtype.ext
        change value.val = value.val ++ (view s).val
        rw [bytes_empty,List.append_nil]
      · apply Subtype.ext
        change input.val = List.drop (view s).length input.val
        rw [empty,List.drop_zero]
    · have positive : 0 < (view s).length := by omega
      simp only [positive,decide_true,if_true]
      have hchunk : bytes.buf.buf_impl.Buf.partial_TraitDecl_4.Blanket.chunk innerInst (encode s) = .ok (view s) := chunk_eq s
      rw [hchunk]
      simp only [bind_tc_ok]
      rw [extend_bound value (view s) bound]
      simp only [bind_tc_ok]
      rw [advance_view_raw s]
      simp only [bind_tc_ok]
      dsimp! only
      rw [has_remaining_eq (after s),after_empty]
      rfl
  · rw [dif_neg bound]
    have reserve : alloc.vec.Vec.reserve Global value (view s).len = .fail .panic := by
      unfold alloc.vec.Vec.reserve ProstAdapterCandidate.alloc.vec.Vec.reserve
      exact if_neg (by simpa only [Slice.len_val] using bound)
    rw [reserve]
    rfl
#print axioms remaining_eq
#print axioms advance_view_raw
#print axioms has_remaining_eq
#print axioms extend_bound
#print axioms put_reference
end ChatResponseReference.ContiguousPut.GeneratedReference
