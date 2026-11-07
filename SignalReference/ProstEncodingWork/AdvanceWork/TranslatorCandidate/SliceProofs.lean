import ProstEncodingWork.AdvanceWork.TranslatorCandidate.Generated.Candidate.Slice.Funs

namespace LibSignalReference.Candidate.SliceAdvance

open Aeneas Aeneas.Std

/-- Candidate translated actual helper, using the unchanged standard
formatting models. Its argument fields and actual panic branch are retained. -/
theorem panic_exact (error : BytesSliceAdvance.TryGetError) :
    BytesSliceAdvance.panic_advance error = .fail .panic := rfl

theorem advance_success (self : Slice U8) (count : Usize)
    (h : count.val ≤ self.length) :
    BytesSliceAdvance.Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance self count =
      .ok (self.drop count) := by
  have not_beyond : ¬ Slice.len self < count := by scalar_tac
  simp [BytesSliceAdvance.Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance,
    not_beyond, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index, h]

theorem advance_failure (self : Slice U8) (count : Usize)
    (h : self.length < count.val) :
    BytesSliceAdvance.Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance self count =
      .fail .panic := by
  have beyond : Slice.len self < count := by scalar_tac
  simp [BytesSliceAdvance.Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance,
    beyond, panic_exact]

/-- Exact result behavior on every input, including out-of-range counts. -/
theorem advance_exact (self : Slice U8) (count : Usize) :
    BytesSliceAdvance.Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance self count =
      if count.val ≤ self.length then .ok (self.drop count) else .fail .panic := by
  split
  · exact advance_success _ _ ‹_›
  · exact advance_failure _ _ (by omega)

theorem advance_bytes (self : Slice U8) (count : Usize)
    (h : count.val ≤ self.length) :
    ∃ after, BytesSliceAdvance.Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance
        self count = .ok after ∧
      after.val = self.val.drop count.val ∧ after.length = self.length - count.val := by
  refine ⟨self.drop count, advance_success self count h, rfl, ?_⟩
  simp [Slice.drop, Slice.length]

theorem advance_all (self : Slice U8) :
    BytesSliceAdvance.Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance self (Slice.len self) =
      .ok ⟨[], by simp⟩ := by
  rw [advance_success self (Slice.len self) (by simp)]
  congr 1
  apply Subtype.ext
  simp [Slice.drop]

end LibSignalReference.Candidate.SliceAdvance
