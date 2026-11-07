import AesKeyScheduleWork.ColumnsBridge
import TlsMpc.Signal.AesKeySchedule

namespace LibSignalReference.Candidate.AesKeySchedule

open Aeneas Aeneas.Std
open TlsMpc.Signal.AesKeySchedule (window)

set_option maxHeartbeats 2000000

def take8 (words : Array U64 size) (offset : Nat) : Slice U64 :=
  ⟨(words.val.drop offset).take 8, by
    have hs := words.property
    simp only [List.length_take, List.length_drop]
    scalar_tac⟩

def replace (words : Array U64 size) (offset : Nat) (part : Slice U64) : Array U64 size :=
  ⟨words.val.setSlice! offset part.val, by simp⟩

theorem take8_length (words : Array U64 size) (offset : Nat) (hs : offset + 8 ≤ size.val) :
    (take8 words offset).length = 8 := by
  simp [take8, Slice.length]
  scalar_tac

theorem borrow_window (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val) :
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice U64)) words ⟨start,finish⟩ =
      .ok (take8 words start.val, replace words start.val) := by
  have hf : start ≤ finish := by scalar_tac
  have ht : start.val + 8 ≤ size.val := by omega
  simp [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut, hf, ht,
    Array.to_slice, take8, List.slice, he, Array.from_slice]
  rfl

theorem replace_val (words : Array U64 size) (offset : Nat) (part : Slice U64)
    (hl : part.length = 8) (hs : offset + 8 ≤ size.val) :
    (replace words offset part).val =
      words.val.take offset ++ part.val ++ words.val.drop (offset + 8) := by
  have hpl : part.val.length = 8 := hl
  have hb : 8 ≤ words.val.length - offset := by simp; omega
  simp only [replace, List.setSlice!, hpl, Nat.min_eq_left hb,
    List.take_of_length_le (by omega : part.val.length ≤ 8)]

theorem replace_get (words : Array U64 size) (offset : Nat) (part : Slice U64)
    (hl : part.length = 8) (hs : offset + 8 ≤ size.val) :
    take8 (replace words offset part) offset = part := by
  apply Subtype.ext
  have hpl : part.val.length = 8 := hl
  have ho : offset ≤ words.val.length := by simp; omega
  simp only [take8, replace_val words offset part hl hs]
  simp [List.length_take, Nat.min_eq_left (by omega : offset ≤ size.val), hpl]

theorem replace_twice (words : Array U64 size) (offset : Nat) (first second : Slice U64)
    (hf : first.length = 8) (hs' : second.length = 8) (hs : offset + 8 ≤ size.val) :
    replace (replace words offset first) offset second = replace words offset second := by
  apply Subtype.ext
  rw [replace_val _ _ second hs' hs, replace_val words offset first hf hs,
    replace_val words offset second hs' hs]
  have ho : offset ≤ words.val.length := by simp; omega
  have hfl : first.val.length = 8 := hf
  simp [List.drop_append, List.length_take, Nat.min_eq_left (by omega : offset ≤ size.val), hfl]

theorem replace_bv (words : Array U64 size) (offset : Nat) (part : Slice U64)
    (hl : part.length = 8) (hs : offset + 8 ≤ size.val)
    (f : List (BitVec 64) → List (BitVec 64))
    (hv : part.val.map UScalar.bv = f ((take8 words offset).val.map UScalar.bv)) :
    (replace words offset part).val.map UScalar.bv = window f offset (words.val.map UScalar.bv) := by
  rw [replace_val words offset part hl hs]
  simp only [List.map_append, hv, window, take8, List.map_take, List.map_drop]

def applyWindow (words : Array U64 size) (start finish : Usize)
    (operation : Slice U64 → Result (Slice U64)) : Result (Array U64 size) := do
  let (part, back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U64)) words ⟨start,finish⟩
  let result ← operation part
  .ok (back result)

theorem applyWindow_spec (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val)
    (operation : Slice U64 → Result (Slice U64)) (f : List (BitVec 64) → List (BitVec 64))
    (hop : ∀ part : Slice U64, part.length = 8 → ∃ result,
      operation part = .ok result ∧ result.length = 8 ∧
        result.val.map UScalar.bv = f (part.val.map UScalar.bv)) :
    ∃ result, applyWindow words start finish operation = .ok result ∧
      result.val.map UScalar.bv = window f start.val (words.val.map UScalar.bv) := by
  have hbound : start.val + 8 ≤ size.val := by omega
  obtain ⟨result, hr, hl, hv⟩ := hop (take8 words start.val) (take8_length words start.val hbound)
  refine ⟨replace words start.val result, ?_, replace_bv words start.val result hl hbound f hv⟩
  with_unfolding_all simp [applyWindow, borrow_window words start finish he hs, hr]

/-- Reborrowing the same valid eight-word window preserves its write-back.
This justifies joining the actual separate SubBytes and omitted-NOT calls. -/
theorem applyWindow_compose (words : Array U64 size) (start finish : Usize)
    (he : finish.val = start.val + 8) (hs : finish.val ≤ size.val)
    (first second : Slice U64 → Result (Slice U64))
    (hf : ∀ part : Slice U64, part.length = 8 → ∃ result, first part = .ok result ∧ result.length = 8)
    (hs' : ∀ part : Slice U64, part.length = 8 → ∃ result, second part = .ok result ∧ result.length = 8) :
    (do let intermediate ← applyWindow words start finish first
        applyWindow intermediate start finish second) =
      applyWindow words start finish (fun part => do let intermediate ← first part; second intermediate) := by
  have hb : start.val + 8 ≤ size.val := by omega
  obtain ⟨middle, hm, hml⟩ := hf (take8 words start.val) (take8_length words start.val hb)
  obtain ⟨last, hl, hll⟩ := hs' middle hml
  with_unfolding_all simp [applyWindow, borrow_window _ start finish he hs, hm,
    replace_get words start.val middle hml hb, hl, replace_twice words start.val middle last hml hll hb]

end LibSignalReference.Candidate.AesKeySchedule
