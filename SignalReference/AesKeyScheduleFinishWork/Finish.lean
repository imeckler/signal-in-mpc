import AesKeyScheduleFinishWork.Phases
import AesKeyScheduleFinishWork.Restoration

namespace LibSignalReference.Candidate.AesKeyScheduleFinish

open Aeneas Aeneas.Std
open RustCryptoAesKeySchedule
open LibSignalReference.Candidate.AesKeySchedule
open TlsMpc.Signal.AesKeySchedule (concrete)

set_option maxHeartbeats 2000000

/-- Exact proof-only factor of the generated entrypoint after its expansion
loop. Every translated call, iterator constructor and mutable write-back is
preserved; this does not replace or modify the generated reference. -/
def finishActual (words : Array U64 120#usize) : Result (Array U64 120#usize) := do
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 8#usize, «end» := 104#usize } 32#usize
  let words1 ← soft.fixslice.aes256_key_schedule_loop1 iter words
  let (part, back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice U64)) words1
      { start := 104#usize, «end» := 112#usize }
  let part1 ← soft.fixslice.inv_shift_rows_1 part
  let words2 := back part1
  soft.fixslice.aes256_key_schedule_loop2
    { start := 1#usize, «end» := 15#usize } words2

theorem phase_start :
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 8#usize, «end» := 104#usize } 32#usize =
        .ok (phaseIterator 8#usize) := by
  simp [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default, phaseIterator]

theorem finishActual_factor (words : Array U64 120#usize) :
    finishActual words = (do
      let words1 ← soft.fixslice.aes256_key_schedule_loop1 (phaseIterator 8#usize) words
      let words2 ← applyWindow words1 104#usize 112#usize soft.fixslice.inv_shift_rows_1
      soft.fixslice.aes256_key_schedule_loop2 ⟨1#usize,15#usize⟩ words2) := by
  with_unfolding_all simp [finishActual, phase_start, applyWindow]

/-- The complete translated postprocessing succeeds on every 120-word secret
array and has exactly the pure operation used by the verified MPC compiler. -/
theorem finishActual_spec (words : Array U64 120#usize) :
    ∃ result, finishActual words = .ok result ∧ result.val.map UScalar.bv =
      TlsMpc.Signal.AesKeySchedule.finish concrete (words.val.map UScalar.bv) := by
  obtain ⟨words1, h1, hv1⟩ := phase_loop words
  obtain ⟨words2, h2, hv2⟩ := inverse1Array_spec words1 104#usize 112#usize (by decide) (by decide)
  obtain ⟨words3, h3, hv3⟩ := restoration_loop words2 1#usize (by decide)
  refine ⟨words3, ?_, ?_⟩
  · rw [finishActual_factor]
    simp only [h1, h2, h3, bind_tc_ok]
  · simpa [TlsMpc.Signal.AesKeySchedule.finish, hv1, hv2] using hv3

end LibSignalReference.Candidate.AesKeyScheduleFinish
