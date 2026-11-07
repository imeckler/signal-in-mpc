import AesKeyScheduleFinishWork.Windows

namespace LibSignalReference.Candidate.AesKeyScheduleFinish

open Aeneas Aeneas.Std
open RustCryptoAesKeySchedule
open LibSignalReference.Candidate.AesKeySchedule
open TlsMpc.Signal.AesKeySchedule (concrete phaseGroup)

set_option maxHeartbeats 2000000

abbrev PhaseIterator := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

def phaseIterator (offset : Usize) : PhaseIterator := ⟨⟨offset,104#usize⟩,32#usize⟩

def phaseNext (iter : PhaseIterator) : Result (Option Usize × PhaseIterator) :=
  core.iter.adapters.step_by.IteratorStepBy.next
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter

theorem range104_next (index : Usize) (hi : index.val < 104) :
    ∃ next, core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨index,104#usize⟩ =
      .ok (some index, ⟨next,104#usize⟩) ∧ next.val = index.val + 1 := by
  let next : Usize := Usize.ofNatCore (index.val + 1) (by scalar_tac)
  refine ⟨next, ?_, rfl⟩
  have hb : index.val < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hi, hb, next]
  rfl

theorem skipRange104 (count : Nat) (index : Usize) (hi : index.val + count ≤ 104) :
    ∃ next, core.iter.adapters.step_by.skipN
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        ⟨index,104#usize⟩ count = .ok ⟨next,104#usize⟩ ∧ next.val = index.val + count := by
  induction count generalizing index with
  | zero => exact ⟨index, rfl, by omega⟩
  | succ count ih =>
    obtain ⟨next, hn, hv⟩ := range104_next index (by omega)
    obtain ⟨last, hl, hvlast⟩ := ih next (by omega)
    refine ⟨last, ?_, by omega⟩
    simp only [core.iter.adapters.step_by.skipN, core.iter.traits.iterator.IteratorRange]
    rw [hn]
    simpa only [bind_tc_ok] using hl

theorem phaseNext_spec (index : Usize) (hi : index.val + 32 ≤ 104) :
    ∃ next, phaseNext (phaseIterator index) = .ok (some index,phaseIterator next) ∧
      next.val = index.val + 32 := by
  obtain ⟨first, hf, hvf⟩ := range104_next index (by omega)
  obtain ⟨last, hl, hvl⟩ := skipRange104 31 first (by omega)
  refine ⟨last, ?_, by omega⟩
  simp only [phaseNext, phaseIterator, core.iter.adapters.step_by.IteratorStepBy.next,
    core.iter.traits.iterator.IteratorRange]
  rw [hf]
  have hcount : (32#usize).val - 1 = 31 := by decide
  simp only [bind_tc_ok, hcount, hl]

theorem phase_next8 : phaseNext (phaseIterator 8#usize) =
    .ok (some 8#usize, phaseIterator 40#usize) := by
  obtain ⟨next, hn, hv⟩ := phaseNext_spec 8#usize (by decide)
  have he : next = 40#usize := by scalar_tac
  simpa only [he] using hn

theorem phase_next40 : phaseNext (phaseIterator 40#usize) =
    .ok (some 40#usize, phaseIterator 72#usize) := by
  obtain ⟨next, hn, hv⟩ := phaseNext_spec 40#usize (by decide)
  have he : next = 72#usize := by scalar_tac
  simpa only [he] using hn

theorem phase_next72 : phaseNext (phaseIterator 72#usize) =
    .ok (some 72#usize, phaseIterator 104#usize) := by
  obtain ⟨next, hn, hv⟩ := phaseNext_spec 72#usize (by decide)
  have he : next = 104#usize := by scalar_tac
  simpa only [he] using hn

theorem phase_nextDone : phaseNext (phaseIterator 104#usize) =
    .ok (none, phaseIterator 104#usize) := by rfl

/-- Exact factoring of the three actual checked borrows and inverse shifts. -/
def phaseArray (words : Array U64 120#usize) (offset : Usize) :
    Result (Array U64 120#usize) := do
  let offset1 ← offset + 8#usize
  let words1 ← applyWindow words offset offset1 soft.fixslice.inv_shift_rows_1
  let offset2 ← offset + 16#usize
  let words2 ← applyWindow words1 offset1 offset2 soft.fixslice.inv_shift_rows_2
  let offset3 ← offset + 24#usize
  applyWindow words2 offset2 offset3 soft.fixslice.inv_shift_rows_3

theorem phaseArray_spec (words : Array U64 120#usize) (offset : Usize)
    (ho : offset.val + 24 ≤ 120) :
    phaseArray words offset ⦃ result => result.val.map UScalar.bv =
      phaseGroup concrete offset.val (words.val.map UScalar.bv) ⦄ := by
  unfold phaseArray
  step*
  simp_all only [phaseGroup]

theorem phase_body (words : Array U64 120#usize) (iter next : PhaseIterator) (offset : Usize)
    (hn : phaseNext iter = .ok (some offset,next)) (ho : offset.val + 24 ≤ 120) :
    ∃ result, soft.fixslice.aes256_key_schedule_loop1.body iter words =
        .ok (.cont (next,result)) ∧
      result.val.map UScalar.bv = phaseGroup concrete offset.val (words.val.map UScalar.bv) := by
  obtain ⟨result, hresult, hv⟩ := WP.spec_imp_exists (phaseArray_spec words offset ho)
  refine ⟨result, ?_, hv⟩
  have hfactor : soft.fixslice.aes256_key_schedule_loop1.body iter words =
      (do let value ← phaseArray words offset
          .ok (.cont (next,value))) := by
    rw [soft.fixslice.aes256_key_schedule_loop1.body, show
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
          .ok (some offset,next) from hn]
    with_unfolding_all simp [phaseArray, applyWindow]
  rw [hfactor, hresult]
  rfl

theorem phase_loop_step (words : Array U64 120#usize) (iter next : PhaseIterator) (offset : Usize)
    (hn : phaseNext iter = .ok (some offset,next)) (ho : offset.val + 24 ≤ 120) :
    ∃ result, soft.fixslice.aes256_key_schedule_loop1 iter words =
        soft.fixslice.aes256_key_schedule_loop1 next result ∧
      result.val.map UScalar.bv = phaseGroup concrete offset.val (words.val.map UScalar.bv) := by
  obtain ⟨result, hresult, hv⟩ := phase_body words iter next offset hn ho
  refine ⟨result, ?_, hv⟩
  unfold soft.fixslice.aes256_key_schedule_loop1
  rw [loop]
  dsimp only
  rw [hresult]

theorem phase_loop_done (words : Array U64 120#usize) :
    soft.fixslice.aes256_key_schedule_loop1 (phaseIterator 104#usize) words = .ok words := by
  unfold soft.fixslice.aes256_key_schedule_loop1
  rw [loop]
  dsimp only
  rw [soft.fixslice.aes256_key_schedule_loop1.body, show
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) (phaseIterator 104#usize) =
        .ok (none,phaseIterator 104#usize) from phase_nextDone]
  rfl

theorem phase_loop (words : Array U64 120#usize) :
    ∃ result, soft.fixslice.aes256_key_schedule_loop1 (phaseIterator 8#usize) words = .ok result ∧
      result.val.map UScalar.bv = phaseGroup concrete 72
        (phaseGroup concrete 40 (phaseGroup concrete 8 (words.val.map UScalar.bv))) := by
  obtain ⟨words1, h1, hv1⟩ := phase_loop_step words _ _ _ phase_next8 (by decide)
  obtain ⟨words2, h2, hv2⟩ := phase_loop_step words1 _ _ _ phase_next40 (by decide)
  obtain ⟨words3, h3, hv3⟩ := phase_loop_step words2 _ _ _ phase_next72 (by decide)
  refine ⟨words3, ?_, ?_⟩
  · rw [h1, h2, h3, phase_loop_done]
  · simpa [hv1, hv2] using hv3

end LibSignalReference.Candidate.AesKeyScheduleFinish
