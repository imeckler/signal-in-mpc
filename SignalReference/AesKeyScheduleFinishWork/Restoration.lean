import AesKeyScheduleFinishWork.Windows

namespace LibSignalReference.Candidate.AesKeyScheduleFinish

open Aeneas Aeneas.Std
open RustCryptoAesKeySchedule
open LibSignalReference.Candidate.AesKeySchedule
open TlsMpc.Signal.AesKeySchedule (concrete window restoreNots restoreRounds)

set_option maxHeartbeats 2000000

def nextRound (index : Usize) (hi : index.val < 15) : Usize :=
  Usize.ofNatCore (index.val + 1) (by scalar_tac)

theorem range_next (index : Usize) (hi : index.val < 15) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨index,15#usize⟩ =
      .ok (some index, ⟨nextRound index hi,15#usize⟩) := by
  have hb : index.val < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hi, hb, nextRound]
  rfl

theorem range_done :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨15#usize,15#usize⟩ =
      .ok (none, ⟨15#usize,15#usize⟩) := by rfl

/-- A proof-only factoring of the actual checked arithmetic and window call. -/
def restoreArrayRound (words : Array U64 120#usize) (round : Usize) :
    Result (Array U64 120#usize) := do
  let offset ← round * 8#usize
  let finish ← offset + 8#usize
  applyWindow words offset finish soft.fixslice.sub_bytes_nots

theorem restoreArrayRound_spec (words : Array U64 120#usize) (round : Usize)
    (hr : round.val < 15) :
    restoreArrayRound words round ⦃ result =>
      result.val.map UScalar.bv = window (restoreNots concrete 0) (round.val * 8)
        (words.val.map UScalar.bv) ⦄ := by
  unfold restoreArrayRound
  step*

theorem restore_body (words : Array U64 120#usize) (round : Usize)
    (hr : round.val < 15) :
    ∃ result,
      soft.fixslice.aes256_key_schedule_loop2.body ⟨round,15#usize⟩ words =
        .ok (.cont (⟨nextRound round hr,15#usize⟩,result)) ∧
      result.val.map UScalar.bv = window (restoreNots concrete 0) (round.val * 8)
        (words.val.map UScalar.bv) := by
  obtain ⟨result, hresult, hv⟩ := WP.spec_imp_exists (restoreArrayRound_spec words round hr)
  refine ⟨result, ?_, hv⟩
  have hfactor : soft.fixslice.aes256_key_schedule_loop2.body ⟨round,15#usize⟩ words =
      (do let value ← restoreArrayRound words round
          .ok (.cont (⟨nextRound round hr,15#usize⟩,value))) := by
    rw [soft.fixslice.aes256_key_schedule_loop2.body, range_next round hr]
    with_unfolding_all simp [restoreArrayRound, applyWindow]
  rw [hfactor, hresult]
  rfl

theorem restoration_loop (words : Array U64 120#usize) (round : Usize)
    (hr : round.val ≤ 15) :
    ∃ result, soft.fixslice.aes256_key_schedule_loop2 ⟨round,15#usize⟩ words = .ok result ∧
      result.val.map UScalar.bv = restoreRounds concrete (15 - round.val) round.val
        (words.val.map UScalar.bv) := by
  generalize hn : 15 - round.val = count
  induction count generalizing words round with
  | zero =>
    have hr15 : round = 15#usize := by scalar_tac
    subst round
    refine ⟨words, ?_, rfl⟩
    unfold soft.fixslice.aes256_key_schedule_loop2
    rw [loop]
    simp [soft.fixslice.aes256_key_schedule_loop2.body, range_done]
  | succ count ih =>
    have hr' : round.val < 15 := by omega
    obtain ⟨after, hafter, hvalue⟩ := restore_body words round hr'
    have hrnext : (nextRound round hr').val ≤ 15 := by simp only [nextRound]; scalar_tac
    have hcount : 15 - (nextRound round hr').val = count := by simp only [nextRound]; scalar_tac
    obtain ⟨result, hresult, hv⟩ := ih after (nextRound round hr') hrnext hcount
    refine ⟨result, ?_, ?_⟩
    · unfold soft.fixslice.aes256_key_schedule_loop2
      rw [loop]
      dsimp only
      rw [hafter]
      simpa only [soft.fixslice.aes256_key_schedule_loop2] using hresult
    · simpa only [restoreRounds, show (nextRound round hr').val = round.val + 1 from rfl,
        hvalue] using hv

end LibSignalReference.Candidate.AesKeyScheduleFinish
