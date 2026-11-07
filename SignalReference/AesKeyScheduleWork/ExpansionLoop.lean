import AesKeyScheduleWork.RoundBody

namespace LibSignalReference.Candidate.AesKeySchedule

open Aeneas Aeneas.Std
open RustCryptoAesKeySchedule
open TlsMpc.Signal.AesKeySchedule (expandRounds concrete)

set_option maxHeartbeats 2000000

/-- All seven actual expansion iterations, including their checked arithmetic
and early final iteration, equal the compiled pure recurrence. -/
theorem expansion_loop (words : Array U64 120#usize) (offset round : Usize)
    (hr : round.val < 7) (ho : offset.val = 8 + 16 * round.val) :
    ∃ result, soft.fixslice.aes256_key_schedule_loop0 words offset round = .ok result ∧
      result.val.map UScalar.bv = expandRounds concrete (7 - round.val) round.val
        (words.val.map UScalar.bv) := by
  generalize hn : 7 - round.val = count
  induction count generalizing words offset round with
  | zero => omega
  | succ count ih =>
    obtain ⟨flow, hflow, hpost⟩ := WP.spec_imp_exists (roundBody_spec words offset round hr ho)
    cases flow with
    | done after =>
      obtain ⟨hr6, hv⟩ := hpost
      have hc : count = 0 := by omega
      subst count
      refine ⟨after, ?_, ?_⟩
      · unfold soft.fixslice.aes256_key_schedule_loop0
        rw [loop]
        dsimp only
        rw [hflow]
      · simpa only [expandRounds] using hv
    | cont state =>
      rcases state with ⟨after, nextOffset, nextRound⟩
      obtain ⟨hr6, hnOffset, hnRound, hv⟩ := hpost
      have hr' : nextRound.val < 7 := by omega
      have ho' : nextOffset.val = 8 + 16 * nextRound.val := by omega
      have hc : 7 - nextRound.val = count := by omega
      obtain ⟨result, hresult, hvalue⟩ := ih after nextOffset nextRound hr' ho' hc
      refine ⟨result, ?_, ?_⟩
      · unfold soft.fixslice.aes256_key_schedule_loop0
        rw [loop]
        dsimp only
        rw [hflow]
        simpa only [soft.fixslice.aes256_key_schedule_loop0] using hresult
      · simpa only [expandRounds, hnRound, hv] using hvalue

end LibSignalReference.Candidate.AesKeySchedule
