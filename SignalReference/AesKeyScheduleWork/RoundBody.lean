import AesKeyScheduleWork.ArrayHelpers

namespace LibSignalReference.Candidate.AesKeySchedule

open Aeneas Aeneas.Std
open RustCryptoAesKeySchedule

set_option maxHeartbeats 4000000

/-- Proof-only factoring of the translated body's existing borrows and calls.
No Rust source or generated definition is changed by this factoring. -/
def roundBody (words : Array U64 120#usize) (offset round : Usize) :
    Result (ControlFlow (Array U64 120#usize × Usize × Usize) (Array U64 120#usize)) := do
  let w1 ← copyArray words offset
  let offset1 ← offset + 8#usize
  let offset2 ← offset1 + 8#usize
  let w3 ← substituteArray w1 offset1 offset2
  let w4 ← applyWindow w3 offset1 offset2 (fun part => soft.fixslice.add_round_constant_bit part round)
  let rotation1 ← soft.fixslice.ror_distance 1#u32 3#u32
  let w5 ← columnsArray w4 offset1 16#usize rotation1
  let round1 ← round + 1#usize
  if round1 = 7#usize then .ok (.done w5) else
  let w6 ← copyArray w5 offset1
  let offset3 ← offset2 + 8#usize
  let w8 ← substituteArray w6 offset2 offset3
  let rotation2 ← soft.fixslice.ror_distance 0#u32 3#u32
  let w9 ← columnsArray w8 offset2 16#usize rotation2
  .ok (.cont (w9, offset2, round1))

theorem roundBody_eq (words : Array U64 120#usize) (offset round : Usize) :
    soft.fixslice.aes256_key_schedule_loop0.body words offset round = roundBody words offset round := by
  with_unfolding_all simp [soft.fixslice.aes256_key_schedule_loop0.body, roundBody, copyArray, columnsArray,
    substituteArray, applyWindow, Array.to_slice_mut, lift, bind_tc_ok]
  repeat intro
  split <;> simp_all

def RoundPost (before : Array U64 120#usize) (offset round : Usize) :
    ControlFlow (Array U64 120#usize × Usize × Usize) (Array U64 120#usize) → Prop
  | .done after => round.val = 6 ∧ after.val.map UScalar.bv =
      TlsMpc.Signal.AesKeySchedule.expandRound TlsMpc.Signal.AesKeySchedule.concrete round.val
        (before.val.map UScalar.bv)
  | .cont (after, nextOffset, nextRound) => round.val < 6 ∧
      nextOffset.val = offset.val + 16 ∧ nextRound.val = round.val + 1 ∧
      after.val.map UScalar.bv =
        TlsMpc.Signal.AesKeySchedule.expandRound TlsMpc.Signal.AesKeySchedule.concrete round.val
          (before.val.map UScalar.bv)

theorem roundBody_spec (words : Array U64 120#usize) (offset round : Usize)
    (hr : round.val < 7) (ho : offset.val = 8 + 16 * round.val) :
    soft.fixslice.aes256_key_schedule_loop0.body words offset round ⦃ flow => RoundPost words offset round flow ⦄ := by
  rw [roundBody_eq]
  unfold roundBody
  have hrot1 : soft.fixslice.ror_distance 1#u32 3#u32 = .ok 28#u32 := by rfl
  have hrot2 : soft.fixslice.ror_distance 0#u32 3#u32 = .ok 12#u32 := by rfl
  simp only [hrot1, hrot2, bind_tc_ok]
  step*
  · have hr6 : round.val = 6 := by scalar_tac
    simp_all [RoundPost, TlsMpc.Signal.AesKeySchedule.expandRound,
      TlsMpc.Signal.AesKeySchedule.concrete]
  · have hr6 : round.val < 6 := by scalar_tac
    have hrn : round.val ≠ 6 := by omega
    simp_all [RoundPost, TlsMpc.Signal.AesKeySchedule.expandRound,
      TlsMpc.Signal.AesKeySchedule.concrete, Nat.add_assoc]

end LibSignalReference.Candidate.AesKeySchedule
