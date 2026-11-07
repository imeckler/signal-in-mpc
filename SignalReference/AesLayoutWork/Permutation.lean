import Aeneas
import Mathlib.Tactic.IntervalCases
import AesLayoutWork.Network

namespace TlsMpc.Signal.AesLayout

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem transpose_bit (words : Words (BitVec 64)) (plane : Fin 8) (lane : Fin 64) :
    ((transpose words).at plane.val).getLsbD lane.val =
      (words.at (lane.val % 8)).getLsbD (lane.val / 8 * 8 + plane.val) := by
  fin_cases plane <;> fin_cases lane <;>
    simp [transpose, deltaSwap, Words.at, Bool.xor_comm, Bool.xor_left_comm]

theorem read_bit (input : Nat → BitVec 8) (bit : Nat) (hbit : bit < 64) :
    (readReordered input).getLsbD bit =
      (input (bit / 16 + ((bit / 8) % 2) * 8)).getLsbD (bit % 8) := by
  interval_cases bit <;> simp [readReordered]

theorem network_bit (input : Nat → Nat → BitVec 8) (plane : Fin 8) (lane : Fin 64) :
    ((network input).at plane.val).getLsbD lane.val =
      (input (lane.val % 4) ((lane.val / 4) % 4 * 4 + lane.val / 16)).getLsbD plane.val := by
  rw [network, transpose_bit]
  fin_cases plane <;> fin_cases lane <;>
    simp only [prepare, Words.at] <;>
    rw [read_bit _ _ (by decide)] <;> rfl

end TlsMpc.Signal.AesLayout
