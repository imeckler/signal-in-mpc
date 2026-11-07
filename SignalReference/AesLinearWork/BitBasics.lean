import AesLinearWork.Layout

namespace TlsMpc.Signal.AesLinear

open AesLayout
set_option maxHeartbeats 200000

def feedback (plane : Nat) : Bool := plane == 0 || plane == 1 || plane == 3 || plane == 4

def mixBit (wire : Nat → Nat → Bool) (plane lane : Nat) : Bool :=
  wire plane ((lane + 16) % 64) ^^
    (if plane = 0 then false else wire (plane - 1) lane ^^ wire (plane - 1) ((lane + 16) % 64)) ^^
    (if feedback plane then wire 7 lane ^^ wire 7 ((lane + 16) % 64) else false) ^^
    (wire plane ((lane + 32) % 64) ^^ wire plane ((lane + 48) % 64))

theorem rotate_bit (word : BitVec 64) (shift lane : Nat) (hs : shift < 64) (hl : lane < 64) :
    (word.rotateRight shift).getLsbD lane = word.getLsbD ((lane + shift) % 64) := by
  rw [BitVec.getLsbD_rotateRight_of_lt hs]
  by_cases h : lane < 64 - shift
  · rw [Nat.mod_eq_of_lt (by omega : lane + shift < 64)]
    simp [h, Nat.add_comm]
  · have hm : (lane + shift) % 64 = lane - (64 - shift) := by omega
    simp [h, hl, hm]


end TlsMpc.Signal.AesLinear
