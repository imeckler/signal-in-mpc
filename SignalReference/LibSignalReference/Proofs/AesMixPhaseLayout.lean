import LibSignalReference.Proofs.AesMixPhaseBits
import LibSignalReference.Proofs.AesShiftBits

namespace TlsMpc.Signal.AesRemainingLinear

open AesLayout
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem mixWords_network_bit (input : Nat → Nat → BitVec 8)
    (phase : Fin 4) (plane : Fin 8) (lane : Fin 64) :
    ((mixWords phase.val (network input)).at plane.val).getLsbD lane.val =
      ((network (phaseBytes Aes.concrete phase.val input)).at plane.val).getLsbD lane.val := by
  rw [mixWords_bit, network_bit]
  simp only [mixBit]
  simp (disch := first | omega | apply laneAfter_lt) only [AesLinear.network_at_bit]
  fin_cases phase <;>
    simp (disch := omega) only [phaseBytes, AesLinear.shiftBytesN, AesLinear.shiftBytes_eq,
      AesLinear.mixBytes_eq, AesLinear.mixByte_bit] <;>
    simp only [Bool.xor_assoc] <;>
    fin_cases lane <;> rfl

theorem mixWords_network (input : Nat → Nat → BitVec 8) (phase : Fin 4) :
    mixWords phase.val (network input) = network (phaseBytes Aes.concrete phase.val input) := by
  apply AesLinear.words_ext
  intro plane
  apply BitVec.eq_of_getLsbD_eq
  intro lane hl
  exact mixWords_network_bit input phase plane ⟨lane,hl⟩

theorem shift_four_network (input : Nat → Nat → BitVec 8) :
    network (AesLinear.shiftBytesN Aes.concrete 4 input) = network input := by
  apply AesLinear.words_ext
  intro plane
  apply BitVec.eq_of_getLsbD_eq
  intro lane hl
  rw [network_bit _ plane ⟨lane,hl⟩, network_bit _ plane ⟨lane,hl⟩]
  simp (disch := omega) only [AesLinear.shiftBytesN, AesLinear.shiftBytes_eq]
  have h : lane ∈ List.range 64 := List.mem_range.mpr hl
  interval_cases lane <;> rfl

/-- The phase changes from k-1 to k while a byte round applies ShiftRows
followed by MixColumns. This is the representation invariant used by the
actual fixslice encryption loop; no same-layout assumption is made. -/
theorem phase_transition_bytes (o : Aes.Ops B) (input : Nat → Nat → B)
    (phase : Fin 3) (block : Nat) (index : Fin 16) :
    phaseBytes o (phase.val + 1) (AesLinear.shiftBytesN o (4 - phase.val) input) block index.val =
      AesLinear.shiftBytesN o (3 - phase.val)
        (AesLinear.mixBytes o (AesLinear.shiftBytes o input)) block index.val := by
  fin_cases phase <;>
    simp (disch := omega) only [phaseBytes, AesLinear.shiftBytesN, AesLinear.shiftBytes_eq,
      AesLinear.mixBytes_eq] <;>
    fin_cases index <;> rfl

theorem round_phase_network (input : Nat → Nat → BitVec 8) (phase : Fin 3) :
    mixWords (phase.val + 1) (network (AesLinear.shiftBytesN Aes.concrete (4 - phase.val) input)) =
      network (AesLinear.shiftBytesN Aes.concrete (3 - phase.val)
        (AesLinear.mixBytes Aes.concrete (AesLinear.shiftBytes Aes.concrete input))) := by
  rw [mixWords_network _ ⟨phase.val + 1, by omega⟩]
  apply AesLinear.words_ext
  intro plane
  apply BitVec.eq_of_getLsbD_eq
  intro lane hl
  rw [network_bit _ plane ⟨lane,hl⟩, network_bit _ plane ⟨lane,hl⟩]
  rw [phase_transition_bytes _ _ phase _ ⟨(lane / 4) % 4 * 4 + lane / 16, by omega⟩]

theorem phaseFastBytes_eq (o : Aes.Ops B) (input : Nat → Nat → B)
    (phase : Fin 4) (block : Nat) (index : Fin 16) :
    phaseFastBytes o phase.val input block index.val = phaseBytes o phase.val input block index.val := by
  fin_cases phase <;>
    simp (disch := omega) only [phaseFastBytes, shiftIndex, phaseBytes, AesLinear.shiftBytesN,
      AesLinear.shiftBytes_eq, AesLinear.mixBytes_eq] <;>
    fin_cases index <;> rfl

theorem fast_network (input : Nat → Nat → BitVec 8) (phase : Fin 4) :
    network (phaseFastBytes Aes.concrete phase.val input) =
      network (phaseBytes Aes.concrete phase.val input) := by
  apply AesLinear.words_ext
  intro plane
  apply BitVec.eq_of_getLsbD_eq
  intro lane hl
  rw [network_bit _ plane ⟨lane,hl⟩, network_bit _ plane ⟨lane,hl⟩]
  rw [phaseFastBytes_eq _ _ phase _ ⟨(lane / 4) % 4 * 4 + lane / 16, by omega⟩]

end TlsMpc.Signal.AesRemainingLinear
