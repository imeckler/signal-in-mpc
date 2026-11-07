import LibSignalReference.Proofs.AesShiftReference
import LibSignalReference.Proofs.AesLinearProofs
import LibSignalReference.Proofs.AesLayoutPermutation

namespace TlsMpc.Signal.AesLinear

open AesLayout
set_option maxHeartbeats 4000000

def shiftedLane (times lane : Nat) : Nat :=
  lane / 16 * 16 + ((lane / 4 % 4 + times * (lane / 16)) % 4) * 4 + lane % 4

theorem shiftedLane_lt (times lane : Nat) (hl : lane < 64) : shiftedLane times lane < 64 := by
  unfold shiftedLane
  omega

theorem xor_cancel_outer : ∀ a b : Bool, (a ^^ (b ^^ a)) = b := by decide +kernel

theorem shiftWord1_bit (word : BitVec 64) (lane : Fin 64) :
    (shiftWord1 word).getLsbD lane.val = word.getLsbD (shiftedLane 1 lane.val) := by
  fin_cases lane <;> simp [shiftWord1, deltaWord, shiftedLane, xor_cancel_outer]

theorem shiftWord2_bit (word : BitVec 64) (lane : Fin 64) :
    (shiftWord2 word).getLsbD lane.val = word.getLsbD (shiftedLane 2 lane.val) := by
  fin_cases lane <;> simp [shiftWord2, deltaWord, shiftedLane, xor_cancel_outer]

theorem shiftWord3_bit (word : BitVec 64) (lane : Fin 64) :
    (shiftWord3 word).getLsbD lane.val = word.getLsbD (shiftedLane 3 lane.val) := by
  fin_cases lane <;> simp [shiftWord3, deltaWord, shiftedLane, xor_cancel_outer]

theorem mapWords_at (f : W → W') (words : Words W) (plane : Fin 8) :
    (mapWords f words).at plane.val = f (words.at plane.val) := by
  fin_cases plane <;> rfl

theorem shiftBytes_eq (o : Aes.Ops B) (input : Nat → Nat → B) (block index : Nat)
    (hi : index < 16) :
    shiftBytes o input block index = input block (4 * ((index / 4 + index % 4) % 4) + index % 4) := by
  have hb : 4 * ((index / 4 + index % 4) % 4) + index % 4 < 16 := by omega
  simp only [shiftBytes, Aes.shiftRows, Aes.get, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]
  exact block_get o input block _ hb

theorem shift1_network_bit (input : Nat → Nat → BitVec 8) (plane : Fin 8) (lane : Fin 64) :
    ((mapWords shiftWord1 (network input)).at plane.val).getLsbD lane.val =
      ((network (shiftBytes Aes.concrete input)).at plane.val).getLsbD lane.val := by
  rw [mapWords_at, shiftWord1_bit, network_bit input plane
    ⟨shiftedLane 1 lane.val, shiftedLane_lt 1 lane.val lane.isLt⟩, network_bit]
  rw [shiftBytes_eq _ _ _ _ (by omega)]
  fin_cases lane <;> rfl

theorem shift1_network (input : Nat → Nat → BitVec 8) :
    mapWords shiftWord1 (network input) = network (shiftBytes Aes.concrete input) := by
  apply words_ext
  intro plane
  apply BitVec.eq_of_getLsbD_eq
  intro lane hl
  exact shift1_network_bit input plane ⟨lane,hl⟩

theorem shift2_network_bit (input : Nat → Nat → BitVec 8) (plane : Fin 8) (lane : Fin 64) :
    ((mapWords shiftWord2 (network input)).at plane.val).getLsbD lane.val =
      ((network (shiftBytesN Aes.concrete 2 input)).at plane.val).getLsbD lane.val := by
  rw [mapWords_at, shiftWord2_bit, network_bit input plane
    ⟨shiftedLane 2 lane.val, shiftedLane_lt 2 lane.val lane.isLt⟩, network_bit]
  simp only [shiftBytesN]
  rw [shiftBytes_eq _ _ _ _ (by omega), shiftBytes_eq _ _ _ _ (by omega)]
  fin_cases lane <;> rfl

theorem shift2_network (input : Nat → Nat → BitVec 8) :
    mapWords shiftWord2 (network input) = network (shiftBytesN Aes.concrete 2 input) := by
  apply words_ext
  intro plane
  apply BitVec.eq_of_getLsbD_eq
  intro lane hl
  exact shift2_network_bit input plane ⟨lane,hl⟩

theorem shift3_network_bit (input : Nat → Nat → BitVec 8) (plane : Fin 8) (lane : Fin 64) :
    ((mapWords shiftWord3 (network input)).at plane.val).getLsbD lane.val =
      ((network (shiftBytesN Aes.concrete 3 input)).at plane.val).getLsbD lane.val := by
  rw [mapWords_at, shiftWord3_bit, network_bit input plane
    ⟨shiftedLane 3 lane.val, shiftedLane_lt 3 lane.val lane.isLt⟩, network_bit]
  simp only [shiftBytesN]
  rw [shiftBytes_eq _ _ _ _ (by omega), shiftBytes_eq _ _ _ _ (by omega),
    shiftBytes_eq _ _ _ _ (by omega)]
  fin_cases lane <;> rfl

theorem shift3_network (input : Nat → Nat → BitVec 8) :
    mapWords shiftWord3 (network input) = network (shiftBytesN Aes.concrete 3 input) := by
  apply words_ext
  intro plane
  apply BitVec.eq_of_getLsbD_eq
  intro lane hl
  exact shift3_network_bit input plane ⟨lane,hl⟩

end TlsMpc.Signal.AesLinear
