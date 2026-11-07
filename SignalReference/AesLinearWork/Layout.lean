import AesLinearWork.Reference
import LibSignalReference.Proofs.AesLayoutPermutation

namespace TlsMpc.Signal.AesLinear

open AesLayout

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block_get (o : Aes.Ops B) (input : Nat → Nat → B) (block index : Nat)
    (hi : index < 16) : Aes.get o (blockBytes input block) index = input block index := by
  simp [Aes.get, blockBytes, hi]

theorem mixBytes_eq (o : Aes.Ops B) (input : Nat → Nat → B) (block index : Nat)
    (hi : index < 16) :
    mixBytes o input block index =
      Aes.mixByte o (input block (4 * (index / 4) + index % 4))
        (input block (4 * (index / 4) + (index % 4 + 1) % 4))
        (input block (4 * (index / 4) + (index % 4 + 2) % 4))
        (input block (4 * (index / 4) + (index % 4 + 3) % 4)) := by
  have h0 : 4 * (index / 4) + index % 4 < 16 := by omega
  have h1 : 4 * (index / 4) + (index % 4 + 1) % 4 < 16 := by omega
  have h2 : 4 * (index / 4) + (index % 4 + 2) % 4 < 16 := by omega
  have h3 : 4 * (index / 4) + (index % 4 + 3) % 4 < 16 := by omega
  simp only [mixBytes, Aes.mixColumns, Aes.get, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  congr 1 <;> apply block_get <;> omega

theorem network_w0 (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w0).getLsbD lane =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 0 := by
  simpa only [Words.at] using network_bit input ⟨0,by decide⟩ ⟨lane,hl⟩

theorem network_w0_elem (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w0)[lane] =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 0 := by
  rw [← BitVec.getLsbD_eq_getElem]
  exact network_w0 input lane hl

theorem network_w1 (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w1).getLsbD lane =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 1 := by
  simpa only [Words.at] using network_bit input ⟨1,by decide⟩ ⟨lane,hl⟩

theorem network_w1_elem (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w1)[lane] =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 1 := by
  rw [← BitVec.getLsbD_eq_getElem]
  exact network_w1 input lane hl

theorem network_w2 (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w2).getLsbD lane =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 2 := by
  simpa only [Words.at] using network_bit input ⟨2,by decide⟩ ⟨lane,hl⟩

theorem network_w2_elem (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w2)[lane] =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 2 := by
  rw [← BitVec.getLsbD_eq_getElem]
  exact network_w2 input lane hl

theorem network_w3 (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w3).getLsbD lane =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 3 := by
  simpa only [Words.at] using network_bit input ⟨3,by decide⟩ ⟨lane,hl⟩

theorem network_w3_elem (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w3)[lane] =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 3 := by
  rw [← BitVec.getLsbD_eq_getElem]
  exact network_w3 input lane hl

theorem network_w4 (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w4).getLsbD lane =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 4 := by
  simpa only [Words.at] using network_bit input ⟨4,by decide⟩ ⟨lane,hl⟩

theorem network_w4_elem (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w4)[lane] =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 4 := by
  rw [← BitVec.getLsbD_eq_getElem]
  exact network_w4 input lane hl

theorem network_w5 (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w5).getLsbD lane =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 5 := by
  simpa only [Words.at] using network_bit input ⟨5,by decide⟩ ⟨lane,hl⟩

theorem network_w5_elem (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w5)[lane] =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 5 := by
  rw [← BitVec.getLsbD_eq_getElem]
  exact network_w5 input lane hl

theorem network_w6 (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w6).getLsbD lane =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 6 := by
  simpa only [Words.at] using network_bit input ⟨6,by decide⟩ ⟨lane,hl⟩

theorem network_w6_elem (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w6)[lane] =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 6 := by
  rw [← BitVec.getLsbD_eq_getElem]
  exact network_w6 input lane hl

theorem network_w7 (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w7).getLsbD lane =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 7 := by
  simpa only [Words.at] using network_bit input ⟨7,by decide⟩ ⟨lane,hl⟩

theorem network_w7_elem (input : Nat → Nat → BitVec 8) (lane : Nat) (hl : lane < 64) :
    ((network input).w7)[lane] =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD 7 := by
  rw [← BitVec.getLsbD_eq_getElem]
  exact network_w7 input lane hl


end TlsMpc.Signal.AesLinear
