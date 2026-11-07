import AesLinearWork.BitFormula

namespace TlsMpc.Signal.AesLinear

open AesLayout
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem network_at_bit (input : Nat → Nat → BitVec 8) (plane lane : Nat)
    (hp : plane < 8) (hl : lane < 64) :
    ((network input).at plane).getLsbD lane =
      (input (lane % 4) ((lane / 4) % 4 * 4 + lane / 16)).getLsbD plane := by
  exact network_bit input ⟨plane,hp⟩ ⟨lane,hl⟩

theorem mixWords_network_bit (input : Nat → Nat → BitVec 8) (plane : Fin 8) (lane : Fin 64) :
    ((mixWords (network input)).at plane.val).getLsbD lane.val =
      ((network (mixBytes Aes.concrete input)).at plane.val).getLsbD lane.val := by
  rw [mixWords_bit, network_bit]
  rw [mixBytes_eq _ _ _ _ (by omega), mixByte_bit]
  simp only [mixBit]
  simp (disch := omega) only [network_at_bit]
  simp only [Bool.xor_assoc]
  fin_cases lane <;> rfl

theorem words_ext {a b : Words W} (h : ∀ plane : Fin 8, a.at plane.val = b.at plane.val) : a = b := by
  cases a
  cases b
  have h0 := h ⟨0,by decide⟩
  have h1 := h ⟨1,by decide⟩
  have h2 := h ⟨2,by decide⟩
  have h3 := h ⟨3,by decide⟩
  have h4 := h ⟨4,by decide⟩
  have h5 := h ⟨5,by decide⟩
  have h6 := h ⟨6,by decide⟩
  have h7 := h ⟨7,by decide⟩
  simp only [Words.at] at h0 h1 h2 h3 h4 h5 h6 h7
  cases h0; cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7
  rfl

theorem mixWords_network (input : Nat → Nat → BitVec 8) :
    mixWords (network input) = network (mixBytes Aes.concrete input) := by
  apply words_ext
  intro plane
  apply BitVec.eq_of_getLsbD_eq
  intro lane hl
  exact mixWords_network_bit input plane ⟨lane,hl⟩

end TlsMpc.Signal.AesLinear
