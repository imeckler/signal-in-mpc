import LibSignalReference.Proofs.AesLinearBits

namespace TlsMpc.Signal.AesLinear
open AesLayout
set_option maxHeartbeats 200000

theorem mixWords_bit (words : Words (BitVec 64)) (plane : Fin 8) (lane : Fin 64) :
    ((mixWords words).at plane.val).getLsbD lane.val =
      mixBit (fun p l => (words.at p).getLsbD l) plane.val lane.val := by
  have h48 : ((lane.val + 32) % 64 + 16) % 64 = (lane.val + 48) % 64 := by omega
  fin_cases plane <;>
    simp (disch := omega) only [mixWords, Words.at, BitVec.getLsbD_xor, rotate_bit] <;>
    simp [mixBit, feedback, Words.at, h48]

theorem xor_permute5 : ∀ a b c d e : Bool,
    (a ^^ (b ^^ (c ^^ (d ^^ e)))) = (c ^^ (a ^^ (b ^^ (d ^^ e)))) := by decide +kernel

theorem xor_permute7 : ∀ a b c d e f g : Bool,
    (a ^^ (b ^^ (c ^^ (d ^^ (e ^^ (f ^^ g)))))) =
      (e ^^ (a ^^ (c ^^ (b ^^ (d ^^ (f ^^ g)))))) := by decide +kernel

theorem xtime_bit (byte : BitVec 8) (plane : Fin 8) :
    (Aes.xtimeValue byte).getLsbD plane.val =
      ((if plane.val = 0 then false else byte.getLsbD (plane.val - 1)) ^^
        (if feedback plane.val then byte.getLsbD 7 else false)) := by
  fin_cases plane <;>
    simp only [Aes.xtimeValue, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft',
      BitVec.getLsbD_and, BitVec.getLsbD_replicate, BitVec.getLsbD_extractLsb'] <;>
    simp [feedback]

theorem mixByte_bit (a b c d : BitVec 8) (plane : Fin 8) :
    (Aes.mixByte Aes.concrete a b c d).getLsbD plane.val =
      (b.getLsbD plane.val ^^
        (if plane.val = 0 then false else a.getLsbD (plane.val - 1) ^^ b.getLsbD (plane.val - 1)) ^^
        (if feedback plane.val then a.getLsbD 7 ^^ b.getLsbD 7 else false) ^^
        c.getLsbD plane.val ^^ d.getLsbD plane.val) := by
  simp only [Aes.mixByte, Aes.concrete, BitVec.getLsbD_xor]
  rw [xtime_bit a plane, xtime_bit b plane]
  by_cases hp : plane.val = 0
  · have hf : feedback plane.val = true := by simp [feedback, hp]
    rw [hf]
    simp only [hp, ↓reduceIte, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]
    exact xor_permute5 _ _ _ _ _
  · by_cases hf : feedback plane.val = true
    · simp only [hp, hf, ↓reduceIte, Bool.xor_assoc]
      exact xor_permute7 _ _ _ _ _ _ _
    · have hfalse : feedback plane.val = false := Bool.eq_false_iff.mpr hf
      rw [hfalse]
      simp only [hp, Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.xor_assoc]
      exact xor_permute5 _ _ _ _ _

end TlsMpc.Signal.AesLinear
