import LibSignalReference.Generated.AesMixPhases.Funs
import TlsMpc.Signal.AesMixPhases
import LibSignalReference.Proofs.AesLinearReference

namespace LibSignalReference.Proofs.AesMixPhases

open Aeneas Aeneas.Std TlsMpc.Signal.AesLayout TlsMpc.Signal.AesRemainingLinear
open LibSignalReference.Proofs.AesLinear
set_option maxHeartbeats 4000000

theorem rotate_first1 (word : U64) :
    RustCryptoAesRemainingLinear.soft.fixslice.rotate_rows_and_columns_1_1 word =
      .ok ⟨rotateFirst 1 word.bv⟩ := by rfl

theorem rotate_first2 (word : U64) :
    RustCryptoAesRemainingLinear.soft.fixslice.rotate_rows_and_columns_1_2 word =
      .ok ⟨rotateFirst 2 word.bv⟩ := by rfl

theorem rotate_first3 (word : U64) :
    RustCryptoAesRemainingLinear.soft.fixslice.rotate_rows_and_columns_1_3 word =
      .ok ⟨rotateFirst 3 word.bv⟩ := by rfl

theorem rotate_second1 (word : U64) :
    RustCryptoAesRemainingLinear.soft.fixslice.rotate_rows_and_columns_2_2 word =
      .ok ⟨rotateSecond 1 word.bv⟩ := by rfl

theorem rotate_second2 (word : U64) :
    RustCryptoAesRemainingLinear.soft.fixslice.rotate_rows_2 word =
      .ok ⟨rotateSecond 2 word.bv⟩ := by rfl

theorem rotate_second3 (word : U64) :
    RustCryptoAesRemainingLinear.soft.fixslice.rotate_rows_and_columns_2_2 word =
      .ok ⟨rotateSecond 3 word.bv⟩ := by rfl

theorem mix1_reference (words : Words (BitVec 64)) :
    RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_1 (wordArray words) =
      .ok (wordArray (mixWords 1 words)) := by
  simp [RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_1, wordArray, Array.index_usize,
    Array.update, Words.list, rotate_first1, rotate_second1, lift, mixWords]
  rfl

theorem mix2_reference (words : Words (BitVec 64)) :
    RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_2 (wordArray words) =
      .ok (wordArray (mixWords 2 words)) := by
  simp [RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_2, wordArray, Array.index_usize,
    Array.update, Words.list, rotate_first2, rotate_second2, lift, mixWords]
  rfl

theorem mix3_reference (words : Words (BitVec 64)) :
    RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_3 (wordArray words) =
      .ok (wordArray (mixWords 3 words)) := by
  simp [RustCryptoAesRemainingLinear.soft.fixslice.mix_columns_3, wordArray, Array.index_usize,
    Array.update, Words.list, rotate_first3, rotate_second3, lift, mixWords]
  rfl

end LibSignalReference.Proofs.AesMixPhases
