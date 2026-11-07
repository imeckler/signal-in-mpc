import AesLinearWork.Generated.MixColumns0.Funs
import AesLinearWork.Mix

namespace SignalReference.AesLinear

open Aeneas Aeneas.Std TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def wordArray (words : Words (BitVec 64)) : Array U64 8#usize :=
  ⟨words.list.map (fun word => ⟨word⟩), by simp [Words.list]⟩

theorem rotate_one (word : U64) :
    RustCryptoAesLinear.soft.fixslice.rotate_rows_1 word = .ok ⟨word.bv.rotateRight 16⟩ := by rfl

theorem rotate_two (word : U64) :
    RustCryptoAesLinear.soft.fixslice.rotate_rows_2 word = .ok ⟨word.bv.rotateRight 32⟩ := by rfl

theorem mix_reference (words : Words (BitVec 64)) :
    RustCryptoAesLinear.soft.fixslice.mix_columns_0 (wordArray words) =
      .ok (wordArray (mixWords words)) := by
  simp [RustCryptoAesLinear.soft.fixslice.mix_columns_0, wordArray, Array.index_usize,
    Array.update, Words.list, rotate_one, rotate_two, lift, mixWords]
  rfl

end SignalReference.AesLinear
