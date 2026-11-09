import AesCtrBlockWork.Generated.InvBitsliceNamedV1.Funs
import LibSignalReference.Proofs.AesInverseWrite
namespace LibSignalReference.Candidate.AesCtrInverse
open Aeneas Aeneas.Std
open LibSignalReference.Proofs.AesLayout
open LibSignalReference.Proofs.AesInverseWrite
open TlsMpc.Signal.AesLayout

theorem delta_source_same :
 RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 =
 RustCryptoAesLayout.soft.fixslice.delta_swap_2 := rfl

theorem write_source_same :
 RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice.write_reordered =
 RustCryptoAesInverseWrite.soft.fixslice.inv_bitslice.write_reordered := rfl

theorem delta_refines (a b mask : U64) (shift : U32) (hs : shift.val<64) :
 RustCryptoAesCtrInverse.soft.fixslice.delta_swap_2 a b shift mask =
 .ok (⟨(deltaSwap a.bv b.bv shift.val mask.bv).1⟩,
      ⟨(deltaSwap a.bv b.bv shift.val mask.bv).2⟩) := by
 rw [delta_source_same]
 exact LibSignalReference.Proofs.AesLayout.delta_refines a b mask shift hs

theorem write_refines (column : U64) (initial : Nat→U8) :
 RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice.write_reordered column (slice12 initial) =
 .ok (resultSlice column.bv (fun byte => (initial byte).bv)) := by
 rw [write_source_same]
 exact write_reference column initial

theorem rejects_bad_length (input : Slice U64) (bad : input.length≠8) :
 RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice input = .fail .assertionFailure := by
 have h : input.len ≠ 8#usize := by scalar_tac
 simp [RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice,
   RustCryptoAesCtrInverse.core.slice.SliceU64.len.specialized_Fun_119f09e8f72b57b7623987b9b0f893bbea4ce9fea982447bc97cd7147a229fe0,
   h, massert]
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def blockBytes (lo hi : BitVec 64) : List (BitVec 8) :=
 [lo.setWidth 8,(lo >>> 16).setWidth 8,(lo >>> 32).setWidth 8,(lo >>> 48).setWidth 8,
  hi.setWidth 8,(hi >>> 16).setWidth 8,(hi >>> 32).setWidth 8,(hi >>> 48).setWidth 8,
  (lo >>> 8).setWidth 8,(lo >>> 24).setWidth 8,(lo >>> 40).setWidth 8,(lo >>> 56).setWidth 8,
  (hi >>> 8).setWidth 8,(hi >>> 24).setWidth 8,(hi >>> 40).setWidth 8,(hi >>> 56).setWidth 8]
def blockArray (lo hi : BitVec 64) : Array U8 (16#usize) :=
 ⟨(blockBytes lo hi).map UScalar.mk,by simp [blockBytes]⟩
def inverseResult (words : Words (BitVec 64)) : RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5 :=
 let t:=transpose words
 ⟨[blockArray t.w0 t.w4,blockArray t.w1 t.w5,blockArray t.w2 t.w6,blockArray t.w3 t.w7],by simp⟩
def zeroBatch : RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5 :=
 ⟨List.replicate 4 ⟨List.replicate 16 (0#u8),by decide⟩,by decide⟩
theorem default_batch : RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.Insts.CoreDefaultDefault.default = .ok zeroBatch := by
 simp [RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.Insts.CoreDefaultDefault.default,core.default.DefaultArray.default,core.default.DefaultArray,core.default.DefaultU8.default,Array.repeat,zeroBatch,UScalar.ofNatCore]
 simp only [UScalar.val]
 rfl

end LibSignalReference.Candidate.AesCtrInverse
