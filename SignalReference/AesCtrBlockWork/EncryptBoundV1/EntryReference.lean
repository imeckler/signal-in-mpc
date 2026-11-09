import AesCtrBlockWork.EncryptBoundV1.LoopReference
import AesCtrBlockWork.InverseLayoutCircuit
namespace LibSignalReference.Candidate.AesEntryReference
open Aeneas Aeneas.Std TlsMpc.Signal.AesLayout
open LibSignalReference.Proofs.AesLayout LibSignalReference.Proofs.AesLinear
open LibSignalReference.Candidate.AesRawSub LibSignalReference.Candidate.AesRoundModel
open LibSignalReference.Candidate.AesKeyRanges LibSignalReference.Candidate.AesLoopReference
open LibSignalReference.Candidate.AesInverseCircuit LibSignalReference.Candidate.AesCtrInverse
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def zeroWords : Words (BitVec 64) := ⟨0,0,0,0,0,0,0,0⟩

theorem default_state : RustCryptoAesCtrBlock.ArrayU648.Insts.CoreDefaultDefault.default =
 .ok (wordArray zeroWords) := by
 simp [RustCryptoAesCtrBlock.ArrayU648.Insts.CoreDefaultDefault.default,
  core.default.DefaultArray.default,core.default.DefaultU64.default,
  Array.repeat,wordArray,Words.list,zeroWords,UScalar.ofNatCore]
 simp only [UScalar.val]
 rfl

theorem first_key (keys : Nat→Words (BitVec 64)) :
 RustCryptoAesCtrBlock.ArrayU64120.Insts.CoreOpsIndexIndexspecialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26.index
  (keyArray keys) {«end»:=8#usize} = .ok (wordSlice (keys 0)) := by
 simp [RustCryptoAesCtrBlock.ArrayU64120.Insts.CoreOpsIndexIndexspecialized_Type_57510f1564d005eda0c45028821c0f658cf9a616f9dbf382cc9e92345d79bf26.index,
  core.slice.index.SliceIndexRangeToUsizeSlice.index,keyArray,Array.to_slice,Slice.length,
  wordSlice,Words.list,List.range_succ,List.slice]

theorem last_key (keys : Nat→Words (BitVec 64)) :
 RustCryptoAesCtrBlock.ArrayU64120.Insts.CoreOpsIndexIndexspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index
  (keyArray keys) {start:=112#usize} = .ok (wordSlice (keys 14)) := by
 simp [RustCryptoAesCtrBlock.ArrayU64120.Insts.CoreOpsIndexIndexspecialized_Type_d1f2f41ce9b6a4bab41ab00dc2d7f45668cf5cd166e8302372ae9482af4f16f6.index,
  core.slice.index.SliceIndexRangeFromUsizeSlice.index,keyArray,Array.to_slice,Slice.length,Slice.drop,
  wordSlice,Words.list,List.range_succ,List.slice]

def finalWords (keys : Nat→Words (BitVec 64)) (input : Nat→Nat→BitVec 8) :=
 xorWords (rawWords (TlsMpc.Signal.AesLinear.mapWords TlsMpc.Signal.AesLinear.shiftWord2
  (loopResult keys (xorWords (network input) (keys 0))))) (keys 14)

theorem actual_entry (keys : Nat→Words (BitVec 64)) (input : Nat→Nat→BitVec 8) :
 RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt (keyArray keys) (originalBatch input) =
 .ok (inverseResult (finalWords keys input)) := by
 simp [RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt,default_state,
  RustCryptoAesCtrBlock.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5.Insts.CoreOpsIndexIndexUsize.index,
  RustCryptoAesCtrBlock.hybrid_array.Array.specialized_Type_f6d0079c9d47818b2c760c13dc530abd0fcf2330bbf625eeaa753c4e448e7d5f.Insts.CoreOpsDerefDeref.deref,
  originalBatch,Array.index_usize,Array.to_slice_mut,Array.to_slice,lift,List.range_succ]
 rw [LibSignalReference.Candidate.AesActualBindings.forward]
 with_unfolding_all erw [bitslice_network (fun block byte=>(⟨input block byte⟩ : U8)) zeroWords]
 simp only [bind_tc_ok]
 rw [first_key]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [loop_reference]
 simp only [bind_tc_ok]
 rw [LibSignalReference.Candidate.AesActualBindings.shift]
 with_unfolding_all erw [shift2_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 rw [last_key]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok]
 rw [LibSignalReference.Candidate.AesActualBindings.inverse]
 with_unfolding_all erw [LibSignalReference.Candidate.AesInverseComposition.actual_inverse]
 with_unfolding_all rfl
end LibSignalReference.Candidate.AesEntryReference
