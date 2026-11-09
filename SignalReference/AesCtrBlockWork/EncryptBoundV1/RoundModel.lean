import AesCtrBlockWork.EncryptBoundV1.RawSubReference
import AesCtrBlockWork.ZipModelV1.RoundKeyReference
import LibSignalReference.Proofs.AesMixPhaseReference
import LibSignalReference.Proofs.AesShiftReference
namespace LibSignalReference.Candidate.AesRoundModel
open Aeneas Aeneas.Std TlsMpc.Signal.AesLayout
open LibSignalReference.Proofs.AesLayout LibSignalReference.Proofs.AesLinear
open LibSignalReference.Candidate.AesRawSub
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def xorWords (a b : Words (BitVec 64)) : Words (BitVec 64) :=
 ⟨a.w0^^^b.w0,a.w1^^^b.w1,a.w2^^^b.w2,a.w3^^^b.w3,
  a.w4^^^b.w4,a.w5^^^b.w5,a.w6^^^b.w6,a.w7^^^b.w7⟩
def subArray (state : Array U64 (8#usize)) : Result (Array U64 (8#usize)) := do
 let (s,back)←lift (Array.to_slice_mut state)
 let changed←RustCryptoAesCtrBlock.soft.fixslice.sub_bytes s
 .ok (back changed)

theorem subArray_reference (words : Words (BitVec 64)) :
 subArray (wordArray words)=.ok (wordArray (rawWords words)) := by
 simp only [subArray,Array.to_slice_mut,lift,bind_tc_ok]
 change (do
  let changed←RustCryptoAesCtrBlock.soft.fixslice.sub_bytes (wordSlice words)
  .ok (Array.from_slice (wordArray words) changed)) = _
 rw [actual_words]
 with_unfolding_all rfl

theorem scalar_xor (a b : BitVec 64) :
 ((⟨a⟩ : U64) ^^^ (⟨b⟩ : U64))=(⟨a^^^b⟩ : U64) := rfl

theorem key_reference (words key : Words (BitVec 64)) :
 RustCryptoAesCtrBlock.soft.fixslice.add_round_key (wordArray words) (wordSlice key) =
 .ok (wordArray (xorWords words key)) := by
 have h:=LibSignalReference.Candidate.AesRoundKeyStdZip.actual_add_round_key
  (fun i=>(⟨words.at i⟩ : U64)) (fun i=>(⟨key.at i⟩ : U64))
 with_unfolding_all simpa only [RustCryptoAesCtrBlock.soft.fixslice.add_round_key,
  LibSignalReference.Candidate.AesRoundKeyStdZip.array8,
  LibSignalReference.Candidate.AesRoundKeyStdZip.slice8,
  wordArray,wordSlice,Words.list,Words.at,xorWords,List.map_cons,List.map_nil,scalar_xor] using h

theorem mix0_reference (words : Words (BitVec 64)) :
 RustCryptoAesCtrBlock.soft.fixslice.mix_columns_0 (wordArray words)=
 .ok (wordArray (TlsMpc.Signal.AesLinear.mixWords words)) := by
 exact mix_reference words

theorem mix1_reference (words : Words (BitVec 64)) :
 RustCryptoAesCtrBlock.soft.fixslice.mix_columns_1 (wordArray words)=
 .ok (wordArray (TlsMpc.Signal.AesRemainingLinear.mixWords 1 words)) := by
 exact LibSignalReference.Proofs.AesMixPhases.mix1_reference words

theorem mix2_reference (words : Words (BitVec 64)) :
 RustCryptoAesCtrBlock.soft.fixslice.mix_columns_2 (wordArray words)=
 .ok (wordArray (TlsMpc.Signal.AesRemainingLinear.mixWords 2 words)) := by
 exact LibSignalReference.Proofs.AesMixPhases.mix2_reference words

theorem mix3_reference (words : Words (BitVec 64)) :
 RustCryptoAesCtrBlock.soft.fixslice.mix_columns_3 (wordArray words)=
 .ok (wordArray (TlsMpc.Signal.AesRemainingLinear.mixWords 3 words)) := by
 exact LibSignalReference.Proofs.AesMixPhases.mix3_reference words
end LibSignalReference.Candidate.AesRoundModel
