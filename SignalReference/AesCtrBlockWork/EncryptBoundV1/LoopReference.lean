import AesCtrBlockWork.EncryptBoundV1.RoundModel
import AesCtrBlockWork.EncryptBoundV1.KeyRanges
namespace LibSignalReference.Candidate.AesLoopReference
open Aeneas Aeneas.Std TlsMpc.Signal.AesLayout
open LibSignalReference.Proofs.AesLayout LibSignalReference.Proofs.AesLinear
open LibSignalReference.Candidate.AesRawSub
open LibSignalReference.Candidate.AesRoundModel
open LibSignalReference.Candidate.AesKeyRanges
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def round1 (words key : Words (BitVec 64)) := xorWords (TlsMpc.Signal.AesRemainingLinear.mixWords 1 (rawWords words)) key
def round2 (words key : Words (BitVec 64)) := xorWords (TlsMpc.Signal.AesRemainingLinear.mixWords 2 (rawWords words)) key
def round3 (words key : Words (BitVec 64)) := xorWords (TlsMpc.Signal.AesRemainingLinear.mixWords 3 (rawWords words)) key
def round0 (words key : Words (BitVec 64)) := xorWords (TlsMpc.Signal.AesLinear.mixWords (rawWords words)) key
def fourRounds (keys : Nat→Words (BitVec 64)) (r : Nat) (words : Words (BitVec 64)) :=
 round0 (round3 (round2 (round1 words (keys r)) (keys (r+1))) (keys (r+2))) (keys (r+3))

theorem body0 (keys : Nat→Words (BitVec 64)) (words : Words (BitVec 64)) :
 RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt_loop.body (keyArray keys) (wordArray words) (8#usize) =
 .ok (.cont (wordArray (fourRounds keys 1 words),40#usize)) := by
 simp only [RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt_loop.body,
   Array.to_slice_mut,lift,bind_tc_ok,uncurry_apply_pair]
 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix1_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (1 : Fin 15)]
 simp only [bind_tc_ok]
 have hr:=source_range keys (1 : Fin 15)
 simp only [sourceRange,start] at hr
 with_unfolding_all erw [hr]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok,show stop (1 : Fin 15) ≠ 112#usize from by decide +kernel,if_false]

 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix2_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (2 : Fin 15)]
 simp only [bind_tc_ok]
 have hr2:=source_range keys (2 : Fin 15)
 simp only [sourceRange,start] at hr2
 with_unfolding_all erw [hr2]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok]

 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix3_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (3 : Fin 15)]
 simp only [bind_tc_ok]
 have hr3:=source_range keys (3 : Fin 15)
 simp only [sourceRange,start] at hr3
 with_unfolding_all erw [hr3]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok]

 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix0_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (4 : Fin 15)]
 simp only [bind_tc_ok]
 have hr4:=source_range keys (4 : Fin 15)
 simp only [sourceRange,start] at hr4
 with_unfolding_all erw [hr4]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok]
 with_unfolding_all rfl


theorem body1 (keys : Nat→Words (BitVec 64)) (words : Words (BitVec 64)) :
 RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt_loop.body (keyArray keys) (wordArray words) (40#usize) =
 .ok (.cont (wordArray (fourRounds keys 5 words),72#usize)) := by
 simp only [RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt_loop.body,
   Array.to_slice_mut,lift,bind_tc_ok,uncurry_apply_pair]
 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix1_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (5 : Fin 15)]
 simp only [bind_tc_ok]
 have hr:=source_range keys (5 : Fin 15)
 simp only [sourceRange,start] at hr
 with_unfolding_all erw [hr]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok,show stop (5 : Fin 15) ≠ 112#usize from by decide +kernel,if_false]

 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix2_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (6 : Fin 15)]
 simp only [bind_tc_ok]
 have hr2:=source_range keys (6 : Fin 15)
 simp only [sourceRange,start] at hr2
 with_unfolding_all erw [hr2]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok]

 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix3_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (7 : Fin 15)]
 simp only [bind_tc_ok]
 have hr3:=source_range keys (7 : Fin 15)
 simp only [sourceRange,start] at hr3
 with_unfolding_all erw [hr3]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok]

 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix0_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (8 : Fin 15)]
 simp only [bind_tc_ok]
 have hr4:=source_range keys (8 : Fin 15)
 simp only [sourceRange,start] at hr4
 with_unfolding_all erw [hr4]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok]
 with_unfolding_all rfl


theorem body2 (keys : Nat→Words (BitVec 64)) (words : Words (BitVec 64)) :
 RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt_loop.body (keyArray keys) (wordArray words) (72#usize) =
 .ok (.cont (wordArray (fourRounds keys 9 words),104#usize)) := by
 simp only [RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt_loop.body,
   Array.to_slice_mut,lift,bind_tc_ok,uncurry_apply_pair]
 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix1_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (9 : Fin 15)]
 simp only [bind_tc_ok]
 have hr:=source_range keys (9 : Fin 15)
 simp only [sourceRange,start] at hr
 with_unfolding_all erw [hr]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok,show stop (9 : Fin 15) ≠ 112#usize from by decide +kernel,if_false]

 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix2_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (10 : Fin 15)]
 simp only [bind_tc_ok]
 have hr2:=source_range keys (10 : Fin 15)
 simp only [sourceRange,start] at hr2
 with_unfolding_all erw [hr2]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok]

 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix3_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (11 : Fin 15)]
 simp only [bind_tc_ok]
 have hr3:=source_range keys (11 : Fin 15)
 simp only [sourceRange,start] at hr3
 with_unfolding_all erw [hr3]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok]

 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix0_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (12 : Fin 15)]
 simp only [bind_tc_ok]
 have hr4:=source_range keys (12 : Fin 15)
 simp only [sourceRange,start] at hr4
 with_unfolding_all erw [hr4]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok]
 with_unfolding_all rfl


theorem body3 (keys : Nat→Words (BitVec 64)) (words : Words (BitVec 64)) :
 RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt_loop.body (keyArray keys) (wordArray words) (104#usize) =
 .ok (.done (wordArray (round1 words (keys 13)))) := by
 simp only [RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt_loop.body,
   Array.to_slice_mut,lift,bind_tc_ok,uncurry_apply_pair]
 with_unfolding_all erw [actual_words]
 simp only [bind_tc_ok]
 with_unfolding_all erw [mix1_reference]
 simp only [bind_tc_ok]
 with_unfolding_all erw [add8 (13 : Fin 15)]
 simp only [bind_tc_ok]
 have hr:=source_range keys (13 : Fin 15)
 simp only [sourceRange,start] at hr
 with_unfolding_all erw [hr]
 simp only [bind_tc_ok]
 with_unfolding_all erw [key_reference]
 simp only [bind_tc_ok,show stop (13 : Fin 15) = 112#usize from by decide +kernel,if_true]
 with_unfolding_all rfl


def loopResult (keys : Nat→Words (BitVec 64)) (words : Words (BitVec 64)) :=
 round1 (fourRounds keys 9 (fourRounds keys 5 (fourRounds keys 1 words))) (keys 13)

theorem loop_reference (keys : Nat→Words (BitVec 64)) (words : Words (BitVec 64)) :
 RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt_loop (keyArray keys) (wordArray words) (8#usize) =
 .ok (wordArray (loopResult keys words)) := by
 simp only [RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt_loop]
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body0]
 with_unfolding_all dsimp only
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body2]
 with_unfolding_all dsimp only
 with_unfolding_all rw [loop.eq_1]
 with_unfolding_all dsimp only
 with_unfolding_all rw [body3]
 with_unfolding_all dsimp only

 with_unfolding_all rfl

end LibSignalReference.Candidate.AesLoopReference
