import AesCtrBlockWork.FixsliceCircuitV1Work.Symbolic64
import LibSignalReference.Proofs.AesLayout
namespace LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open _root_.Std.Tactic.BVDecide
open LibSignalReference.Candidate.AesInverseCircuit
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem at_map (f : W→W') (words : Words W) (index : Nat) :
 (mapWords f words).at index=f (words.at index) := by
 unfold Words.at
 split <;>rfl


def planeExpr64 (input : Nat→Nat→BVExpr 8) (plane : Nat) : BVExpr 64 :=
 TlsMpc.Signal.AesKeySchedule.packWordExpr (fun byte=>byteExpr input plane byte)

theorem packed_plane (input : Nat→Nat→BitVec 8) (plane : Fin 8) :
 TlsMpc.Signal.AesKeySchedule.packWord (fun byte=>byteValue input plane.val byte)=
 (network input).at plane.val := by
 unfold TlsMpc.Signal.AesKeySchedule.packWord
 simp only [byteValue_network input plane ⟨7,by decide⟩,byteValue_network input plane ⟨6,by decide⟩,
  byteValue_network input plane ⟨5,by decide⟩,byteValue_network input plane ⟨4,by decide⟩,
  byteValue_network input plane ⟨3,by decide⟩,byteValue_network input plane ⟨2,by decide⟩,
  byteValue_network input plane ⟨1,by decide⟩,byteValue_network input plane ⟨0,by decide⟩]
 exact TlsMpc.Signal.AesKeySchedule.packWord_extract ((network input).at plane.val)


theorem planeExpr64_correct (input : Nat→Nat→BVExpr 8) (plane : Fin 8)
 (assign : BVExpr.Assignment) :
 (planeExpr64 input plane.val).eval assign=(network (fun b i=>(input b i).eval assign)).at plane.val := by
 simp only [planeExpr64,TlsMpc.Signal.AesKeySchedule.packWordExpr_refines,byteExpr_refines]
 exact packed_plane (fun b i=>(input b i).eval assign) plane


def inputWords64 (input : Nat→Nat→BVExpr 8) : Words (BVExpr 64) :=
 ⟨planeExpr64 input 0,planeExpr64 input 1,planeExpr64 input 2,planeExpr64 input 3,
  planeExpr64 input 4,planeExpr64 input 5,planeExpr64 input 6,planeExpr64 input 7⟩

theorem inputWords64_at (input : Nat→Nat→BVExpr 8) (plane : Fin 8) :
 (inputWords64 input).at plane.val=planeExpr64 input plane.val := by
 fin_cases plane <;>rfl

theorem inputWords64_correct (input : Nat→Nat→BVExpr 8) (assign : BVExpr.Assignment) :
 mapWords (BVExpr.eval assign) (inputWords64 input)=network (fun b i=>(input b i).eval assign) := by
 apply words_ext
 intro plane
 rw [at_map,inputWords64_at]
 exact planeExpr64_correct input plane assign


def byteLane (block byte : Nat) : Nat := block+16*(byte%4)+4*(byte/4)
def decode64 (words : Words (BitVec 64)) (block byte : Nat) : BitVec 8 :=
 AesSbox.packValue ((List.range 8).map (fun plane=>(words.at plane).extractLsb' (byteLane block byte) 1))

theorem decode64_bit (words : Words (BitVec 64)) (block byte : Nat) (plane : Fin 8) :
 (decode64 words block byte).getLsbD plane.val=(words.at plane.val).getLsbD (byteLane block byte) := by
 fin_cases plane <;>simp only [decode64,AesSbox.packValue,BitVec.getLsbD_append] <;>simp


theorem network_decode64 (words : Words (BitVec 64)) : network (decode64 words)=words := by
 apply words_ext
 intro plane
 apply BitVec.eq_of_getLsbD_eq
 intro lane hl
 rw [network_bit _ plane ⟨lane,hl⟩,decode64_bit]
 congr 1
 interval_cases lane <;>simp [byteLane]


theorem inverse_decode64 (words : Words (BitVec 64)) :
 AesCtrInverse.inverseResult words=originalBatch (decode64 words) := by
 have h:=inverse_network (decode64 words)
 rw [network_decode64] at h
 exact h


def decodeExpr64 (words : Words (BVExpr 64)) (block byte : Nat) : BVExpr 8 :=
 AesSbox.packExpr ((List.range 8).map (fun plane=>BvConstruct.extract (byteLane block byte) 1 (words.at plane)))



theorem decodeExpr64_correct (words : Words (BVExpr 64)) (block byte : Nat) (assign : BVExpr.Assignment) :
 (decodeExpr64 words block byte).eval assign=decode64 (mapWords (BVExpr.eval assign) words) block byte := by
 simp only [decodeExpr64,decode64,AesSbox.packExpr_refines,List.map_map,Function.comp_def,
  BvConstruct.eval_extract,at_map]

end LibSignalReference.Candidate.FixsliceCircuitV1
