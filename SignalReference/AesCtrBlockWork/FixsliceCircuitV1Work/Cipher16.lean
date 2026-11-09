import AesCtrBlockWork.FixsliceCircuitV1Work.Symbolic16
import AesCtrBlockWork.FixsliceCircuitV1Work.ComputedCipher64
namespace LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open Aeneas Aeneas.Std
open _root_.Std.Tactic.BVDecide
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def byteLane16 (byte : Nat) : Nat := 4*(byte%4)+byte/4
def decode16 (words : Words (BitVec 16)) (byte : Nat) : BitVec 8 :=
 AesSbox.packValue ((List.range 8).map (fun plane=>(words.at plane).extractLsb' (byteLane16 byte) 1))

theorem project_extract1 (block : Fin 4) (word : BitVec 64) (i : Nat) (hi : i<16) :
 (project block word).extractLsb' i 1=word.extractLsb' (4*i+block.val) 1 := by
 apply BitVec.eq_of_getLsbD_eq
 intro bit hb
 have hz:bit=0 := by omega
 subst bit
 simpa only [BitVec.getLsbD_extractLsb',Nat.add_zero,show decide (0<1)=true from by decide,Bool.true_and] using project_bit block word i hi

theorem decode16_project (block : Fin 4) (words : Words (BitVec 64)) (byte : Fin 16) :
 decode16 (mapWords (project block) words) byte.val=decode64 words block.val byte.val := by
 have hi : byteLane16 byte.val<16 := by unfold byteLane16;omega
 have hl : 4*byteLane16 byte.val+block.val=byteLane block.val byte.val := by
  unfold byteLane16 byteLane
  omega
 simp only [decode16,decode64,at_map,project_extract1 _ _ _ hi,hl]

def decodeExpr16 (words : Words (BVExpr 16)) (byte : Nat) : BVExpr 8 :=
 AesSbox.packExpr ((List.range 8).map (fun plane=>BvConstruct.extract (byteLane16 byte) 1 (words.at plane)))

theorem decodeExpr16_correct (words : Words (BVExpr 16)) (byte : Nat) (assign : BVExpr.Assignment) :
 (decodeExpr16 words byte).eval assign=decode16 (mapWords (BVExpr.eval assign) words) byte := by
 simp only [decodeExpr16,decode16,AesSbox.packExpr_refines,List.map_map,Function.comp_def,BvConstruct.eval_extract,at_map]

theorem projectWordsExpr_correct (block : Fin 4) (words : Words (BVExpr 64)) (assign : BVExpr.Assignment) :
 mapWords (BVExpr.eval assign) (mapWords (projectExpr block) words)=
 mapWords (project block) (mapWords (BVExpr.eval assign) words) := by
 simp only [mapWords,projectExpr_correct]

def stateExpression16 (block : Fin 4) (keys : Nat→Words (BVExpr 64)) (input : Nat→Nat→BVExpr 8) : Words (BVExpr 16) :=
 encrypt (symbolic16 block) (fun r=>mapWords (projectExpr block) (keys r))
  (mapWords (projectExpr block) (inputWords64 input))

theorem stateExpression16_correct (block : Fin 4) (keys : Nat→Words (BVExpr 64)) (input : Nat→Nat→BVExpr 8)
 (assign : BVExpr.Assignment) :
 mapWords (BVExpr.eval assign) (stateExpression16 block keys input)=
 mapWords (project block) (encrypt concrete64 (fun r=>mapWords (BVExpr.eval assign) (keys r))
  (network (fun b i=>(input b i).eval assign))) := by
 simp only [stateExpression16,symbolic_state_correct16,projectWordsExpr_correct,inputWords64_correct]
 exact (projected_encrypt block _ _).symm

def expression16 (block : Fin 4) (keys : Nat→Words (BVExpr 64)) (input : Nat→Nat→BVExpr 8) : List (BVExpr 8) :=
 (List.range 16).map (decodeExpr16 (stateExpression16 block keys input))

theorem expression16_correct (block : Fin 4) (keys : Nat→Words (BVExpr 64)) (input : Nat→Nat→BVExpr 8)
 (assign : BVExpr.Assignment) :
 (expression16 block keys input).map (BVExpr.eval assign)=
 (List.range 16).map (decode64 (encrypt concrete64 (fun r=>mapWords (BVExpr.eval assign) (keys r))
  (network (fun b i=>(input b i).eval assign))) block.val) := by
 simp only [expression16,List.map_map,Function.comp_def]
 apply List.map_congr_left
 intro byte hb
 have hbyte : byte<16 := by simpa using hb
 simp only [decodeExpr16_correct,stateExpression16_correct]
 exact decode16_project block _ ⟨byte,hbyte⟩

def selectedBytes (result : RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5) (block : Fin 4) : List (BitVec 8) :=
 ((encodeBatch result).drop (16*block.val)).take 16

theorem selected_original (input : Nat→Nat→BitVec 8) (block : Fin 4) :
 selectedBytes (AesInverseCircuit.originalBatch input) block=(List.range 16).map (input block.val) := by
 fin_cases block <;>simp [selectedBytes,encodeBatch,AesInverseCircuit.originalBatch,List.range_succ]

theorem compiled_actual16 (block : Fin 4) (keys : Nat→Words (BVExpr 64)) (input : Nat→Nat→BVExpr 8)
 (assign : BVExpr.Assignment) :
 ∃ result,
  RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt
   (AesKeyRanges.keyArray (fun r=>mapWords (BVExpr.eval assign) (keys r)))
   (AesInverseCircuit.originalBatch (fun b i=>(input b i).eval assign)) = .ok result ∧
  ∀ (index : Nat) (hi : index<8*(expression16 block keys input).length),
   AigExport.evalRef
    (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expression16 block keys input))).aig)
    (fun varId bit=>(assign.get varId).bv.getLsbD bit)
    (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (expression16 block keys input))).vec.get index hi)) =
   (ByteCircuit.joinValue (selectedBytes result block)).getLsbD index := by
 refine ⟨AesInverseCircuit.originalBatch (decode64 (encrypt concrete64
  (fun r=>mapWords (BVExpr.eval assign) (keys r)) (network (fun b i=>(input b i).eval assign)))),actual_model _ _,?_⟩
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,expression16_correct,selected_original]

def computedExpression16 (block : Fin 4) (key : Nat→BVExpr 8) (input : Nat→Nat→BVExpr 8) : List (BVExpr 8) :=
 expression16 block (keyGroupsExpression key) input

theorem compiled_actual_from_key16 (block : Fin 4) (key : Nat→BVExpr 8) (input : Nat→Nat→BVExpr 8)
 (assign : BVExpr.Assignment) :
 ∃ schedule result,
  RustCryptoAesKeySchedule.soft.fixslice.aes256_key_schedule
   (AesKeySchedule.keyArray (fun i=>(⟨(key i).eval assign⟩ : U8))) = .ok schedule ∧
  RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt schedule
   (AesInverseCircuit.originalBatch (fun b i=>(input b i).eval assign)) = .ok result ∧
  ∀ (index : Nat) (hi : index<8*(computedExpression16 block key input).length),
   AigExport.evalRef
    (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (computedExpression16 block key input))).aig)
    (fun varId bit=>(assign.get varId).bv.getLsbD bit)
    (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (computedExpression16 block key input))).vec.get index hi)) =
   (ByteCircuit.joinValue (selectedBytes result block)).getLsbD index := by
 obtain ⟨schedule,hkey,hschedule⟩:=actual_schedule (fun i=>(key i).eval assign)
 obtain ⟨result,hcipher,hbits⟩:=compiled_actual16 block (keyGroupsExpression key) input assign
 have hgroups : (fun r=>mapWords (BVExpr.eval assign) (keyGroupsExpression key r))=
  groupAt 0 (scheduleValue (fun i=>(key i).eval assign)) := by
  funext r
  exact keyGroupsExpression_correct key assign r
 rw [hgroups,←hschedule] at hcipher
 refine ⟨schedule,result,hkey,hcipher,?_⟩
 simpa only [computedExpression16] using hbits

/-- Exact plaintext embedding used by pinned soft.rs::encrypt_block: other
three batch inputs are zero, only output block0 is selected. -/
def singleInput (input : Nat→BVExpr 8) (block byte : Nat) : BVExpr 8 :=
 if block=0 then input byte else .const 0
def singleExpression (key input : Nat→BVExpr 8) : List (BVExpr 8) :=
 computedExpression16 ⟨0,by decide⟩ key (singleInput input)
end LibSignalReference.Candidate.FixsliceCircuitV1
