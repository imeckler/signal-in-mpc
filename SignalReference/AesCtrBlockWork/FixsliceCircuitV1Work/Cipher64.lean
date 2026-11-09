import AesCtrBlockWork.FixsliceCircuitV1Work.Layout
namespace LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open _root_.Std.Tactic.BVDecide
open Aeneas Aeneas.Std
open LibSignalReference.Candidate.AesInverseCircuit
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def expression64 (keys : Nat→Words (BVExpr 64)) (input : Nat→Nat→BVExpr 8) : List (BVExpr 8) :=
 let state:=encrypt symbolic64 keys (inputWords64 input)
 (List.range 4).flatMap (fun block=>(List.range 16).map (decodeExpr64 state block))
def value64 (keys : Nat→Words (BitVec 64)) (input : Nat→Nat→BitVec 8) : List (BitVec 8) :=
 let state:=encrypt concrete64 keys (network input)
 (List.range 4).flatMap (fun block=>(List.range 16).map (decode64 state block))

theorem expression64_correct (keys : Nat→Words (BVExpr 64)) (input : Nat→Nat→BVExpr 8)
 (assign : BVExpr.Assignment) :
 (expression64 keys input).map (BVExpr.eval assign)=
 value64 (fun r=>mapWords (BVExpr.eval assign) (keys r)) (fun b i=>(input b i).eval assign) := by
 simp only [expression64,value64,List.map_flatMap,List.map_map,Function.comp_def,
  decodeExpr64_correct,symbolic_state_correct,inputWords64_correct]

def encodeBatch (batch : RustCryptoAesCtrInverse.hybrid_array.Array.specialized_Type_466e03121b73c7d435361c7adc904649fbf81c760e593c61b65a8532a101fdf5) : List (BitVec 8) :=
 batch.val.flatMap (fun block=>block.val.map UScalar.bv)

theorem encode_original (input : Nat→Nat→BitVec 8) :
 encodeBatch (originalBatch input)=(List.range 4).flatMap (fun b=>(List.range 16).map (input b)) := by
 simp [encodeBatch,originalBatch,List.flatMap_map,List.map_map,Function.comp_def]

theorem actual_model (keys : Nat→Words (BitVec 64)) (input : Nat→Nat→BitVec 8) :
 RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt (AesKeyRanges.keyArray keys) (originalBatch input) =
 .ok (originalBatch (decode64 (encrypt concrete64 keys (network input)))) := by
 rw [AesEntryReference.actual_entry,inverse_decode64,concrete_matches]
 rfl

theorem compiled_actual64 (keys : Nat→Words (BVExpr 64)) (input : Nat→Nat→BVExpr 8)
 (assign : BVExpr.Assignment) :
 ∃ result,
  RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt
   (AesKeyRanges.keyArray (fun r=>mapWords (BVExpr.eval assign) (keys r)))
   (originalBatch (fun b i=>(input b i).eval assign)) = .ok result ∧
  ∀ (index : Nat) (hi : index<8*(expression64 keys input).length),
   AigExport.evalRef
    (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expression64 keys input))).aig)
    (fun varId bit=>(assign.get varId).bv.getLsbD bit)
    (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (expression64 keys input))).vec.get index hi)) =
   (ByteCircuit.joinValue (encodeBatch result)).getLsbD index := by
 refine ⟨originalBatch (decode64 (encrypt concrete64
  (fun r=>mapWords (BVExpr.eval assign) (keys r)) (network (fun b i=>(input b i).eval assign)))),actual_model _ _,?_⟩
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,expression64_correct,encode_original]
 rfl
end LibSignalReference.Candidate.FixsliceCircuitV1
