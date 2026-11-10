import CtrReferenceV1Work.ParallelCallbackV1Work.Reference
import CtrReferenceV1Work.ParallelXorV1Work.Circuit
import AesCtrBlockWork.FixsliceCircuitV1Work.ComputedCipher64
namespace LibSignalReference.Candidate.ParallelCallback4
open Aeneas Aeneas.Std TlsMpc
open _root_.Std.Tactic.BVDecide
open LibSignalReference.Candidate.FixedDispatch
open LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def expression (key : Nat → BVExpr 8) (input : Nat → Nat → BVExpr 8) (counter : U32) : List (BVExpr 8) :=
 let state := encrypt symbolic64 (keyGroupsExpression key)
  (inputWords64 (fun r c => .const (ParallelCtr4.counterInput counter r c)))
 (List.range 4).flatMap (fun r => (List.range 16).map
  (fun c => BvConstruct.bin (input r c) .xor (decodeExpr64 state r c)))

theorem expression_correct (key : Nat → BVExpr 8) (input : Nat → Nat → BVExpr 8)
 (counter : U32) (assign : BVExpr.Assignment) :
 (expression key input counter).map (BVExpr.eval assign) =
 ParallelXor4.bytes (AesInverseCircuit.originalBatch (fun r c=>
  (input r c).eval assign ^^^
   encrypted (groupAt 0 (scheduleValue (fun i=>(key i).eval assign)))
    (ParallelCtr4.counterInput counter) r c)) := by
 have hk : (fun r=>mapWords (BVExpr.eval assign) (keyGroupsExpression key r)) =
  groupAt 0 (scheduleValue (fun i=>(key i).eval assign)) := by
  funext r
  exact keyGroupsExpression_correct key assign r
 simp [expression,ParallelXor4.bytes,AesInverseCircuit.originalBatch,blockOf,
  List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def,
  BvConstruct.eval_bin,BVBinOp.eval,decodeExpr64_correct,symbolic_state_correct,
  inputWords64_correct,hk,encrypted]

theorem expression_length (key : Nat → BVExpr 8) (input : Nat → Nat → BVExpr 8) (counter : U32) :
 (expression key input counter).length = 64 := by
 simp [expression,List.length_flatMap,List.range_succ]

theorem compiled_actual_chunk (key : Nat → BVExpr 8) (input : Nat → Nat → BVExpr 8)
 (counter : U32) (assign : BVExpr.Assignment) (old : Array (Array U8 16#usize) 4#usize) :
 ∃ schedule output,
  RustCryptoAesKeySchedule.soft.fixslice.aes256_key_schedule
   (AesKeySchedule.keyArray (fun i=>(⟨(key i).eval assign⟩ : U8))) = .ok schedule ∧
  ActualParallelCallback4.apply_parallel_chunk
   ⟨counter,(CtrState.zeroNonce counter).nonce,schedule⟩
   ⟨AesInverseCircuit.originalBatch (fun r c=>(input r c).eval assign),old⟩ =
   .ok (backend (groupAt 0 (scheduleValue (fun i=>(key i).eval assign)))
    (FixedCtr.after 4 counter),output) ∧
  ∀ (index : Nat) (hi : index < 8*(expression key input counter).length),
   AigExport.evalRef
    (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expression key input counter))).aig)
    (fun varId bit => (assign.get varId).bv.getLsbD bit)
    (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (expression key input counter))).vec.get index hi)) =
   (ByteCircuit.joinValue (ParallelXor4.bytes output.output)).getLsbD index := by
 obtain ⟨schedule,hkey,hkeys⟩ := actual_schedule (fun i=>(key i).eval assign)
 let keys := groupAt 0 (scheduleValue (fun i=>(key i).eval assign))
 refine ⟨schedule,⟨AesInverseCircuit.originalBatch (fun r c=>(input r c).eval assign),
  AesInverseCircuit.originalBatch (fun r c=>(input r c).eval assign ^^^
   encrypted keys (ParallelCtr4.counterInput counter) r c)⟩,hkey,?_,?_⟩
 · rw [hkeys]
   exact actual_chunk keys counter _ old
 · intro index hi
   rw [ByteCircuit.compile_bytes_correct,expression_correct]
end LibSignalReference.Candidate.ParallelCallback4
