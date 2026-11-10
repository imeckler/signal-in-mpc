import CtrReferenceV1Work.ParallelXorV1Work.Reference
import TlsMpc.ByteCircuit
namespace LibSignalReference.Candidate.ParallelXor4
open Aeneas Aeneas.Std TlsMpc
open _root_.Std.Tactic.BVDecide
open LibSignalReference.Candidate.FixedDispatch
set_option maxHeartbeats 1000000

def expression (input data : Nat → Nat → BVExpr 8) : List (BVExpr 8) :=
 (List.range 4).flatMap (fun r => (List.range 16).map
  (fun c => BvConstruct.bin (input r c) .xor (data r c)))

def bytes (value : Array (Array U8 16#usize) 4#usize) :=
 value.val.flatMap (fun block => block.val.map UScalar.bv)

theorem expression_correct (input data : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment) :
 (expression input data).map (BVExpr.eval assign) =
 bytes (batch (fun r c => (input r c).eval assign ^^^ (data r c).eval assign)) := by
 simp [expression,bytes,batch,AesInverseCircuit.originalBatch,blockOf,
  List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def,
  BvConstruct.eval_bin,BVBinOp.eval]

theorem compiled_source_xor (input data : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
 (old : Array (Array U8 16#usize) 4#usize) :
 ∃ output back,
  ActualParallelXor4.InOut.xor_in2out
   ⟨batch (fun r c => (input r c).eval assign),old⟩
   (batch (fun r c => (data r c).eval assign)) = .ok (output,back) ∧
  ∀ (index : Nat) (hi : index < 8*(expression input data).length),
   AigExport.evalRef
    (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expression input data))).aig)
    (fun varId bit => (assign.get varId).bv.getLsbD bit)
    (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (expression input data))).vec.get index hi)) =
   (ByteCircuit.joinValue (bytes output.output)).getLsbD index := by
 refine ⟨⟨batch (fun r c => (input r c).eval assign),
  batch (fun r c => (input r c).eval assign ^^^ (data r c).eval assign)⟩,
  (fun value => ⟨batch (fun r c => (input r c).eval assign),value.output⟩),
  source_xor _ _ _,?_⟩
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,expression_correct]
end LibSignalReference.Candidate.ParallelXor4
