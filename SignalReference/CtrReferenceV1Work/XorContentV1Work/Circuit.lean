import CtrReferenceV1Work.XorContentV1Work.LoopReference
import TlsMpc.ByteCircuit
namespace LibSignalReference.Candidate.XorContent16
open Aeneas Aeneas.Std TlsMpc
open _root_.Std.Tactic.BVDecide
open LibSignalReference.Candidate.FixedDispatch
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def expression (input data : Nat → BVExpr 8) : List (BVExpr 8) :=
 (List.range 16).map (fun i => BvConstruct.bin (input i) .xor (data i))

theorem expression_correct (input data : Nat → BVExpr 8) (assign : BVExpr.Assignment) :
 (expression input data).map (BVExpr.eval assign) =
 (blockOf (fun i => (input i).eval assign ^^^ (data i).eval assign)).val.map UScalar.bv := by
 simp only [expression,blockOf,List.map_map,Function.comp_def,BvConstruct.eval_bin,BVBinOp.eval]

theorem compiled_source_xor (input data : Nat → BVExpr 8) (assign : BVExpr.Assignment)
 (old : Array U8 16#usize) :
 ∃ output back,
  ActualXorContent16.InOut.xor_in2out
   ⟨blockOf (fun i => (input i).eval assign),old⟩
   (blockOf (fun i => (data i).eval assign)) = .ok (output,back) ∧
  ∀ (index : Nat) (hi : index < 8*(expression input data).length),
   AigExport.evalRef
    (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expression input data))).aig)
    (fun varId bit => (assign.get varId).bv.getLsbD bit)
    (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (expression input data))).vec.get index hi)) =
   (ByteCircuit.joinValue (output.output.val.map UScalar.bv)).getLsbD index := by
 refine ⟨⟨blockOf (fun i => (input i).eval assign),
  blockOf (fun i => (input i).eval assign ^^^ (data i).eval assign)⟩,
  (fun value => ⟨blockOf (fun i => (input i).eval assign),value.output⟩),
  source_xor _ _ _,?_⟩
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,expression_correct]

end LibSignalReference.Candidate.XorContent16
