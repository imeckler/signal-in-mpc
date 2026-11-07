import TlsMpc.AigExport
import TlsMpc.BvConstruct

namespace TlsMpc.Signal.AesXorAssign

open Std.Tactic.BVDecide

def expr (state key : BVExpr 64) : BVExpr 64 := BvConstruct.bin state .xor key

theorem expr_refines (state key : BVExpr 64) (assign : BVExpr.Assignment) :
    (expr state key).eval assign = (state.eval assign ^^^ key.eval assign) := by
  simp [expr]

theorem compiled_expr_correct (state key : BVExpr 64) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 64) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (expr state key)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (expr state key)).vec.get index hi)) =
      (state.eval assign ^^^ key.eval assign).getLsbD index := by
  rw [AigExport.compile_correct, expr_refines]

end TlsMpc.Signal.AesXorAssign
