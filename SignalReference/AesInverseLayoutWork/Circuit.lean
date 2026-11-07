import TlsMpc.ByteCircuit

/-! Fixed 12-byte write-back operation used by actual RustCrypto AES inverse
layout. The column and every initial byte are secret. Four bytes are preserved;
the eight writes are pure bit selection, without secret branches or indexing. -/

namespace TlsMpc.Signal.AesInverseWrite

open Std.Tactic.BVDecide

def value (column : BitVec 64) (initial : Nat → BitVec 8) : List (BitVec 8) :=
  [column.extractLsb' 0 8, column.extractLsb' 16 8,
   column.extractLsb' 32 8, column.extractLsb' 48 8,
   initial 4, initial 5, initial 6, initial 7,
   column.extractLsb' 8 8, column.extractLsb' 24 8,
   column.extractLsb' 40 8, column.extractLsb' 56 8]

def expr (column : BVExpr 64) (initial : Nat → BVExpr 8) : List (BVExpr 8) :=
  [BvConstruct.extract 0 8 column, BvConstruct.extract 16 8 column,
   BvConstruct.extract 32 8 column, BvConstruct.extract 48 8 column,
   initial 4, initial 5, initial 6, initial 7,
   BvConstruct.extract 8 8 column, BvConstruct.extract 24 8 column,
   BvConstruct.extract 40 8 column, BvConstruct.extract 56 8 column]

theorem expr_refines (column : BVExpr 64) (initial : Nat → BVExpr 8)
    (assign : BVExpr.Assignment) :
    (expr column initial).map (BVExpr.eval assign) =
      value (column.eval assign) (fun index => (initial index).eval assign) := by
  simp only [expr, value, List.map_cons, List.map_nil, BvConstruct.eval_extract]

theorem compiled_expr_correct (column : BVExpr 64) (initial : Nat → BVExpr 8)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (expr column initial).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (expr column initial))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (expr column initial))).vec.get index hi)) =
      (ByteCircuit.joinValue
        (value (column.eval assign) (fun byte => (initial byte).eval assign))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, expr_refines]

end TlsMpc.Signal.AesInverseWrite
