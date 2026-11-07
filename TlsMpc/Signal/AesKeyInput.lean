import TlsMpc.Signal.AesKeySchedule

/-! The 32 secret AES256 key bytes feed the repeated-block initial bit layout
by public wire permutation. No extra secret input or opening is required. -/

namespace TlsMpc.Signal.AesKeySchedule

open Std.Tactic.BVDecide

def packWord (bytes : Nat → BitVec 8) : BitVec 64 :=
  bytes 7 ++ (bytes 6 ++ (bytes 5 ++ (bytes 4 ++ (bytes 3 ++ (bytes 2 ++ (bytes 1 ++ bytes 0))))))

def packWordExpr (bytes : Nat → BVExpr 8) : BVExpr 64 :=
  BvConstruct.append (bytes 7) (BvConstruct.append (bytes 6) (BvConstruct.append (bytes 5)
    (BvConstruct.append (bytes 4) (BvConstruct.append (bytes 3) (BvConstruct.append (bytes 2)
      (BvConstruct.append (bytes 1) (bytes 0)))))))

theorem packWordExpr_refines (bytes : Nat → BVExpr 8) (assign : BVExpr.Assignment) :
    (packWordExpr bytes).eval assign = packWord (fun i => (bytes i).eval assign) := by
  simp only [packWordExpr, packWord, BvConstruct.eval_append]

theorem packWord_extract (word : BitVec 64) :
    packWord (fun i => word.extractLsb' (8 * i) 8) = word := by
  simp only [packWord]
  repeat rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  simp

def initialWords (key : Nat → BitVec 8) (offset : Nat) : List (BitVec 64) :=
  (List.range 8).map fun plane => packWord
    (fun byte => AesLayout.byteValue (fun _ index => key (offset + index)) plane byte)

def initialWordsExpr (key : Nat → BVExpr 8) (offset : Nat) : List (BVExpr 64) :=
  (List.range 8).map fun plane => packWordExpr
    (fun byte => AesLayout.byteExpr (fun _ index => key (offset + index)) plane byte)

theorem initialWordsExpr_refines (key : Nat → BVExpr 8) (offset : Nat) (assign : BVExpr.Assignment) :
    (initialWordsExpr key offset).map (BVExpr.eval assign) =
      initialWords (fun i => (key i).eval assign) offset := by
  simp only [initialWordsExpr, initialWords, List.map_map, Function.comp_def,
    packWordExpr_refines, AesLayout.byteExpr_refines]

def keyExpr (key : Nat → BVExpr 8) : List (BVExpr 8) :=
  expr (initialWordsExpr key 0) (initialWordsExpr key 16)

def keyValue (key : Nat → BitVec 8) : List (BitVec 8) :=
  value (initialWords key 0) (initialWords key 16)

theorem keyExpr_refines (key : Nat → BVExpr 8) (assign : BVExpr.Assignment) :
    (keyExpr key).map (BVExpr.eval assign) = keyValue (fun i => (key i).eval assign) := by
  simp only [keyExpr, keyValue, expr_refines, initialWordsExpr_refines]

theorem compiled_keyExpr_correct (key : Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (keyExpr key).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (keyExpr key))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (keyExpr key))).vec.get index hi)) =
      (ByteCircuit.joinValue (keyValue (fun i => (key i).eval assign))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, keyExpr_refines]

end TlsMpc.Signal.AesKeySchedule
