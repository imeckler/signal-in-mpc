import TlsMpc.ByteCircuit

/-! Public-index copying used inside the actual AES key schedule. All word
values remain secret; the circuit performs only rewiring. -/

namespace TlsMpc.Signal.AesKeyCopy

open Std.Tactic.BVDecide

def copyBackward (zero : W) (src dst : Nat) : Nat → List W → List W
  | 0, words => words
  | n + 1, words => copyBackward zero src dst n
      (words.set (dst + n) (words[src + n]?.getD zero))

theorem copyBackward_map (f : W → W') (zero : W) (src dst n : Nat) (words : List W) :
    (copyBackward zero src dst n words).map f =
      copyBackward (f zero) src dst n (words.map f) := by
  induction n generalizing words with
  | zero => rfl
  | succ n ih =>
    simp only [copyBackward, ih, List.map_set, List.getElem?_map]
    cases words[src + n]? <;> rfl

def encode (words : List (BitVec 64)) : List (BitVec 8) :=
  words.flatMap fun word => (List.range 8).map fun index => word.extractLsb' (8 * index) 8

def encodeExpr (words : List (BVExpr 64)) : List (BVExpr 8) :=
  words.flatMap fun word => (List.range 8).map fun index => BvConstruct.extract (8 * index) 8 word

def expr (src : Nat) (words : List (BVExpr 64)) : List (BVExpr 8) :=
  encodeExpr (copyBackward (.const 0) src (src + 8) 8 words)

def value (src : Nat) (words : List (BitVec 64)) : List (BitVec 8) :=
  encode (copyBackward 0 src (src + 8) 8 words)

theorem encodeExpr_refines (words : List (BVExpr 64)) (assign : BVExpr.Assignment) :
    (encodeExpr words).map (BVExpr.eval assign) = encode (words.map (BVExpr.eval assign)) := by
  simp [encodeExpr, encode, List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def, BvConstruct.eval_extract]

theorem expr_refines (src : Nat) (words : List (BVExpr 64)) (assign : BVExpr.Assignment) :
    (expr src words).map (BVExpr.eval assign) = value src (words.map (BVExpr.eval assign)) := by
  simp only [expr, value, encodeExpr_refines, copyBackward_map, BVExpr.eval_const]

theorem compiled_expr_correct (src : Nat) (words : List (BVExpr 64)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (expr src words).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expr src words))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (expr src words))).vec.get index hi)) =
      (ByteCircuit.joinValue (value src (words.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, expr_refines]

end TlsMpc.Signal.AesKeyCopy
