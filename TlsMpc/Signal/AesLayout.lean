import TlsMpc.AesSbox
import TlsMpc.Signal.AesLayoutNetwork

/-! The 64 secret input bytes are four AES blocks, each in its original byte
order. The 64 output bytes are eight bitplanes, each a little-endian u64.
Only public indices select wires. No input bit is opened. -/

namespace TlsMpc.Signal.AesLayout

open Std.Tactic.BVDecide

def sourceBlock (lane : Nat) : Nat := lane % 4
def sourceByte (lane : Nat) : Nat := (lane / 4) % 4 * 4 + lane / 16

def byteValue (input : Nat → Nat → BitVec 8) (plane offset : Nat) : BitVec 8 :=
  AesSbox.packValue ((List.range 8).map (fun bit =>
    (input (sourceBlock (offset * 8 + bit)) (sourceByte (offset * 8 + bit))).extractLsb' plane 1))

def byteExpr (input : Nat → Nat → BVExpr 8) (plane offset : Nat) : BVExpr 8 :=
  AesSbox.packExpr ((List.range 8).map (fun bit =>
    BvConstruct.extract plane 1 (input (sourceBlock (offset * 8 + bit)) (sourceByte (offset * 8 + bit)))))

def value (input : Nat → Nat → BitVec 8) : List (BitVec 8) :=
  (List.range 64).map (fun index => byteValue input (index / 8) (index % 8))

def expr (input : Nat → Nat → BVExpr 8) : List (BVExpr 8) :=
  (List.range 64).map (fun index => byteExpr input (index / 8) (index % 8))

def encodeWords (words : Words (BitVec 64)) : List (BitVec 8) :=
  (List.range 64).map (fun index => (words.at (index / 8)).extractLsb' (index % 8 * 8) 8)

theorem byteExpr_refines (input : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (plane offset : Nat) :
    (byteExpr input plane offset).eval assign =
      byteValue (fun block index => (input block index).eval assign) plane offset := by
  simp only [byteExpr, byteValue, AesSbox.packExpr_refines, List.map_map,
    Function.comp_def, BvConstruct.eval_extract]

theorem expr_refines (input : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment) :
    (expr input).map (BVExpr.eval assign) =
      value (fun block index => (input block index).eval assign) := by
  simp only [expr, value, List.map_map, Function.comp_def, byteExpr_refines]

theorem compiled_expr_correct (input : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (expr input).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expr input))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (expr input))).vec.get index hi)) =
      (ByteCircuit.joinValue (value (fun block index => (input block index).eval assign))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, expr_refines]

end TlsMpc.Signal.AesLayout
