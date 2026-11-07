import TlsMpc.Aes
import TlsMpc.Signal.AesLayout

/-! Phase-zero fixslice MixColumns and the existing byte-oriented operation.
The representation is exactly the ordinary bitslice layout; no phase-change
invariant is assumed for the other fixslice variants. -/

namespace TlsMpc.Signal.AesLinear

open AesLayout Std.Tactic.BVDecide

def mixWords (a : Words (BitVec 64)) : Words (BitVec 64) :=
  let b0 := a.w0.rotateRight 16
  let b1 := a.w1.rotateRight 16
  let b2 := a.w2.rotateRight 16
  let b3 := a.w3.rotateRight 16
  let b4 := a.w4.rotateRight 16
  let b5 := a.w5.rotateRight 16
  let b6 := a.w6.rotateRight 16
  let b7 := a.w7.rotateRight 16
  let c0 := a.w0 ^^^ b0
  let c1 := a.w1 ^^^ b1
  let c2 := a.w2 ^^^ b2
  let c3 := a.w3 ^^^ b3
  let c4 := a.w4 ^^^ b4
  let c5 := a.w5 ^^^ b5
  let c6 := a.w6 ^^^ b6
  let c7 := a.w7 ^^^ b7
  ⟨b0 ^^^ c7 ^^^ c0.rotateRight 32,
   b1 ^^^ c0 ^^^ c7 ^^^ c1.rotateRight 32,
   b2 ^^^ c1 ^^^ c2.rotateRight 32,
   b3 ^^^ c2 ^^^ c7 ^^^ c3.rotateRight 32,
   b4 ^^^ c3 ^^^ c7 ^^^ c4.rotateRight 32,
   b5 ^^^ c4 ^^^ c5.rotateRight 32,
   b6 ^^^ c5 ^^^ c6.rotateRight 32,
   b7 ^^^ c6 ^^^ c7.rotateRight 32⟩

def blockBytes (input : Nat → Nat → B) (block : Nat) : List B :=
  (List.range 16).map (input block)

def mixBytes (o : Aes.Ops B) (input : Nat → Nat → B) (block index : Nat) : B :=
  Aes.get o (Aes.mixColumns o (blockBytes input block)) index

def expr (input : Nat → Nat → BVExpr 8) : List (BVExpr 8) :=
  AesLayout.expr (mixBytes Aes.symbolic input)

theorem mixBytes_map {a : Aes.Ops B} {b : Aes.Ops B'} {f : B → B'}
    (h : Aes.Hom a b f) (input : Nat → Nat → B) (block index : Nat) :
    f (mixBytes a input block index) =
      mixBytes b (fun block index => f (input block index)) block index := by
  simp only [mixBytes, Aes.get_map h, Aes.mixColumns_map h,
    blockBytes, List.map_map, Function.comp_def]

theorem expr_refines (input : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment) :
    (expr input).map (BVExpr.eval assign) =
      AesLayout.value (mixBytes Aes.concrete (fun block index => (input block index).eval assign)) := by
  rw [expr, AesLayout.expr_refines]
  congr 1
  funext block index
  exact mixBytes_map (Aes.evaluationHom assign) input block index

theorem compiled_expr_correct (input : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (expr input).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expr input))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (expr input))).vec.get index hi)) =
      (ByteCircuit.joinValue (AesLayout.value
        (mixBytes Aes.concrete (fun block index => (input block index).eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, expr_refines]

end TlsMpc.Signal.AesLinear
