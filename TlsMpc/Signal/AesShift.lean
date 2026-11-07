import TlsMpc.Signal.AesMix

namespace TlsMpc.Signal.AesLinear

open AesLayout Std.Tactic.BVDecide

def mapWords (f : W → W') (words : Words W) : Words W' :=
  ⟨f words.w0, f words.w1, f words.w2, f words.w3,
    f words.w4, f words.w5, f words.w6, f words.w7⟩

def deltaWord (a : BitVec 64) (shift : Nat) (mask : BitVec 64) : BitVec 64 :=
  let t := (a ^^^ (a >>> shift)) &&& mask
  a ^^^ (t ^^^ (t <<< shift))

def shiftWord1 (word : BitVec 64) : BitVec 64 :=
  deltaWord (deltaWord word 8 0x00f000ff000f0000) 4 0x0f0f00000f0f0000

def shiftWord2 (word : BitVec 64) : BitVec 64 :=
  deltaWord word 8 0x00ff000000ff0000

def shiftWord3 (word : BitVec 64) : BitVec 64 :=
  deltaWord (deltaWord word 8 0x000f00ff00f00000) 4 0x0f0f00000f0f0000

def shiftBytes (o : Aes.Ops B) (input : Nat → Nat → B) (block index : Nat) : B :=
  Aes.get o (Aes.shiftRows o (blockBytes input block)) index

def shiftExpr (input : Nat → Nat → BVExpr 8) : List (BVExpr 8) :=
  AesLayout.expr (shiftBytes Aes.symbolic input)

def shiftBytesN (o : Aes.Ops B) : Nat → (Nat → Nat → B) → Nat → Nat → B
  | 0, input => input
  | n + 1, input => shiftBytes o (shiftBytesN o n input)

def shiftNExpr (times : Nat) (input : Nat → Nat → BVExpr 8) : List (BVExpr 8) :=
  AesLayout.expr (shiftBytesN Aes.symbolic times input)

theorem shiftBytes_map {a : Aes.Ops B} {b : Aes.Ops B'} {f : B → B'}
    (h : Aes.Hom a b f) (input : Nat → Nat → B) (block index : Nat) :
    f (shiftBytes a input block index) =
      shiftBytes b (fun block index => f (input block index)) block index := by
  simp only [shiftBytes, Aes.get_map h, Aes.shiftRows_map h,
    blockBytes, List.map_map, Function.comp_def]

theorem shiftExpr_refines (input : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment) :
    (shiftExpr input).map (BVExpr.eval assign) =
      AesLayout.value (shiftBytes Aes.concrete (fun block index => (input block index).eval assign)) := by
  rw [shiftExpr, AesLayout.expr_refines]
  congr 1
  funext block index
  exact shiftBytes_map (Aes.evaluationHom assign) input block index

theorem compiled_shiftExpr_correct (input : Nat → Nat → BVExpr 8) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (shiftExpr input).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (shiftExpr input))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (shiftExpr input))).vec.get index hi)) =
      (ByteCircuit.joinValue (AesLayout.value
        (shiftBytes Aes.concrete (fun block index => (input block index).eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, shiftExpr_refines]

theorem shiftBytesN_map {a : Aes.Ops B} {b : Aes.Ops B'} {f : B → B'}
    (h : Aes.Hom a b f) (times : Nat) (input : Nat → Nat → B) (block index : Nat) :
    f (shiftBytesN a times input block index) =
      shiftBytesN b times (fun block index => f (input block index)) block index := by
  induction times generalizing block index with
  | zero => rfl
  | succ n ih =>
    simp only [shiftBytesN, shiftBytes_map h]
    congr 1
    funext block index
    exact ih block index

theorem shiftNExpr_refines (times : Nat) (input : Nat → Nat → BVExpr 8)
    (assign : BVExpr.Assignment) :
    (shiftNExpr times input).map (BVExpr.eval assign) =
      AesLayout.value (shiftBytesN Aes.concrete times
        (fun block index => (input block index).eval assign)) := by
  rw [shiftNExpr, AesLayout.expr_refines]
  congr 1
  funext block index
  exact shiftBytesN_map (Aes.evaluationHom assign) times input block index

theorem compiled_shiftNExpr_correct (times : Nat) (input : Nat → Nat → BVExpr 8)
    (assign : BVExpr.Assignment) (index : Nat) (hi : index < 8 * (shiftNExpr times input).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (shiftNExpr times input))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef
        ((AigExport.compile (ByteCircuit.joinExpr (shiftNExpr times input))).vec.get index hi)) =
      (ByteCircuit.joinValue (AesLayout.value (shiftBytesN Aes.concrete times
        (fun block index => (input block index).eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, shiftNExpr_refines]

end TlsMpc.Signal.AesLinear
