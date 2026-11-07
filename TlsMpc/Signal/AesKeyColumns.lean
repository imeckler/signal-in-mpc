import TlsMpc.Signal.AesKeyCopy

/-! The column recurrence in the actual portable AES key schedule. Public
indices and rotation distances determine circuit shape; every word is secret. -/

namespace TlsMpc.Signal.AesKeyColumns

open Std.Tactic.BVDecide

structure Ops (W : Type) where
  lit : Nat → W
  xor : W → W → W
  and : W → W → W
  ror : Nat → W → W
  shl4 : W → W
  shl8 : W → W
  shl12 : W → W

def concrete : Ops (BitVec 64) where
  lit := BitVec.ofNat 64
  xor := (· ^^^ ·)
  and := (· &&& ·)
  ror := fun amount word => word.rotateRight amount
  shl4 := (· <<< 4)
  shl8 := (· <<< 8)
  shl12 := (· <<< 12)

def symbolic : Ops (BVExpr 64) where
  lit := fun n => .const (BitVec.ofNat 64 n)
  xor := fun a b => BvConstruct.bin a .xor b
  and := fun a b => BvConstruct.bin a .and b
  ror := fun amount word => BvConstruct.un (.rotateRight amount) word
  shl4 := fun word => .shiftLeft word (.const (4 : BitVec 4))
  shl8 := fun word => .shiftLeft word (.const (8 : BitVec 4))
  shl12 := fun word => .shiftLeft word (.const (12 : BitVec 4))

def column (o : Ops W) (rotation : Nat) (previous current : W) : W :=
  let word := o.xor previous (o.and (o.lit 0x000f000f000f000f) (o.ror rotation current))
  o.xor (o.xor (o.xor word
    (o.and (o.lit 0xfff0fff0fff0fff0) (o.shl4 word)))
    (o.and (o.lit 0xff00ff00ff00ff00) (o.shl8 word)))
    (o.and (o.lit 0xf000f000f000f000) (o.shl12 word))

def run (zero : W) (f : W → W → W) (offset distance : Nat) :
    Nat → Nat → List W → List W
  | _, 0, words => words
  | start, count + 1, words =>
    let pos :=  offset + start
    run zero f offset distance (start + 1) count
      (words.set pos (f (words[pos - distance]?.getD zero) (words[pos]?.getD zero)))

theorem run_map (f : W → W') (zero : W) (a : W → W → W) (b : W' → W' → W')
    (h : ∀ x y, f (a x y) = b (f x) (f y)) (offset distance start count : Nat) (words : List W) :
    (run zero a offset distance start count words).map f =
      run (f zero) b offset distance start count (words.map f) := by
  induction count generalizing start words with
  | zero => rfl
  | succ count ih =>
    simp only [run, ih, List.map_set, h, List.getElem?_map]
    cases words[offset + start - distance]? <;> cases words[offset + start]? <;> rfl

theorem column_refines (rotation : Nat) (previous current : BVExpr 64) (assign : BVExpr.Assignment) :
    (column symbolic rotation previous current).eval assign =
      column concrete rotation (previous.eval assign) (current.eval assign) := by
  simp [column, symbolic, concrete, BVExpr.eval_const, BVExpr.eval_shiftLeft, BVBinOp.eval, BVUnOp.eval]

def expr (offset distance rotation : Nat) (words : List (BVExpr 64)) : List (BVExpr 8) :=
  AesKeyCopy.encodeExpr (run (.const 0) (column symbolic rotation) offset distance 0 8 words)

def value (offset distance rotation : Nat) (words : List (BitVec 64)) : List (BitVec 8) :=
  AesKeyCopy.encode (run 0 (column concrete rotation) offset distance 0 8 words)

theorem expr_refines (offset distance rotation : Nat) (words : List (BVExpr 64))
    (assign : BVExpr.Assignment) :
    (expr offset distance rotation words).map (BVExpr.eval assign) =
      value offset distance rotation (words.map (BVExpr.eval assign)) := by
  simp only [expr, value, AesKeyCopy.encodeExpr_refines,
    run_map (BVExpr.eval assign) (.const 0) _ _ (fun _ _ => column_refines rotation _ _ assign),
    BVExpr.eval_const]

theorem compiled_expr_correct (offset distance rotation : Nat) (words : List (BVExpr 64))
    (assign : BVExpr.Assignment) (index : Nat) (hi : index < 8 * (expr offset distance rotation words).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (expr offset distance rotation words))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (expr offset distance rotation words))).vec.get index hi)) =
      (ByteCircuit.joinValue (value offset distance rotation (words.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, expr_refines]

end TlsMpc.Signal.AesKeyColumns
