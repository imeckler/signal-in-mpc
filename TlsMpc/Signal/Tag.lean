import TlsMpc.ByteCircuit

/-!
Secret byte-tag classification, used for the actual Signal ServiceIdKind and
CiphertextMessageType decoders. The output is an acceptance byte (0 or1) and
the input tag. This losslessly represents both a valid enum discriminant and
the rejected byte carried by Rust's TryFromReprError. It reveals neither byte.
-/

namespace TlsMpc.Signal.Tag

open Std.Tactic.BVDecide

def orBits (byte : BitVec 8) : Nat → BitVec 1
  | 0 => 0#1
  | n + 1 => orBits byte n ||| byte.extractLsb' n 1

def orBitsSymbolic (byte : BVExpr 8) : Nat → BVExpr 1
  | 0 => .const 0#1
  | n + 1 => .bin (orBitsSymbolic byte n) .or (.extract n 1 byte)

theorem orBits_refines (byte : BVExpr 8) (assign : BVExpr.Assignment) (n : Nat) :
    (orBitsSymbolic byte n).eval assign = orBits (byte.eval assign) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orBitsSymbolic, BVExpr.eval_bin, BVExpr.eval_extract,
      BVBinOp.eval, orBits, ih]

def accepts (byte : BitVec 8) : List Nat → BitVec 1
  | [] => 0#1
  | tag :: tags => (~~~orBits (byte ^^^ BitVec.ofNat 8 tag) 8) ||| accepts byte tags

def acceptsSymbolic (byte : BVExpr 8) : List Nat → BVExpr 1
  | [] => .const 0#1
  | tag :: tags => .bin
      (.un .not (orBitsSymbolic (.bin byte .xor (.const (BitVec.ofNat 8 tag))) 8))
      .or (acceptsSymbolic byte tags)

theorem accepts_refines (byte : BVExpr 8) (assign : BVExpr.Assignment) (tags : List Nat) :
    (acceptsSymbolic byte tags).eval assign = accepts (byte.eval assign) tags := by
  induction tags with
  | nil => rfl
  | cons tag tags ih =>
    simp only [acceptsSymbolic, BVExpr.eval_bin, BVExpr.eval_un, BVBinOp.eval,
      BVUnOp.eval, orBits_refines, BVExpr.eval_const, accepts, ih]

def value (tags : List Nat) (byte : BitVec 8) : List (BitVec 8) :=
  [0#7 ++ accepts byte tags, byte]

def symbolic (tags : List Nat) (byte : BVExpr 8) : List (BVExpr 8) :=
  [.append (.const 0#7) (acceptsSymbolic byte tags) (by decide), byte]

theorem symbolic_refines (tags : List Nat) (byte : BVExpr 8) (assign : BVExpr.Assignment) :
    (symbolic tags byte).map (BVExpr.eval assign) = value tags (byte.eval assign) := by
  simp only [symbolic, value, List.map_cons, List.map_nil, BVExpr.eval_append,
    BVExpr.eval_const, accepts_refines]

theorem compiled_classify_correct (tags : List Nat) (byte : BVExpr 8)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (symbolic tags byte).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (symbolic tags byte))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (symbolic tags byte))).vec.get index hi)) =
      (ByteCircuit.joinValue (value tags (byte.eval assign))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, symbolic_refines]

end TlsMpc.Signal.Tag
