import TlsMpc.ByteCircuit

/-! Byte-preserving Curve25519 scalar clamping. This applies the byte masks used
by libsignal's pinned curve25519-dalek dependency. It is not field reduction,
curve arithmetic, or a complete private-key decoder. The Aeneas refinement
of the actual dependency implementation lives in SignalReference. -/

namespace TlsMpc.Signal.Clamp

open Std.Tactic.BVDecide

def apply (band bor : B → B → B) (constant : Nat → B) (bytes : List B) : List B :=
  (bytes.set 0 (band (bytes[0]?.getD (constant 0)) (constant 248))).set 31
    (bor (band (bytes[31]?.getD (constant 0)) (constant 127)) (constant 64))

def value : List (BitVec 8) → List (BitVec 8) :=
  apply (· &&& ·) (· ||| ·) (BitVec.ofNat 8)

def symbolic : List (BVExpr 8) → List (BVExpr 8) :=
  apply (fun x y => .bin x .and y) (fun x y => .bin x .or y)
    (fun n => .const (BitVec.ofNat 8 n))

theorem map_getD (f : B → B') (bytes : List B) (i : Nat) (default : B) :
    ((bytes.map f)[i]?).getD (f default) = f (bytes[i]?.getD default) := by
  simp only [List.getElem?_map]
  cases bytes[i]? <;> rfl

theorem apply_map (f : B → B') (aAnd aOr : B → B → B) (aConst : Nat → B)
    (bAnd bOr : B' → B' → B') (bConst : Nat → B')
    (hAnd : ∀ x y, f (aAnd x y) = bAnd (f x) (f y))
    (hOr : ∀ x y, f (aOr x y) = bOr (f x) (f y))
    (hConst : ∀ n, f (aConst n) = bConst n) (bytes : List B) :
    (apply aAnd aOr aConst bytes).map f = apply bAnd bOr bConst (bytes.map f) := by
  simp only [apply, List.map_set, hAnd, hOr, ← hConst, map_getD]

theorem symbolic_refines (bytes : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    (symbolic bytes).map (BVExpr.eval assign) = value (bytes.map (BVExpr.eval assign)) := by
  exact apply_map (BVExpr.eval assign) _ _ _ _ _ _
    (by intros; rfl) (by intros; rfl) (by intros; rfl) bytes

theorem value_length (bytes : List (BitVec 8)) : (value bytes).length = bytes.length := by
  simp [value, apply]

theorem compiled_clamp_correct (bytes : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (symbolic bytes).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (symbolic bytes))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (symbolic bytes))).vec.get index hi)) =
    (ByteCircuit.joinValue (value (bytes.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, symbolic_refines]

end TlsMpc.Signal.Clamp
