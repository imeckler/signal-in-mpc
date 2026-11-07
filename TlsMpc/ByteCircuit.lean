import TlsMpc.Sha256

/-! Byte-oriented bridge to the verified bit-vector compiler. Inputs are byte
variables, with index zero denoting the first byte on the wire. -/

namespace TlsMpc.ByteCircuit

open Std.Tactic.BVDecide

def inputBytes (start size : Nat) : List (BVExpr 8) :=
  (List.range size).map (fun i => .var (start + i))

def joinExpr : (bytes : List (BVExpr 8)) → BVExpr (8 * bytes.length)
  | [] => .const 0
  | byte :: rest => .append byte (joinExpr rest) (by simp; omega)

def joinValue : (bytes : List (BitVec 8)) → BitVec (8 * bytes.length)
  | [] => 0
  | byte :: rest => (byte ++ joinValue rest).cast (by simp; omega)

private theorem eval_append_toNat (left : BVExpr l) (right : BVExpr r)
    (h : w = l + r) (assign : BVExpr.Assignment) :
    ((BVExpr.append left right h).eval assign).toNat =
      (left.eval assign ++ right.eval assign).toNat := by
  cases h
  rfl

theorem joinExpr_correct (bytes : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    (joinExpr bytes).eval assign =
      (joinValue (bytes.map (BVExpr.eval assign))).cast (by simp) := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
      apply BitVec.eq_of_toNat_eq
      simp [joinExpr, eval_append_toNat, joinValue, BitVec.toNat_append, ih]

theorem compile_bytes_correct (bytes : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * bytes.length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (joinExpr bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (joinExpr bytes)).vec.get index hi)) =
    (joinValue (bytes.map (BVExpr.eval assign))).getLsbD index := by
  rw [AigExport.compile_correct, joinExpr_correct]
  rfl

theorem compiled_hash_correct (message : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (Sha256.hash Sha256.symbolic message).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (joinExpr (Sha256.hash Sha256.symbolic message))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef
        ((AigExport.compile (joinExpr (Sha256.hash Sha256.symbolic message))).vec.get index hi)) =
    (joinValue (Sha256.hash Sha256.concrete (message.map (BVExpr.eval assign)))).getLsbD index := by
  rw [compile_bytes_correct, Sha256.hash_refines]

theorem compiled_hmac_correct (key message : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (Sha256.hmac Sha256.symbolic key message).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (joinExpr (Sha256.hmac Sha256.symbolic key message))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef
        ((AigExport.compile (joinExpr (Sha256.hmac Sha256.symbolic key message))).vec.get index hi)) =
    (joinValue (Sha256.hmac Sha256.concrete
      (key.map (BVExpr.eval assign)) (message.map (BVExpr.eval assign)))).getLsbD index := by
  rw [compile_bytes_correct, Sha256.hmac_refines]

end TlsMpc.ByteCircuit
