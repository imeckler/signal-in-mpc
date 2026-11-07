import Std
import Std.Tactic.BVDecide.Bitblast.BVExpr

/-!
Reusable bit-vector compiler: Lean's standard-library bitblaster already proves
bit-vector operations correct and caches shared subexpressions. This module
exports its DAG to a numeric circuit, without expanding shared nodes into trees.
No SAT solver, `bv_decide`, or native decision oracle is involved in these proofs.

Numeric nodes: [0] = false, [1, variable, width, bit] = input bit,
[2, left, leftInvert, right, rightInvert] = AND of the two signed references.
Bit indices within a variable are little endian. Output order is separate.
The JSON transport and generic MPC interpreter remain unverified.
-/

namespace TlsMpc.AigExport

open Std.Sat Std.Tactic.BVDecide
open scoped AIG

def encodeNode : AIG.Decl BVBit → List Nat
  | .false => [0]
  | .atom bit => [1, bit.var, bit.w, bit.idx.val]
  | .gate lhs rhs => [2, lhs.gate, lhs.invert.toNat, rhs.gate, rhs.invert.toNat]

def exportNodes (aig : AIG BVBit) : Array (List Nat) := aig.decls.map encodeNode

/-- Mathematical semantics of the numeric artifact. Invalid edges evaluate to
false; the external loader must reject malformed artifacts before execution. -/
def evalNode (nodes : Array (List Nat)) (input : Nat → Nat → Bool) (index : Nat) : Bool :=
  match nodes[index]? with
  | some [1, varId, _, bit] => input varId bit
  | some [2, left, linv, right, rinv] =>
      if _h : left < index ∧ right < index then
        (evalNode nodes input left ^^ (linv != 0)) &&
          (evalNode nodes input right ^^ (rinv != 0))
      else false
  | _ => false
termination_by index

def evalRef (nodes : Array (List Nat)) (input : Nat → Nat → Bool)
    (ref : Nat × Nat) : Bool := evalNode nodes input ref.1 ^^ (ref.2 != 0)

def exportRef {aig : AIG BVBit} (ref : AIG.Ref aig) : Nat × Nat := (ref.gate, ref.invert.toNat)

private theorem bool_nat (b : Bool) : (b.toNat != 0) = b := by cases b <;> rfl

/-- Local identity used by the unverified adapter's XOR recognition. This
does not verify the adapter's graph traversal or dead-node elimination. -/
theorem xor_pattern_correct (a b : Bool) :
    (!(a && b) && !(!a && !b)) = (a ^^ b) := by
  cases a <;> cases b <;> rfl

theorem exportNodes_correct (aig : AIG BVBit) (input : Nat → Nat → Bool)
    (index : Nat) (hi : index < aig.decls.size) :
    evalNode (exportNodes aig) input index =
      ⟦aig, ⟨index, false, hi⟩, fun bit => input bit.var bit.idx.val⟧ := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
      have get : (exportNodes aig)[index]? = some (encodeNode aig.decls[index]) := by
        simp [exportNodes, Array.getElem?_eq_getElem hi]
      cases hd : aig.decls[index] with
      | false =>
          rw [AIG.denote_idx_false hd]
          rw [evalNode, get, hd]
          rfl
      | atom bit =>
          rw [AIG.denote_idx_atom hd]
          rw [evalNode, get, hd]
          simp [encodeNode]
      | gate lhs rhs =>
          have bounds := aig.hdag hi hd
          have hl : lhs.gate < aig.decls.size := by omega
          have hr : rhs.gate < aig.decls.size := by omega
          rw [AIG.denote_idx_gate hd]
          rw [evalNode, get, hd]
          simp only [encodeNode, dif_pos bounds, bool_nat, Bool.xor_false]
          rw [ih lhs.gate bounds.1 hl, ih rhs.gate bounds.2 hr]
          simp [AIG.denote]

theorem exportRef_correct (aig : AIG BVBit) (ref : AIG.Ref aig)
    (input : Nat → Nat → Bool) :
    evalRef (exportNodes aig) input (exportRef ref) =
      ⟦aig, ref, fun bit => input bit.var bit.idx.val⟧ := by
  simp only [evalRef, exportRef, bool_nat, exportNodes_correct aig input ref.gate ref.hgate]
  simp [AIG.denote]

def compile (expr : BVExpr w) : AIG.RefVecEntry BVBit w :=
  -- This standard Lean primitive is definitionally the identity. Its runtime
  -- implementation shares equal objects before bitblasting, so repeated AES
  -- counter prefixes do not trigger exponential structural equality checks.
  -- Like native evaluation itself, the runtime implementation is trusted.
  (BVExpr.bitblast AIG.empty ⟨ShareCommon.shareCommon' expr, BVExpr.Cache.empty⟩).result.val

/-- Every bit of every compiled expression agrees with the executable BitVec
specification, for every assignment. Includes the numeric DAG export. -/
theorem compile_correct (expr : BVExpr w) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < w) :
    evalRef (exportNodes (compile expr).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (exportRef ((compile expr).vec.get index hi)) =
    (expr.eval assign).getLsbD index := by
  rw [exportRef_correct]
  exact BVExpr.denote_bitblast AIG.empty ⟨expr, BVExpr.Cache.empty⟩ assign
    (BVExpr.Cache.Inv_empty AIG.empty) index hi

end TlsMpc.AigExport
