import TlsMpc.ByteCircuit

/-!
Fixed-width Signal service identifiers: a secret one-bit ACI/PNI discriminant
followed by the sixteen secret UUID bytes. The one-bit type rules out invalid
tags without opening the identifier kind. The reference bridge in
SignalReference checks this complete operation against pinned libsignal Rust.
-/

namespace TlsMpc.Signal.ServiceId

open Std.Tactic.BVDecide

def value (kind : BitVec 1) (uuid : List (BitVec 8)) : List (BitVec 8) :=
  (0#7 ++ kind) :: uuid

def symbolic (kind : BVExpr 1) (uuid : List (BVExpr 8)) : List (BVExpr 8) :=
  .append (.const 0#7) kind (by decide) :: uuid

theorem symbolic_refines (kind : BVExpr 1) (uuid : List (BVExpr 8))
    (assign : BVExpr.Assignment) :
    (symbolic kind uuid).map (BVExpr.eval assign) =
      value (kind.eval assign) (uuid.map (BVExpr.eval assign)) := by
  rfl

theorem compiled_encode_correct (kind : BVExpr 1) (uuid : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (symbolic kind uuid).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (symbolic kind uuid))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (symbolic kind uuid))).vec.get index hi)) =
      (ByteCircuit.joinValue (value (kind.eval assign)
        (uuid.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, symbolic_refines]

end TlsMpc.Signal.ServiceId
