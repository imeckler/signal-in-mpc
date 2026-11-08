import TlsMpc.TlsWebSocketUpgrade
namespace TlsMpc.TlsProviderGate
open Std.Tactic.BVDecide
def gate (a : ByteAuth.Ops B) (producer upstream : B) : B :=
  a.and (TlsWebSocketUpgrade.eq a producer 255) (TlsWebSocketUpgrade.eq a upstream 255)
theorem gate_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C}
    (h : ByteAuth.Hom a b f) (producer upstream : B) :
    f (gate a producer upstream) = gate b (f producer) (f upstream) := by
  simp only [gate,h.and,TlsWebSocketUpgrade.eq_map h]
theorem gate_value (producer upstream : BitVec 8) :
    gate ByteAuth.concrete producer upstream = if producer=255 ∧ upstream=255 then 255 else 0 := by
  unfold gate TlsWebSocketUpgrade.eq
  rw [ByteAuth.eqMask_value,ByteAuth.eqMask_value]
  change ((if producer=255 then (255:BitVec 8) else 0) &&& (if upstream=255 then (255:BitVec 8) else 0)) = _
  split <;> split <;> simp_all
theorem compiled_gate_correct (producer upstream : BVExpr 8) (assign : BVExpr.Assignment)
    (index : Nat) (bound : index<8*([gate ByteAuth.symbolic producer upstream]).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      [gate ByteAuth.symbolic producer upstream])).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        [gate ByteAuth.symbolic producer upstream])).vec.get index bound)) =
      (ByteCircuit.joinValue [gate ByteAuth.concrete (BVExpr.eval assign producer)
        (BVExpr.eval assign upstream)]).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct]
  simp only [List.map_cons,List.map_nil]
  have mapped := gate_map (ByteAuth.evaluationHom assign) producer upstream
  change BVExpr.eval assign (gate ByteAuth.symbolic producer upstream) = _ at mapped
  rw [mapped]
end TlsMpc.TlsProviderGate
