import TlsMpc.ByteAuth
import TlsMpc.Signal.OpenResult

/-! Tiny composition adapter: the first mask is the actual computed inner-send
status, not a caller's cryptographic assertion. The second comes from the
computed sealed-service result. Both must be255. This prevents a rejected
inner send's zero wire from becoming a valid outer request. -/
namespace TlsMpc.Signal.ServicePayload
open Std.Tactic.BVDecide

def compose (a : ByteAuth.Ops B) (previousStatus : B) (service : List B) : List B :=
  let valid := a.and (ByteAuth.eqMask a previousStatus (a.const 255))
    (ByteAuth.eqMask a (OpenResult.get a service 0) (a.const 255))
  let data := service.drop 1
  valid :: (ByteAuth.release a valid [a.const (data.length/256),a.const data.length] ++
    ByteAuth.release a valid data)

def fixed (a : ByteAuth.Ops B) (service : List B) : List B :=
  compose a (OpenResult.get a service 0) service

theorem compose_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'}
    (ha : ByteAuth.Hom a a' f) (previous : B) (service : List B) :
    (compose a previous service).map f = compose a' (f previous) (service.map f) := by
  simp only [compose,List.map_cons,List.map_append,List.map_drop,List.map_nil,List.length_drop,List.length_map,
    ha.and,ByteAuth.eqMask_map ha,OpenResult.get_map ha,ha.const,ByteAuth.release_map ha]

theorem compiled_compose_correct (previous : BVExpr 8) (service : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index<8*(compose ByteAuth.symbolic previous service).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (compose ByteAuth.symbolic previous service))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (compose ByteAuth.symbolic previous service))).vec.get index hi)) =
      (ByteCircuit.joinValue (compose ByteAuth.concrete (previous.eval assign)
        (service.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,compose_map (ByteAuth.evaluationHom assign)]
theorem fixed_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'}
    (ha : ByteAuth.Hom a a' f) (service : List B) :
    (fixed a service).map f = fixed a' (service.map f) := by
  simp only [fixed,compose_map ha,OpenResult.get_map ha]

theorem compiled_fixed_correct (service : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index<8*(fixed ByteAuth.symbolic service).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (fixed ByteAuth.symbolic service))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (fixed ByteAuth.symbolic service))).vec.get index hi)) =
      (ByteCircuit.joinValue (fixed ByteAuth.concrete (service.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,fixed_map (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.ServicePayload
