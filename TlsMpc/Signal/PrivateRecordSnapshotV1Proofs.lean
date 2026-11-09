import TlsMpc.Signal.PrivateRecordSendV1Proofs
namespace TlsMpc.Signal.PrivateRecordSnapshotV1
open PrivateRecordEncodingV1 Std.Tactic.BVDecide
section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha
 theorem flatten_map (fuel : Nat) (nodes : List (Node B)) :
  (flatten a fuel nodes).map f = flatten a' fuel (nodes.map (Node.map f)) := by
  induction fuel generalizing nodes with
  | zero => rfl
  | succ fuel ih =>
   simp only [flatten,List.map_flatMap,List.flatMap_map,Function.comp_def]
   apply congrArg (fun g => nodes.flatMap g)
   funext node
   cases node <;> simp only [Node.map,List.map_cons,PrivateBuffer.output_map ha,ih]
end
 theorem compiled_applySend_correct (fuel : Nat) (nodes : List (Node (BVExpr 8)))
  (producer : List (BVExpr 8)) (assign : BVExpr.Assignment) :
  PrivateProtobuf.CircuitAgreement
   (flatten ByteAuth.symbolic fuel (PrivateRecordSendV1.applySend Sha256.symbolic ByteAuth.symbolic nodes producer))
   (flatten ByteAuth.concrete fuel (PrivateRecordSendV1.applySend Sha256.concrete ByteAuth.concrete
     (nodes.map (Node.map (BVExpr.eval assign))) (producer.map (BVExpr.eval assign)))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,flatten_map (ByteAuth.evaluationHom assign),
   PrivateRecordSendV1.applySend_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.PrivateRecordSnapshotV1
