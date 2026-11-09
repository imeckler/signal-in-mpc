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
 theorem project_receivers_map (nodes : List (Node B)) :
    (nodes.flatMap fun node => match node with
      | .message 7 present ns =>
        present :: ByteAuth.release a present ((bytesValue 1 ns).drop 1 ++ bytesValue 2 (children 3 ns) ++ scalarValue 1 (children 3 ns))
      | _ => []).map f =
    (nodes.map (Node.map f)).flatMap (fun node => match node with
      | .message 7 present ns =>
        present :: ByteAuth.release a' present ((bytesValue 1 ns).drop 1 ++ bytesValue 2 (children 3 ns) ++ scalarValue 1 (children 3 ns))
      | _ => []) := by
  simp only [List.map_flatMap,List.flatMap_map]
  apply congrArg (fun h => nodes.flatMap h)
  funext node
  cases node with
  | bytes tag present empty value => simp only [Node.map,List.map_nil]
  | scalar tag present defaults raw => simp only [Node.map,List.map_nil]
  | message tag present ns =>
    cases tag with
    | zero => simp only [Node.map,List.map_nil]
    | succ tag =>
      cases tag with
      | zero => simp only [Node.map,List.map_nil]
      | succ tag =>
        cases tag with
        | zero => simp only [Node.map,List.map_nil]
        | succ tag =>
          cases tag with
          | zero => simp only [Node.map,List.map_nil]
          | succ tag =>
            cases tag with
            | zero => simp only [Node.map,List.map_nil]
            | succ tag =>
              cases tag with
              | zero => simp only [Node.map,List.map_nil]
              | succ tag =>
                cases tag with
                | zero => simp only [Node.map,List.map_nil]
                | succ tag =>
                  cases tag with
                  | zero => simp only [Node.map,List.map_cons,ByteAuth.release_map ha,
                    PrivateRecordOperationsV1Proofs.children_map,
                    PrivateRecordOperationsV1Proofs.bytesValue_map,
                    PrivateRecordOperationsV1Proofs.snapshot_scalarValue_map,
                    List.map_drop,List.map_append]
                  | succ tag => simp only [Node.map,List.map_nil]

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
