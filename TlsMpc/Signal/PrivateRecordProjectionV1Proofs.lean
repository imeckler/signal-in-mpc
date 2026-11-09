import TlsMpc.Signal.PrivateRecordSnapshotV1Proofs
namespace TlsMpc.Signal.PrivateRecordSnapshotV1
open PrivateRecordEncodingV1
private theorem append_congr {x y z w : List A} (h : x=z) (k : y=w) : x++y=z++w := by rw [h,k]
section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha

 theorem project_map {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {g : V → V'}
    (ho : Word64.Hom o o' f g) (record : List (Node B)) :
    (project o a record).map f = project o' a' (record.map (Node.map f)) := by
  unfold project
  dsimp only
  simp only [List.map_append]
  have hlen := congrArg List.length (PrivateRecordOperationsV1Proofs.snapshot_scalarValue_map (f := f) 2 (children 2 (children 15 (children 1 record))))
  simp only [List.length_map] at hlen
  simp only [hlen,
    PrivateRecordOperationsV1Proofs.children_map,
    PrivateRecordOperationsV1Proofs.bytesValue_map,
    PrivateRecordOperationsV1Proofs.snapshot_scalarValue_map,
    List.length_map,List.map_drop,List.map_replicate,
    ha.const,Word64.bytes_map ho,ho.add,ho.pack,ho.const]
  repeat' first | rfl | apply append_congr
  · rw [← PrivateRecordOperationsV1Proofs.children_map]
    simp only [List.map_flatMap,List.flatMap_map]
    apply congrArg (fun h => (children 1 record).flatMap h)
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
  · simp only [← PrivateRecordOperationsV1Proofs.children_map,
      ← PrivateRecordOperationsV1Proofs.snapshot_scalarValue_map,List.length_map,
      List.map_append,List.map_replicate,ha.const]



end
open Std.Tactic.BVDecide
 theorem compiled_project_correct (nodes : List (Node (BVExpr 8)))
    (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement
      (project Word64.symbolic ByteAuth.symbolic nodes)
      (project Word64.concrete ByteAuth.concrete (nodes.map (Node.map (BVExpr.eval assign)))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,project_map (ByteAuth.evaluationHom assign) (Word64.evaluationHom assign)]
end TlsMpc.Signal.PrivateRecordSnapshotV1
