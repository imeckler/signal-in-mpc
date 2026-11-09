import TlsMpc.Signal.PrivateRecordRestoreV1Proofs
namespace TlsMpc.Signal.PrivateRecordBindingV1
open PrivateRecordEncodingV1 PrivateRecordOperationsV1Proofs
section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha
 theorem all_map (xs : List B) : f (all a xs)=all a' (xs.map f) := by
  unfold all
  exact fold_map f f a.and a'.and ha.and xs (a.const 255) |>.trans (by rw [ha.const])
 theorem presentMask_map (tag : Nat) (nodes : List (Node B)) :
    f (presentMask a tag nodes)=presentMask a' tag (nodes.map (Node.map f)) := by
  simp only [presentMask,ByteAuth.eqMask_map ha,fieldPresence_map ha,ha.const]
 theorem bytesMask_map (tag width : Nat) (nodes : List (Node B)) :
    f (bytesMask a tag width nodes)=bytesMask a' tag width (nodes.map (Node.map f)) := by
  unfold bytesMask
  rw [← ha.const 0]
  apply fold_map f (Node.map f)
  intro old node
  cases node with
  | scalar => simp only [Node.map]
  | message => simp only [Node.map]
  | bytes t p empty value =>
    simp only [Node.map]
    split <;> simp only [all_map ha,List.map_cons,List.map_nil,ByteAuth.eqMask_map ha,
      ByteAuth.equalMask_map ha,ha.const,PrivateBuffer.publicLength_map ha,PrivateBuffer.Buffer.map]
 theorem absentBytesMask_map (tag : Nat) (nodes : List (Node B)) :
    f (absentBytesMask a tag nodes)=absentBytesMask a' tag (nodes.map (Node.map f)) := by
  unfold absentBytesMask
  rw [← ha.const 0]
  apply fold_map f (Node.map f)
  intro old node
  cases node with
  | scalar => simp only [Node.map]
  | message => simp only [Node.map]
  | bytes t p empty value =>
    simp only [Node.map]
    split <;> simp only [all_map ha,List.map_cons,List.map_nil,ByteAuth.eqMask_map ha,
      ByteAuth.equalMask_map ha,ha.const,PrivateBuffer.publicLength_map ha,PrivateBuffer.Buffer.map]
 theorem scalarMask_map (tag : Nat) (nodes : List (Node B)) :
    f (scalarMask a tag nodes)=scalarMask a' tag (nodes.map (Node.map f)) := by
  unfold scalarMask
  rw [← ha.const 0]
  apply fold_map f (Node.map f)
  intro old node
  cases node with
  | bytes => simp only [Node.map]
  | message => simp only [Node.map]
  | scalar t p defaults raw =>
    simp only [Node.map,List.length_map]
    split <;> simp only [ByteAuth.eqMask_map ha,ha.const]
    split <;> simp only [ByteAuth.eqMask_map ha,ha.const]
 theorem publicKeyMask_map (tag : Nat) (nodes : List (Node B)) :
    f (publicKeyMask a tag nodes)=publicKeyMask a' tag (nodes.map (Node.map f)) := by
  simp only [publicKeyMask,ha.and,bytesMask_map ha,ByteAuth.eqMask_map ha,
    OpenResult.get_map ha,bytesValue_map,ha.const]
 theorem canonicalNodes_map (fuel : Nat) (nodes : List (Node B)) :
    f (canonicalNodes a fuel nodes)=canonicalNodes a' fuel (nodes.map (Node.map f)) := by
  induction fuel generalizing nodes with
  | zero => exact ha.const 0
  | succ fuel ih =>
    simp only [canonicalNodes,all_map ha,List.map_map]
    congr 1
    apply List.map_congr_left
    intro node hn
    simp only [Function.comp_def]
    cases node with
    | bytes tag p empty value =>
      simp only [Node.map,ha.and,PrivateRecordEncodingV1.canonicalMask,
        ByteAuth.eqMask_map ha,ha.xor,ha.const,PrivateBuffer.Buffer.map]
    | scalar tag p defaults raw =>
      simp only [Node.map]
      split <;> simp only [PrivateRecordEncodingV1.canonicalMask,ByteAuth.eqMask_map ha,ha.xor,ha.const]
    | message tag p children =>
      simp only [Node.map,ha.and,PrivateRecordEncodingV1.canonicalMask,
        ByteAuth.eqMask_map ha,ha.xor,ha.const,ih]

 theorem coherence_map {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {fw : W → W'}
    (hs : Sha256.Hom s s' f fw)
    {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {fv : V → V'}
    (ho : Word64.Hom o o' f fv) (record : List (Node B)) (service : List B) :
    f (coherence s o a record service)=
      coherence s' o' a' (record.map (Node.map f)) (service.map f) := by
  have hlen : (PrivateRecordSnapshotV1.scalarValue 2 (PrivateRecordSnapshotV1.children 2
      (PrivateRecordSnapshotV1.children 15 (PrivateRecordSnapshotV1.children 1 record)))).length =
    (PrivateRecordSnapshotV1.scalarValue 2 (PrivateRecordSnapshotV1.children 2
      (PrivateRecordSnapshotV1.children 15 (PrivateRecordSnapshotV1.children 1 (record.map (Node.map f)))))).length := by
    simp only [← children_map,← snapshot_scalarValue_map,List.length_map]
  simp only [coherence,all_map ha,List.map_cons,List.map_nil,canonicalNodes_map ha,
    presentMask_map ha,publicKeyMask_map ha,bytesMask_map ha,scalarMask_map ha,absentBytesMask_map ha,
    ByteAuth.eqMask_map ha,ByteAuth.equalMask_map ha,OpenResult.get_map ha,
    update_scalarValue_map ha,fieldPresence_map ha,children_map,bytesValue_map,snapshot_scalarValue_map,
    ha.const,ha.and,ha.not,Word64.bytes_map ho,ho.add,ho.pack,ho.const,
    PrivateRecordUpdateV1.slice,List.map_take,List.map_drop,List.map_append,List.map_replicate,hlen]

 theorem bind_map {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {fw : W → W'}
    (hs : Sha256.Hom s s' f fw)
    {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {fv : V → V'}
    (ho : Word64.Hom o o' f fv) (record : List (Node B)) (service producer : List B) :
    ((bind s o a record service producer).1.map f,
      (bind s o a record service producer).2.map (Node.map f)) =
      bind s' o' a' (record.map (Node.map f)) (service.map f) (producer.map f) := by
  simp only [bind,List.length_map]
  split <;> simp only [PrivateRecordSendV1.applySend_map hs ha,
    PrivateRecordUpdateV1.chooseList_map ha,List.map_cons,List.map_append,List.map_drop,
    PrivateRecordUpdateV1.slice,List.map_take,ha.const,ha.and,
    ByteAuth.eqMask_map ha,OpenResult.get_map ha,coherence_map ha hs ho]

end
open Std.Tactic.BVDecide
 theorem compiled_bind_correct (fuel : Nat) (record : List (Node (BVExpr 8)))
    (service producer : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    let symbolic := bind Sha256.symbolic Word64.symbolic ByteAuth.symbolic record service producer
    let concrete := bind Sha256.concrete Word64.concrete ByteAuth.concrete
      (record.map (Node.map (BVExpr.eval assign))) (service.map (BVExpr.eval assign)) (producer.map (BVExpr.eval assign))
    PrivateProtobuf.CircuitAgreement
      (symbolic.1 ++ PrivateRecordSnapshotV1.project Word64.symbolic ByteAuth.symbolic symbolic.2 ++
        PrivateRecordSnapshotV1.flatten ByteAuth.symbolic fuel symbolic.2)
      (concrete.1 ++ PrivateRecordSnapshotV1.project Word64.concrete ByteAuth.concrete concrete.2 ++
        PrivateRecordSnapshotV1.flatten ByteAuth.concrete fuel concrete.2) assign := by
  dsimp only
  have hb := bind_map (ByteAuth.evaluationHom assign) (Sha256.evaluationHom assign)
    (Word64.evaluationHom assign) record service producer
  have h1 := congrArg Prod.fst hb
  have h2 := congrArg Prod.snd hb
  simp only [Prod.fst,Prod.snd] at h1 h2
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,List.map_append,List.map_append,
    PrivateRecordSnapshotV1.project_map (ByteAuth.evaluationHom assign) (Word64.evaluationHom assign),
    PrivateRecordSnapshotV1.flatten_map (ByteAuth.evaluationHom assign),h1,h2]
end TlsMpc.Signal.PrivateRecordBindingV1
