import TlsMpc.Signal.PrivateRecordProjectionV1Proofs
namespace TlsMpc.Signal.PrivateRecordSnapshotV1
open PrivateRecordEncodingV1
private def mapRest (f : B → B') (value : List (Node B) × List B) :=
 (value.1.map (Node.map f),value.2.map f)
section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha
 theorem restore_map (fuel : Nat) (schema : List (Node B)) (raw : List B) :
    ((restore a fuel schema raw).1.map (Node.map f),(restore a fuel schema raw).2.map f) =
      restore a' fuel (schema.map (Node.map f)) (raw.map f) := by
  induction fuel generalizing schema raw with
  | zero => rfl
  | succ fuel ih =>
    unfold restore
    apply PrivateRecordOperationsV1Proofs.fold_map (mapRest f) (Node.map f)
    intro acc node
    rcases acc with ⟨ns,rest⟩
    cases node with
    | bytes tag p empty value =>
      have hlen : (value.map f).data.length = value.data.length := by simp only [PrivateBuffer.Buffer.map,List.length_map]
      simp only [mapRest,Node.map,List.length_map,OpenResult.get_map ha,List.map_drop,List.map_take,
        List.map_append,List.map_cons,List.map_nil,PrivateBuffer.fromWire_map ha,hlen]
    | scalar tag p defaults be =>
      simp only [mapRest,Node.map,List.length_map,OpenResult.get_map ha,List.map_drop,List.map_take,
        List.map_append,List.map_cons,List.map_nil]
    | message tag p children =>
      simp only [mapRest,Node.map,OpenResult.get_map ha,List.map_drop,List.map_append,List.map_cons,List.map_nil]
      have h := ih children (rest.drop 1)
      simp only [List.map_drop] at h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [Prod.fst,Prod.snd] at h1 h2
      rw [← h1,← h2]
end
end TlsMpc.Signal.PrivateRecordSnapshotV1
