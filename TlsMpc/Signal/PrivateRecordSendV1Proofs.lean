import TlsMpc.Signal.PrivateRecordOperationsV1Proofs
namespace TlsMpc.Signal.PrivateRecordSendV1
open PrivateRecordEncodingV1 PrivateRecordUpdateV1 PrivateRecordOperationsV1Proofs
section
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
 {f : B → B'} {fw : W → W'} (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include hs ha
 theorem applySend_map (record : List (Node B)) (result : List B) :
  (applySend s a record result).map (Node.map f) = applySend s' a' (record.map (Node.map f)) (result.map f) := by
  have hsender (mask : B) (ns : List (Node B)) :
   (nested 6 (nested 3 (putScalar a mask 1 (slice result 33 4) ∘ putBytes a mask 2 (slice result 1 32))) ns).map (Node.map f) =
   nested 6 (nested 3 (putScalar a' (f mask) 1 (slice (result.map f) 33 4) ∘ putBytes a' (f mask) 2 (slice (result.map f) 1 32))) (ns.map (Node.map f)) := by
   apply nested_map;intro ns
   apply nested_map;intro ns
   simp only [Function.comp_apply,putScalar_map ha,putBytes_map ha,slice,List.map_take,List.map_drop]
  have hpq (mask : B) (ns : List (Node B)) :
   (nested 15 (nested 2 (nested 3 (nested 1 (putScalar a mask 1 (slice result 69 4) ∘ putBytes a mask 2 (slice result 37 32))))) ns).map (Node.map f) =
   nested 15 (nested 2 (nested 3 (nested 1 (putScalar a' (f mask) 1 (slice (result.map f) 69 4) ∘ putBytes a' (f mask) 2 (slice (result.map f) 37 32))))) (ns.map (Node.map f)) := by
   apply nested_map;intro ns
   apply nested_map;intro ns
   apply nested_map;intro ns
   apply nested_map;intro ns
   simp only [Function.comp_apply,putScalar_map ha,putBytes_map ha,slice,List.map_take,List.map_drop]
  have hcurrent (mask : B) (ns : List (Node B)) :
   (nested 1 (fun current => nested 15 (nested 2 (nested 3 (nested 1 (putScalar a mask 1 (slice result 69 4) ∘ putBytes a mask 2 (slice result 37 32)))))
     (nested 6 (nested 3 (putScalar a mask 1 (slice result 33 4) ∘ putBytes a mask 2 (slice result 1 32))) current)) ns).map (Node.map f) =
   nested 1 (fun current => nested 15 (nested 2 (nested 3 (nested 1 (putScalar a' (f mask) 1 (slice (result.map f) 69 4) ∘ putBytes a' (f mask) 2 (slice (result.map f) 37 32)))))
     (nested 6 (nested 3 (putScalar a' (f mask) 1 (slice (result.map f) 33 4) ∘ putBytes a' (f mask) 2 (slice (result.map f) 1 32))) current)) (ns.map (Node.map f)) := by
   apply nested_map;intro ns
   rw [hpq,hsender]
  have hfinal (mask gate : B) (value : List B) (ns : List (Node B)) :
   (nested 3 (putScalar a mask 1 (List.replicate 4 (a.const 0)) ∘ putScalar a gate 2 value) ns).map (Node.map f) =
   nested 3 (putScalar a' (f mask) 1 (List.replicate 4 (a'.const 0)) ∘ putScalar a' (f gate) 2 (value.map f)) (ns.map (Node.map f)) := by
   apply nested_map;intro ns
   simp only [Function.comp_apply,putScalar_map ha,List.map_replicate,ha.const]
  simp only [applySend,List.length_map]
  split
  · rw [hfinal]
    simp only [Function.comp_apply,ha.and,ByteAuth.eqMask_map ha,ha.const,
      OpenResult.get_map ha,List.map_replicate,presence_map ha,hcurrent,
      update_scalarValue_map ha,children_map,ByteAuth.equalMask_map ha,
      List.map_cons,List.map_nil,hs.unpack,hs.add,hs.wordConst,Varint.pack_map hs ha]
  · rfl
end
end TlsMpc.Signal.PrivateRecordSendV1
