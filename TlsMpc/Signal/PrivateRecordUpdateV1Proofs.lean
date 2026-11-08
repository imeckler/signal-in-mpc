import TlsMpc.Signal.PrivateRecordUpdateV1
import TlsMpc.Signal.PrivateRecordEncodingV1Proofs
namespace TlsMpc.Signal.PrivateRecordUpdateV1
open PrivateRecordEncodingV1
section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha
 theorem chooseList_map (mask : B) (yes no : List B) :
  (chooseList a mask yes no).map f = chooseList a' (f mask) (yes.map f) (no.map f) := by
  simp [chooseList,List.map_zipWith,PrivateBuffer.choose_map ha]
 theorem putBytes_map (mask : B) (tag : Nat) (raw : List B) (nodes : List (Node B)) :
  (putBytes a mask tag raw nodes).map (Node.map f) = putBytes a' (f mask) tag (raw.map f) (nodes.map (Node.map f)) := by
  simp only [putBytes,alter,List.map_map,Function.comp_def]
  apply List.map_congr_left;intro node _
  cases node with
  | bytes t p empty value =>
   by_cases h : tag=t
   · simp only [if_pos h,Node.map]
     change Node.bytes t (f p) empty ((selectBuffer a mask (PrivateBuffer.fromPublic a value.data.length raw) value).map f) = _
     rw [selectBuffer_map ha,PrivateBuffer.fromPublic_map ha]
     simp only [PrivateBuffer.Buffer.map,List.length_map]
   · simp only [if_neg h,Node.map]
  | scalar t p empty value => by_cases h : tag=t <;> simp [h,Node.map]
  | message t p children => by_cases h : tag=t <;> simp [h,Node.map]
 theorem putScalar_map (mask : B) (tag : Nat) (raw : List B) (nodes : List (Node B)) :
  (putScalar a mask tag raw nodes).map (Node.map f) = putScalar a' (f mask) tag (raw.map f) (nodes.map (Node.map f)) := by
  simp only [putScalar,alter,List.map_map,Function.comp_def]
  apply List.map_congr_left;intro node _
  cases node <;> simp only [Node.map]
  all_goals split <;> simp only [Node.map,chooseList_map ha]
 theorem presence_map (mask value : B) (tag : Nat) (nodes : List (Node B)) :
  (presence a mask value tag nodes).map (Node.map f) = presence a' (f mask) (f value) tag (nodes.map (Node.map f)) := by
  simp only [presence,alter,List.map_map,Function.comp_def]
  apply List.map_congr_left;intro node _
  cases node <;> simp only [Node.map]
  all_goals split <;> simp only [Node.map,PrivateBuffer.choose_map ha]
end
 theorem nested_map {f : B → B'} (tag : Nat) (g : List (Node B) → List (Node B))
  (g' : List (Node B') → List (Node B'))
  (hg : ∀ ns,(g ns).map (Node.map f)=g' (ns.map (Node.map f))) (nodes : List (Node B)) :
  (nested tag g nodes).map (Node.map f)=nested tag g' (nodes.map (Node.map f)) := by
  simp only [nested,alter,List.map_map,Function.comp_def]
  apply List.map_congr_left;intro node _
  cases node <;> simp only [Node.map]
  all_goals split <;> simp only [Node.map,hg]
section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
 include ha
 theorem receiver_map (mask : B) (slot : List B) (node : Node B) :
  Node.map f (receiver a mask slot node) = receiver a' (f mask) (slot.map f) (Node.map f node) := by
  cases node with
  | bytes => simp [receiver,Node.map]
  | scalar => simp [receiver,Node.map]
  | message tag p children =>
   simp only [receiver,Node.map,PrivateBuffer.choose_map ha,OpenResult.get_map ha]
   congr 1
   rw [presence_map ha]
   have hn (ns : List (Node B)) := nested_map (f:=f) 3
    (presence a mask (a.const 255) 2 ∘ putScalar a mask 1 (slice slot 65 4) ∘ putBytes a mask 2 (slice slot 33 32))
    (presence a' (f mask) (a'.const 255) 2 ∘ putScalar a' (f mask) 1 ((slice slot 65 4).map f) ∘ putBytes a' (f mask) 2 ((slice slot 33 32).map f))
    (by intro ns; simp only [Function.comp_apply,presence_map ha,putScalar_map ha,putBytes_map ha,ha.const]) ns
   rw [hn]
   simp only [presence_map ha,putBytes_map ha,List.map_cons,ha.const,slice,List.map_take,List.map_drop]
end
end TlsMpc.Signal.PrivateRecordUpdateV1
