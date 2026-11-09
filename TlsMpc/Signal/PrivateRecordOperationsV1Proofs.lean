import TlsMpc.Signal.PrivateRecordUpdateV1Proofs
import TlsMpc.Signal.PrivateRecordBindingV1
namespace TlsMpc.Signal.PrivateRecordOperationsV1Proofs
open PrivateRecordEncodingV1

theorem fold_map {A A' X X' : Type} (f : A → A') (g : X → X')
 (step : A → X → A) (step' : A' → X' → A')
 (h : ∀ acc x,f (step acc x)=step' (f acc) (g x)) (xs : List X) (initial : A) :
 f (xs.foldl step initial) = (xs.map g).foldl step' (f initial) := by
 induction xs generalizing initial with
 | nil => rfl
 | cons x xs ih => simp only [List.foldl_cons,List.map_cons,ih,h]

section
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha
 theorem update_scalarValue_map (tag : Nat) (nodes : List (Node B)) :
  (PrivateRecordUpdateV1.scalarValue a tag nodes).map f = PrivateRecordUpdateV1.scalarValue a' tag (nodes.map (Node.map f)) := by
  unfold PrivateRecordUpdateV1.scalarValue
  have hinit : List.replicate 4 (a'.const 0) = (List.replicate 4 (a.const 0)).map f := by simp only [List.map_replicate,ha.const]
  rw [hinit,List.foldl_map]
  symm
  apply List.foldl_hom (List.map f)
  intro old node
  cases node with
  | bytes => simp only [Node.map]
  | message => simp only [Node.map]
  | scalar t p e raw => simp only [Node.map];split <;> rfl
 theorem fieldPresence_map (tag : Nat) (nodes : List (Node B)) :
  f (PrivateRecordUpdateV1.fieldPresence a tag nodes)=PrivateRecordUpdateV1.fieldPresence a' tag (nodes.map (Node.map f)) := by
  unfold PrivateRecordUpdateV1.fieldPresence
  rw [← ha.const 0,List.foldl_map]
  symm
  apply List.foldl_hom f
  intro old node
  cases node <;> simp only [Node.map]
  all_goals split <;> rfl
end
section
variable {f : B → B'}
 theorem children_map (tag : Nat) (nodes : List (Node B)) :
  (PrivateRecordSnapshotV1.children tag nodes).map (Node.map f) = PrivateRecordSnapshotV1.children tag (nodes.map (Node.map f)) := by
  unfold PrivateRecordSnapshotV1.children
  rw [List.foldl_map]
  symm
  apply List.foldl_hom (List.map (Node.map f)) (init := ([] : List (Node B)))
  intro old node
  cases node with
  | bytes => simp only [Node.map]
  | scalar => simp only [Node.map]
  | message t p children => simp only [Node.map];split <;> rfl
 theorem bytesValue_map (tag : Nat) (nodes : List (Node B)) :
  (PrivateRecordSnapshotV1.bytesValue tag nodes).map f = PrivateRecordSnapshotV1.bytesValue tag (nodes.map (Node.map f)) := by
  unfold PrivateRecordSnapshotV1.bytesValue
  rw [List.foldl_map]
  symm
  apply List.foldl_hom (List.map f) (init := ([] : List B))
  intro old node
  cases node with
  | scalar => simp only [Node.map]
  | message => simp only [Node.map]
  | bytes t p e value => simp only [Node.map,PrivateBuffer.Buffer.map];split <;> rfl
 theorem snapshot_scalarValue_map (tag : Nat) (nodes : List (Node B)) :
  (PrivateRecordSnapshotV1.scalarValue tag nodes).map f = PrivateRecordSnapshotV1.scalarValue tag (nodes.map (Node.map f)) := by
  unfold PrivateRecordSnapshotV1.scalarValue
  rw [List.foldl_map]
  symm
  apply List.foldl_hom (List.map f) (init := ([] : List B))
  intro old node
  cases node with
  | bytes => simp only [Node.map]
  | message => simp only [Node.map]
  | scalar t p e raw => simp only [Node.map];split <;> rfl
end
end TlsMpc.Signal.PrivateRecordOperationsV1Proofs
