import TlsMpc.Signal.PrivateBase64
import TlsMpc.Signal.PrivateBufferRecordSemantics

/-! Isolated balanced reduction; original producer remains unchanged. -/
namespace TlsMpc.Signal.PrivateBase64CountV2

namespace Reduce

def pairs (op : M → M → M) : List M → List M
  | x::y::rest => op x y :: pairs op rest
  | rest => rest

def balanced (op : M → M → M) (zero : M) : Nat → List M → M
  | 0,items => items.foldl op zero
  | fuel+1,items => balanced op zero fuel (pairs op items)

theorem fold_pairs (op : M → M → M)
    (assoc : ∀ x y z, op (op x y) z=op x (op y z)) (items : List M) (acc : M) :
    (pairs op items).foldl op acc=items.foldl op acc := by
  induction items using pairs.induct generalizing acc with
  | case1 x y rest ih => simp only [pairs,List.foldl_cons,ih,assoc]
  | case2 rest h => cases rest with
    | nil => rfl
    | cons x rest => cases rest with
      | nil => rfl
      | cons y rest => simp at h

theorem balanced_fold (op : M → M → M) (zero : M)
    (assoc : ∀ x y z, op (op x y) z=op x (op y z)) (fuel : Nat) (items : List M) :
    balanced op zero fuel items=items.foldl op zero := by
  induction fuel generalizing items with
  | zero => rfl
  | succ fuel ih => rw [balanced,ih,fold_pairs op assoc]

theorem pairs_map (op : M → M → M) (op' : N → N → N) (f : M → N)
    (hom : ∀ x y, f (op x y)=op' (f x) (f y)) (items : List M) :
    (pairs op items).map f=pairs op' (items.map f) := by
  induction items using pairs.induct with
  | case1 x y rest ih => simp only [pairs,List.map_cons,hom,ih]
  | case2 rest h => cases rest with
    | nil => rfl
    | cons x rest => cases rest with
      | nil => rfl
      | cons y rest => simp at h

theorem fold_map (op : M → M → M) (op' : N → N → N) (f : M → N)
    (hom : ∀ x y, f (op x y)=op' (f x) (f y)) (items : List M) (acc : M) :
    f (items.foldl op acc)=(items.map f).foldl op' (f acc) := by
  induction items generalizing acc with
  | nil => rfl
  | cons x rest ih => simp only [List.foldl_cons,List.map_cons,ih,hom]

theorem balanced_map (op : M → M → M) (op' : N → N → N) (f : M → N) (zero : M)
    (hom : ∀ x y, f (op x y)=op' (f x) (f y)) (fuel : Nat) (items : List M) :
    f (balanced op zero fuel items)=balanced op' (f zero) fuel (items.map f) := by
  induction fuel generalizing items with
  | zero => exact fold_map op op' f hom items zero
  | succ fuel ih => simp only [balanced,ih,pairs_map op op' f hom]

end Reduce

def add (a : ByteAuth.Ops B) (left right : List B) : List B :=
  (PrivateBuffer.addLoop a left right (List.range 16) (a.const 0)).1

def increment (a : ByteAuth.Ops B) (bits : List B) (index : Nat) : List B :=
  ByteAuth.release a (PrivateBuffer.less a (PrivateBuffer.publicLength a (3*index)) bits)
    (PrivateBuffer.publicLength a 4)

def count (a : ByteAuth.Ops B) (bits : List B) (indices : List Nat) (total : List B) : List B :=
  Reduce.balanced (add a) (PrivateBuffer.publicLength a 0) (Nat.log2 indices.length+1)
    (total::indices.map (increment a bits))

section Refinement
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (hom : ByteAuth.Hom a a' f)
include hom

theorem add_map (left right : List B) :
    (add a left right).map f=add a' (left.map f) (right.map f) := by
  have h:=congrArg Prod.fst (PrivateBuffer.addLoop_map hom left right (List.range 16) (a.const 0))
  simpa only [add,hom.const] using h

theorem increment_map (bits : List B) (index : Nat) :
    (increment a bits index).map f=increment a' (bits.map f) index := by
  simp only [increment,ByteAuth.release_map hom,PrivateBuffer.less_map hom,PrivateBuffer.publicLength_map hom]

theorem count_map (bits : List B) (indices : List Nat) (total : List B) :
    (count a bits indices total).map f=count a' (bits.map f) indices (total.map f) := by
  have h:=Reduce.balanced_map (add a) (add a') (List.map f) (PrivateBuffer.publicLength a 0)
    (fun x y => add_map hom x y) (Nat.log2 indices.length+1) (total::indices.map (increment a bits))
  rw [PrivateBuffer.publicLength_map hom] at h
  simpa only [count,List.map_cons,List.map_map,Function.comp_def,increment_map hom] using h
end Refinement

namespace Concrete
open PrivateBuffer PrivateBuffer.Semantics

abbrev Word := {bits : List Bool // bits.length=16}
def zero : Word := ⟨List.replicate 16 false,by decide⟩
def plus (left right : Word) : Word :=
  ⟨(Semantics.add ((List.range 16).map (fun i => (left.val[i]?.getD false,right.val[i]?.getD false))) false).1,
    by simp only [add_length,List.length_map,List.length_range]⟩
def bytes (word : Word) : List (BitVec 8) := word.val.map mask

theorem plus_value (left right : Word) :
    value (plus left right).val=(value left.val+value right.val)%65536 := by
  let pairs := (List.range 16).map (fun i => (left.val[i]?.getD false,right.val[i]?.getD false))
  have h:=add_value pairs false
  have li:=index_bits left.val
  have ri:=index_bits right.val
  rw [left.property] at li
  rw [right.property] at ri
  simp only [pairs,List.map_map,Function.comp_def,li,ri,Bool.toNat_false,Nat.add_zero,List.length_map,List.length_range] at h
  have bound:=value_lt_pow (plus left right).val
  rw [(plus left right).property] at bound
  change value (plus left right).val+65536*(Semantics.add pairs false).2.toNat=value left.val+value right.val at h
  omega

theorem plus_assoc (x y z : Word) : plus (plus x y) z=plus x (plus y z) := by
  apply Subtype.ext
  apply bits_value_injective
  · rw [(plus (plus x y) z).property,(plus x (plus y z)).property]
  · simp only [plus_value]
    rw [Nat.mod_add_mod,Nat.add_mod_mod,Nat.add_assoc]

theorem zero_value : value zero.val=0 := by decide

theorem zero_plus (x : Word) : plus zero x=x := by
  apply Subtype.ext
  apply bits_value_injective
  · rw [(plus zero x).property,x.property]
  · rw [plus_value,zero_value,Nat.zero_add,Nat.mod_eq_of_lt]
    have h:=value_lt_pow x.val
    simpa only [x.property] using h

theorem add_bytes (left right : Word) :
    add ByteAuth.concrete (bytes left) (bytes right)=bytes (plus left right) := by
  exact congrArg Prod.fst (addLoop_masks left.val right.val (List.range 16) false)

def publicWord (n : Nat) : Word :=
  ⟨byteBits (BitVec.ofNat 8 n)++byteBits (BitVec.ofNat 8 (n/256)),by simp [byteBits]⟩

theorem public_bytes (n : Nat) : bytes (publicWord n)=publicLength ByteAuth.concrete n := by
  unfold publicLength
  rw [decodeLength_masks]
  rfl

theorem zero_bytes : bytes zero=publicLength ByteAuth.concrete 0 := by decide

def incrementWord (bits : List Bool) (index : Nat) : Word :=
  if PrivateBuffer.less ByteAuth.concrete (publicLength ByteAuth.concrete (3*index)) (bits.map mask)==255
  then publicWord 4 else zero

theorem increment_bytes (bits : List Bool) (index : Nat) :
    increment ByteAuth.concrete (bits.map mask) index=bytes (incrementWord bits index) := by
  have h:=less_integer (publicWord (3*index)).val bits
  change PrivateBuffer.less ByteAuth.concrete (bytes (publicWord (3*index))) (bits.map mask)=_ at h
  rw [public_bytes] at h
  unfold increment incrementWord
  rw [h]
  split
  · simp only [BEq.rfl,ite_true]
    rw [public_bytes]
    decide
  · simp only [show ((0 : BitVec 8)==255)=false by decide]
    decide

 theorem count_fold (a : ByteAuth.Ops B) (bits : List B) (indices : List Nat) (total : List B) :
    PrivateBase64.count a bits indices total=indices.foldl (fun acc i => add a acc (increment a bits i)) total := by
  induction indices generalizing total with
  | nil => rfl
  | cons i rest ih => simp only [PrivateBase64.count,List.foldl_cons,ih,add,increment]

theorem count_equiv (bits : List Bool) (indices : List Nat) (total : Word) :
    count ByteAuth.concrete (bits.map mask) indices (bytes total)=
      PrivateBase64.count ByteAuth.concrete (bits.map mask) indices (bytes total) := by
  let words:=total::indices.map (incrementWord bits)
  have hom : ∀ x y, bytes (plus x y)=add ByteAuth.concrete (bytes x) (bytes y) := fun x y => (add_bytes x y).symm
  have mapped:=Reduce.balanced_map plus (add ByteAuth.concrete) bytes zero hom (Nat.log2 indices.length+1) words
  rw [zero_bytes] at mapped
  have wordmap : words.map bytes=bytes total::indices.map (increment ByteAuth.concrete (bits.map mask)) := by
    simp only [words,List.map_cons,List.map_map,Function.comp_def,←increment_bytes]
  rw [wordmap] at mapped
  unfold count
  rw [←mapped,Reduce.balanced_fold plus zero plus_assoc]
  rw [count_fold]
  simp only [words,List.foldl_cons,zero_plus]
  rw [Reduce.fold_map plus (add ByteAuth.concrete) bytes hom]
  simp only [List.map_map,Function.comp_def,increment_bytes]
  rw [List.foldl_map]

end Concrete
end TlsMpc.Signal.PrivateBase64CountV2
