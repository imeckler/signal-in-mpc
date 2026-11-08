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

theorem mask_and_mask (a b : Bool) : (mask a &&& mask b)=mask (a && b) := by
  cases a <;> cases b <;> decide

def canonical (bits : List (BitVec 8)) : Bool := bits.all (fun x => x==0 || x==255)

theorem canonical_mask (bits : List (BitVec 8)) :
    canonicalBits ByteAuth.concrete bits=mask (canonical bits) := by
  have check (x : BitVec 8) :
      ByteAuth.concrete.xor (ByteAuth.eqMask ByteAuth.concrete x 0) (ByteAuth.eqMask ByteAuth.concrete x 255)=
        mask (x==0 || x==255) := by
    rw [ByteAuth.eqMask_value,ByteAuth.eqMask_value]
    by_cases h0 : x=0
    · subst x;decide
    · by_cases h1 : x=255
      · subst x;decide
      · change x≠(0#8) at h0
        change x≠(255#8) at h1
        simp only [ByteAuth.concrete,mask]
        simp_all
  have fold (bits : List (BitVec 8)) (acc : Bool) :
      bits.foldl (fun total x => ByteAuth.concrete.and total
        (ByteAuth.concrete.xor (ByteAuth.eqMask ByteAuth.concrete x 0) (ByteAuth.eqMask ByteAuth.concrete x 255)))
        (mask acc)=mask (acc && canonical bits) := by
    induction bits generalizing acc with
    | nil => cases acc <;> rfl
    | cons x rest ih =>
      rw [List.foldl_cons,check]
      change rest.foldl _ (mask acc &&& mask (x==0 || x==255))=_
      rw [mask_and_mask,ih]
      simp only [canonical,List.all_cons,Bool.and_assoc]
  exact fold bits true

theorem canonical_representation (bits : List (BitVec 8)) (h : canonical bits=true) :
    bits=(bits.map unmask).map mask := by
  symm
  rw [List.map_map]
  calc
    _=bits.map id := by
      apply List.map_congr_left
      intro x hx
      have p : x==0 || x==255 := List.all_eq_true.mp h x hx
      have choices : x=0 ∨ x=255 := by simpa using p
      rcases choices with h0|h1 <;> subst x <;> decide
    _=bits := List.map_id' bits


theorem canonical_zeroes (n : Nat) : canonical (List.replicate n (0 : BitVec 8))=true := by
  simp [canonical]

theorem make_canonical (capacity : Nat) (bits raw : List (BitVec 8)) :
    canonical (make ByteAuth.concrete capacity bits raw).lengthBits=true := by
  unfold make
  split
  · unfold finish
    rw [canonical_mask]
    by_cases hc : canonical bits=true
    · rw [hc]
      have rep:=canonical_representation bits hc
      have order:=less_integer (publicWord capacity).val (bits.map unmask)
      change less ByteAuth.concrete (bytes (publicWord capacity)) ((bits.map unmask).map mask)=_ at order
      rw [public_bytes] at order
      rw [←rep] at order
      rw [order]
      split
      · change canonical (ByteAuth.release ByteAuth.concrete 0 bits)=true
        rw [ByteAuth.release_reject];exact canonical_zeroes bits.length
      · change canonical (ByteAuth.release ByteAuth.concrete 255 bits)=true
        rw [ByteAuth.release_accept];exact hc
    · have no : canonical bits=false := Bool.eq_false_iff.mpr hc
      rw [no]
      have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and (mask false) x=0 := BitVec.zero_and
      simp only [zeroAnd]
      change canonical (ByteAuth.release ByteAuth.concrete 0 bits)=true
      rw [ByteAuth.release_reject];exact canonical_zeroes bits.length
  · change canonical (publicLength ByteAuth.concrete 0)=true
    decide


theorem make_valid (capacity : Nat) (bits raw : List (BitVec 8)) :
    (make ByteAuth.concrete capacity bits raw).valid=0 ∨
    (make ByteAuth.concrete capacity bits raw).valid=255 := by
  unfold make
  split
  · unfold finish
    rw [canonical_mask]
    by_cases hc : canonical bits=true
    · rw [hc]
      have rep:=canonical_representation bits hc
      have order:=less_integer (publicWord capacity).val (bits.map unmask)
      change less ByteAuth.concrete (bytes (publicWord capacity)) ((bits.map unmask).map mask)=_ at order
      rw [public_bytes,←rep] at order
      rw [order]
      split
      · left;rfl
      · right;rfl
    · have no : canonical bits=false := Bool.eq_false_iff.mpr hc
      rw [no]
      left
      exact BitVec.zero_and
  · exact Or.inl rfl

theorem release_canonical (valid : BitVec 8) (bits : List (BitVec 8))
    (hv : valid=0 ∨ valid=255) (hc : canonical bits=true) :
    canonical (ByteAuth.release ByteAuth.concrete valid bits)=true := by
  rcases hv with h0|h1
  · rw [h0,ByteAuth.release_reject];exact canonical_zeroes bits.length
  · rw [h1,ByteAuth.release_accept];exact hc

theorem resize_canonical (capacity : Nat) (input : Buffer (BitVec 8)) :
    canonical (resize ByteAuth.concrete capacity input).lengthBits=true := by
  let raw:=(List.range capacity).map (OpenResult.get ByteAuth.concrete input.data)
  have hc:=make_canonical capacity input.lengthBits raw
  have hv:=make_valid capacity input.lengthBits raw
  unfold resize finish
  apply release_canonical
  · rw [ByteAuth.eqMask_value]
    split
    · have and255 (x : BitVec 8) : ByteAuth.concrete.and x 255=x := BitVec.and_allOnes
      simp only [and255]
      exact hv
    · left;exact BitVec.and_zero
  · exact hc

theorem normalized_count_equiv (capacity : Nat) (input : Buffer (BitVec 8)) (indices : List Nat) :
    count ByteAuth.concrete (resize ByteAuth.concrete capacity input).lengthBits indices
      (publicLength ByteAuth.concrete 0)=
    PrivateBase64.count ByteAuth.concrete (resize ByteAuth.concrete capacity input).lengthBits indices
      (publicLength ByteAuth.concrete 0) := by
  have rep:=canonical_representation _ (resize_canonical capacity input)
  rw [rep,←zero_bytes]
  exact count_equiv _ indices zero

end Concrete

def encode (a : ByteAuth.Ops B) (input : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let b := PrivateBuffer.resize a input.data.length input
  let groups := (input.data.length+2)/3
  let bits := count a b.lengthBits (List.range groups) (PrivateBuffer.publicLength a 0)
  let raw := (List.range groups).flatMap (PrivateBase64.group a b)
  PrivateProtobuf.gate a b.valid (PrivateBuffer.make a (4*groups) bits raw)

theorem encode_correct (input : PrivateBuffer.Buffer (BitVec 8)) :
    encode ByteAuth.concrete input=PrivateBase64.encode ByteAuth.concrete input := by
  unfold encode PrivateBase64.encode
  dsimp only
  rw [Concrete.normalized_count_equiv]

theorem encode_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'}
    (ha : ByteAuth.Hom a a' f) (input : PrivateBuffer.Buffer B) :
    (encode a input).map f=encode a' (input.map f) := by
  have normalized := PrivateBuffer.resize_map ha input.data.length input
  have bits := congrArg PrivateBuffer.Buffer.lengthBits normalized
  have valid := congrArg PrivateBuffer.Buffer.valid normalized
  change List.map f _ = _ at bits
  change f _ = _ at valid
  unfold encode
  rw [PrivateProtobuf.gate_map ha,PrivateBuffer.make_map ha,count_map ha]
  simp only [PrivateBuffer.publicLength_map ha,List.map_flatMap,PrivateBase64.group_map ha,normalized]
  rw [bits,valid]
  simp only [PrivateBuffer.Buffer.map,List.length_map]

end TlsMpc.Signal.PrivateBase64CountV2
