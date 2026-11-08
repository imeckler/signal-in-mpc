import TlsMpc.Signal.PrivateBufferAppendSemantics
namespace TlsMpc.Signal.PrivateBuffer
open Semantics
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem encodeByte_eight (a b c d e f g h : Bool) :
    (encodeByte ByteAuth.concrete ([a,b,c,d,e,f,g,h].map mask) 1).toNat=value [a,b,c,d,e,f,g,h] := by
  have all : ∀ a b c d e f g h : Bool,
      (encodeByte ByteAuth.concrete ([a,b,c,d,e,f,g,h].map mask) 1).toNat=value [a,b,c,d,e,f,g,h] := by decide +kernel
  exact all a b c d e f g h

theorem encodeByte_value8 (bits : List Bool) (hb : bits.length=8) :
    (encodeByte ByteAuth.concrete (bits.map mask) 1).toNat=value bits := by
  obtain ⟨a,t0,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<bits.length)
  obtain ⟨b,t1,rfl⟩ := List.exists_cons_of_length_pos (by simp only [List.length_cons] at hb;omega : 0<t0.length)
  obtain ⟨c,t2,rfl⟩ := List.exists_cons_of_length_pos (by simp only [List.length_cons] at hb;omega : 0<t1.length)
  obtain ⟨d,t3,rfl⟩ := List.exists_cons_of_length_pos (by simp only [List.length_cons] at hb;omega : 0<t2.length)
  obtain ⟨e,t4,rfl⟩ := List.exists_cons_of_length_pos (by simp only [List.length_cons] at hb;omega : 0<t3.length)
  obtain ⟨f,t5,rfl⟩ := List.exists_cons_of_length_pos (by simp only [List.length_cons] at hb;omega : 0<t4.length)
  obtain ⟨g,t6,rfl⟩ := List.exists_cons_of_length_pos (by simp only [List.length_cons] at hb;omega : 0<t5.length)
  obtain ⟨h,t7,rfl⟩ := List.exists_cons_of_length_pos (by simp only [List.length_cons] at hb;omega : 0<t6.length)
  have empty : t7=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hb;omega)
  subst t7
  exact encodeByte_eight a b c d e f g h

theorem encodeByte_drop (bits : List Bool) : encodeByte ByteAuth.concrete (bits.map mask) 0 =
    encodeByte ByteAuth.concrete ((bits.drop 8).map mask) 1 := by
  simp only [encodeByte,Nat.reduceSub,Nat.reduceMul,Nat.zero_add,get_mask,List.getElem?_drop]

theorem encodeLowFold_take (bits : List Bool) (is : List Nat) (bound : ∀ i∈is,i<8) (acc : BitVec 8) :
    is.foldl (fun acc bit => ByteAuth.concrete.xor acc
      (ByteAuth.concrete.and (OpenResult.get ByteAuth.concrete (bits.map mask) bit) (ByteAuth.concrete.const (2^bit)))) acc =
    is.foldl (fun acc bit => ByteAuth.concrete.xor acc
      (ByteAuth.concrete.and (OpenResult.get ByteAuth.concrete ((bits.take 8).map mask) bit) (ByteAuth.concrete.const (2^bit)))) acc := by
  induction is generalizing acc with
  | nil => rfl
  | cons i is ih =>
    have hi : i<8 := bound i (by simp)
    have ht : ∀j∈is,j<8 := by intro j hj;exact bound j (by simp [hj])
    rw [List.foldl_cons,List.foldl_cons]
    have lookup : OpenResult.get ByteAuth.concrete (bits.map mask) i =
        OpenResult.get ByteAuth.concrete ((bits.take 8).map mask) i := by
      rw [get_mask,get_mask,List.getElem?_take_of_lt hi]
    rw [lookup]
    exact ih ht _

theorem encodeByte_take (bits : List Bool) : encodeByte ByteAuth.concrete (bits.map mask) 1 =
    encodeByte ByteAuth.concrete ((bits.take 8).map mask) 1 := by
  unfold encodeByte
  simp only [Nat.reduceSub,Nat.reduceMul,Nat.zero_add]
  exact encodeLowFold_take bits _ (by intro i hi;exact List.mem_range.mp hi) _

theorem byte_append_value (hi lo : BitVec 8) : (hi++lo).toNat=lo.toNat+256*hi.toNat := by
  rw [BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt (i:=8) lo.isLt hi.toNat]
  simp [Nat.shiftLeft_eq,Nat.add_comm,Nat.mul_comm]

theorem encodeLength_masks_value (bits : List Bool) (hb : bits.length=16) :
    ((encodeByte ByteAuth.concrete (bits.map mask) 0)++encodeByte ByteAuth.concrete (bits.map mask) 1).toNat=value bits := by
  have low : (bits.take 8).length=8 := by simp [hb]
  have high : (bits.drop 8).length=8 := by simp [hb]
  rw [byte_append_value,encodeByte_drop,encodeByte_take,encodeByte_value8 _ low,encodeByte_value8 _ high]
  have h := value_append (bits.take 8) (bits.drop 8)
  rw [List.take_append_drop,low] at h
  exact h.symm
theorem encodeLength_masks_eq (bits : List Bool) (hb : bits.length=16) :
    encodeLength ByteAuth.concrete (bits.map mask) =
      [BitVec.ofNat 8 (value bits/256),BitVec.ofNat 8 (value bits)] := by
  let high := encodeByte ByteAuth.concrete (bits.map mask) 0
  let low := encodeByte ByteAuth.concrete (bits.map mask) 1
  have h := encodeLength_masks_value bits hb
  rw [byte_append_value] at h
  change low.toNat+256*high.toNat=value bits at h
  have highBound : high.toNat<256 := high.isLt
  have lowBound : low.toNat<256 := low.isLt
  have bound := value_lt_pow bits
  rw [hb] at bound
  have hh : high=BitVec.ofNat 8 (value bits/256) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  have hl : low=BitVec.ofNat 8 (value bits) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  change [high,low]=_
  rw [hh,hl]

theorem encode_added_decoded_of_fits (capacity : Nat) (hc : capacity<65536) (hi lo hi' lo' : BitVec 8)
    (fits : (hi++lo).toNat+(hi'++lo').toNat≤capacity) :
    encodeLength ByteAuth.concrete (addLoop ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo])
      (decodeLength ByteAuth.concrete [hi',lo']) (List.range 16) (ByteAuth.concrete.const 0)).1 =
      [BitVec.ofNat 8 (((hi++lo).toNat+(hi'++lo').toNat)/256),BitVec.ofNat 8 ((hi++lo).toNat+(hi'++lo').toNat)] := by
  let left := byteBits lo++byteBits hi
  let right := byteBits lo'++byteBits hi'
  let pairs := (List.range 16).map (fun i => (left[i]?.getD false,right[i]?.getD false))
  let result := Semantics.add pairs false
  have hlen : result.1.length=16 := by simp only [result,add_length,pairs,List.length_map,List.length_range]
  have representation := addLoop_masks left right (List.range 16) false
  dsimp only [left,right] at representation
  rw [←decodeLength_masks hi lo,←decodeLength_masks hi' lo'] at representation
  change addLoop ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo])
    (decodeLength ByteAuth.concrete [hi',lo']) (List.range 16) (ByteAuth.concrete.const 0) = (result.1.map mask,mask result.2) at representation
  have numeric := add_decoded_value_of_fits capacity hc hi lo hi' lo' fits
  rw [representation] at numeric
  simp only [List.map_map,Function.comp_def,unmask_mask,List.map_id'] at numeric
  rw [representation,encodeLength_masks_eq _ hlen,numeric]

theorem output_zero (capacity : Nat) :
    output ByteAuth.concrete (zero ByteAuth.concrete capacity)=List.replicate (capacity+3) 0 := by
  have encoded : encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete 0)=[0,0] := by decide
  unfold output zero
  rw [encoded]
  rfl

end TlsMpc.Signal.PrivateBuffer
