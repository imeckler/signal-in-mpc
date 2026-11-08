import ProtoParseWork.PrivateLengthV1Work.Read
import ProtoParseWork.PrivateLengthV1Work.Scan
import TlsMpc.Signal.PrivateProtoParseV1Proofs
namespace PrivateLengthV1.Framing
open TlsMpc TlsMpc.Signal

theorem pack16 (high low : BitVec 8) :
    Word64.concrete.pack (List.replicate 6 (ByteAuth.concrete.const 0) ++ [high,low]) =
      (((0#8 ++ 0#8) ++ (0#8 ++ 0#8)) ++ ((0#8 ++ 0#8) ++ (high ++ low))) := rfl

theorem be16 (length : Nat) (bound : length ≤ 512) :
    Word64.concrete.pack (List.replicate 6 (ByteAuth.concrete.const 0) ++
      [BitVec.ofNat 8 (length/256),BitVec.ofNat 8 length]) = BitVec.ofNat 64 length := by
  rw [pack16]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append,BitVec.toNat_ofNat]
  have small : length < 2^64 := by omega
  have high : length/256 < 256 := by omega
  norm_num
  simp only [Nat.mod_eq_of_lt high]
  have low : length%256 < 2^8 := by omega
  rw [←Nat.shiftLeft_add_eq_or_of_lt low (length/256)]
  have reconstruct : ((length/256) <<< 8)+length%256 = length := by
    rw [Nat.shiftLeft_eq]
    norm_num
    omega
  rw [reconstruct]
  exact (Nat.mod_eq_of_lt small).symm

theorem framing_mask (capacity length : Nat) (within : length ≤ capacity) (bound : capacity ≤ 512) :
    ByteAuth.concrete.and (Word64.concrete.ule (Word64.concrete.const 9) (BitVec.ofNat 64 length))
      (Word64.concrete.ule (BitVec.ofNat 64 length) (Word64.concrete.const capacity)) =
      if 9 ≤ length then 255 else 0 := by
  change ByteAuth.concrete.and
    (Word64.concrete.ule (BitVec.ofNat 64 9) (BitVec.ofNat 64 length))
    (Word64.concrete.ule (BitVec.ofNat 64 length) (BitVec.ofNat 64 capacity)) = _
  rw [Plan.nat_ule _ _ (by omega) (by omega),Plan.nat_ule _ _ (by omega) (by omega),if_pos within]
  split <;> rfl

theorem body_length_word (capacity length : Nat) (within : length ≤ capacity) (bound : capacity ≤ 512) :
    Word64.concrete.select
      (ByteAuth.concrete.and (Word64.concrete.ule (Word64.concrete.const 9) (BitVec.ofNat 64 length))
        (Word64.concrete.ule (BitVec.ofNat 64 length) (Word64.concrete.const capacity)))
      (Word64.concrete.sub (BitVec.ofNat 64 length) (Word64.concrete.const 9)) (Word64.concrete.const 0) =
      BitVec.ofNat 64 (length-9) := by
  rw [framing_mask capacity length within bound]
  by_cases enough : 9 ≤ length
  · rw [if_pos enough,Word64.select_accept]
    have sum : BitVec.ofNat 64 length = BitVec.ofNat 64 (length-9)+BitVec.ofNat 64 9 := by
      rw [←BitVec.ofNat_add]
      congr 1; omega
    change BitVec.ofNat 64 length - BitVec.ofNat 64 9 = _
    rw [sum,BitVec.add_sub_cancel]
  · rw [if_neg enough,Word64.select_reject]
    have zero : length-9 = 0 := by omega
    rw [zero]
    rfl

theorem body_eq (wire : List B) : ProtoParse.body wire = (wire.drop 1).take (wire.length-9) := by
  simp [ProtoParse.body,MessageMac.content,List.drop_take,Nat.sub_sub]

theorem body_length (wire : List B) : (ProtoParse.body wire).length = wire.length-9 := by
  rw [body_eq]
  simp only [List.length_take,List.length_drop]
  omega

theorem body_take (wire : List B) (length : Nat) (within : length ≤ wire.length) :
    ProtoParse.body (wire.take length) = (ProtoParse.body wire).take (length-9) := by
  rw [body_eq,body_eq]
  simp only [List.length_take,Nat.min_eq_left within,List.drop_take,List.take_take]
  have shorter : length-9 ≤ length-1 := by omega
  have bounded : length-9 ≤ wire.length-9 := by omega
  rw [Nat.min_eq_left shorter,Nat.min_eq_left bounded]

theorem version_take (wire : List (BitVec 8)) (length : Nat) (positive : 0 < length) :
    Receive.versionMask ByteAuth.concrete (wire.take length) = Receive.versionMask ByteAuth.concrete wire := by
  have first : OpenResult.get ByteAuth.concrete (wire.take length) 0 = OpenResult.get ByteAuth.concrete wire 0 := by
    simp only [OpenResult.get,List.getElem?_take_of_lt positive]
  simp only [Receive.versionMask,first]

#print axioms be16
#print axioms body_length_word
#print axioms body_take
end PrivateLengthV1.Framing
