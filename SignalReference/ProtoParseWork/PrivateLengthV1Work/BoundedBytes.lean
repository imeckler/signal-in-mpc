import ProtoParseWork.PrivateLengthV1Work.Plan
import ProtoParseWork.PrivateLengthV1Work.Padding
namespace PrivateLengthV1.BoundedBytes
open TlsMpc TlsMpc.Signal

theorem bounded_length (o : Word64.Ops B W) (a : ByteAuth.Ops B) (ending : W) (bytes : List B) :
    (PrivateProtoParseV1.boundedBytes o a ending bytes).length = bytes.length := by
  simp [PrivateProtoParseV1.boundedBytes]

/-- Capacity padding is replaced before building decoder rows. Actual bytes,
including zero and malformed varints, remain unchanged inside the secret end. -/
theorem bounded_eq (bytes : List (BitVec 8)) (ending : Nat)
    (inside : ending ≤ bytes.length) (capacity : bytes.length ≤ 512) :
    PrivateProtoParseV1.boundedBytes Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending) bytes =
      bytes.take ending ++ List.replicate (bytes.length-ending) 128 := by
  apply List.ext_getElem
  · simp [bounded_length,List.length_take]; omega
  · intro i left right
    have hi : i < bytes.length := by simpa [bounded_length] using left
    have hword : i+1 < 2^64 := by omega
    have hend : ending < 2^64 := by omega
    simp only [PrivateProtoParseV1.boundedBytes,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
    change Unpad.chooseByte ByteAuth.concrete
      (Word64.concrete.ule (BitVec.ofNat 64 (i+1)) (BitVec.ofNat 64 ending)) bytes[i] 128 = _
    rw [Plan.nat_ule _ _ hword hend]
    by_cases before : i < ending
    · have le : i+1 ≤ ending := by omega
      simp only [if_pos le]
      rw [Unpad.chooseByte_accept]
      simp [List.getElem_append_left,List.getElem_take,before,Nat.min_eq_left inside]
    · have le : ¬i+1 ≤ ending := by omega
      have tail : (bytes.take ending).length ≤ i := by simp [Nat.min_eq_left inside]; omega
      simp only [if_neg le]
      rw [Unpad.chooseByte_reject,List.getElem_append_right tail]
      simp


#print axioms bounded_eq
end PrivateLengthV1.BoundedBytes
