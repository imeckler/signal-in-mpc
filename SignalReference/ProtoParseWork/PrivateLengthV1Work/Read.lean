import TlsMpc.Signal.PrivateReadAtV1
import ProtoParseWork.PrivateLengthV1Work.Plan
namespace PrivateLengthV1.Read
open TlsMpc TlsMpc.Signal

theorem word_bytes (word : BitVec 64) :
    Word64.bytes Word64.concrete word = OpenResult.encodeLength ByteAuth.concrete word.toNat := by
  unfold Word64.bytes OpenResult.encodeLength
  apply List.map_congr_left
  intro index _
  have power : 256^(7-index) = 2^(8*(7-index)) := by rw [Nat.pow_mul]
  apply BitVec.eq_of_toNat_eq
  simp [Word64.concrete,ByteAuth.concrete,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,power]


theorem bounded_mask (ending width : Nat) (capacity : ending ≤ 512) (widthBound : width ≤ 512)
    (offset : BitVec 64) :
    ByteAuth.concrete.and (Word64.concrete.ule offset (BitVec.ofNat 64 ending))
      (Word64.concrete.ule (Word64.concrete.const width)
        (Word64.concrete.sub (BitVec.ofNat 64 ending) offset)) =
      if offset.toNat+width ≤ ending then 255 else 0 := by
  have small : ending < 2^64 := by omega
  rw [Word64.ule_value offset (BitVec.ofNat 64 ending)]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  by_cases before : offset.toNat ≤ ending
  · rw [if_pos before]
    have self : BitVec.ofNat 64 offset.toNat = offset := by
      apply BitVec.eq_of_toNat_eq
      simp [Nat.mod_eq_of_lt offset.isLt]
    have difference : Word64.concrete.sub (BitVec.ofNat 64 ending) offset =
        BitVec.ofNat 64 (ending-offset.toNat) := by
      have sum : BitVec.ofNat 64 ending = BitVec.ofNat 64 (ending-offset.toNat)+offset := by
        calc
          BitVec.ofNat 64 ending = BitVec.ofNat 64 (ending-offset.toNat)+BitVec.ofNat 64 offset.toNat := by
            rw [←BitVec.ofNat_add]
            congr 1; omega
          _ = BitVec.ofNat 64 (ending-offset.toNat)+offset := by rw [self]
      change BitVec.ofNat 64 ending - offset = _
      rw [sum,BitVec.add_sub_cancel]
    rw [difference]
    change ByteAuth.concrete.and 255
      (Word64.concrete.ule (BitVec.ofNat 64 width) (BitVec.ofNat 64 (ending-offset.toNat))) = _
    rw [Plan.nat_ule _ _ (by omega) (by omega)]
    by_cases fits : width ≤ ending-offset.toNat
    · rw [if_pos fits,if_pos (show offset.toNat+width ≤ ending by omega)]
      rfl
    · rw [if_neg fits,if_neg (show ¬offset.toNat+width ≤ ending by omega)]
      rfl
  · rw [if_neg before,if_neg (show ¬offset.toNat+width ≤ ending by omega)]
    simp [ByteAuth.concrete]


/-- Complete fixed-width read agreement for every shared cursor, including
out-of-bounds and wrapping-addition candidates. No field-validity premise. -/
theorem read_take (bytes : List (BitVec 8)) (ending width : Nat) (offset : BitVec 64)
    (within : ending ≤ bytes.length) (capacity : bytes.length ≤ 512) (widthBound : width ≤ 512) :
    PrivateReadAtV1.read Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending) width bytes offset =
    ReadAt.readCore ByteAuth.concrete width (bytes.take ending) (Word64.bytes Word64.concrete offset) := by
  unfold PrivateReadAtV1.read
  dsimp only
  rw [bounded_mask ending width (by omega) widthBound offset]
  simp only [word_bytes]
  have lengths : (ReadAt.readCore ByteAuth.concrete width bytes
      (OpenResult.encodeLength ByteAuth.concrete offset.toNat)).length =
      (ReadAt.fallback ByteAuth.concrete width (OpenResult.encodeLength ByteAuth.concrete offset.toNat)).length := by
    simp [ReadAt.readCore_length,ReadAt.fallback_length]
  by_cases fits : offset.toNat+width ≤ ending
  · rw [if_pos fits,Unpad.choose_accept _ _ lengths]
    rw [ReadAt.readCore_spec _ _ _ offset.isLt (by omega),
      ReadAt.readCore_spec _ _ _ offset.isLt (by simp only [List.length_take]; omega)]
    have fitsCapacity : offset.toNat+width ≤ bytes.length := by omega
    have fitsPrefix : offset.toNat+width ≤ (bytes.take ending).length := by
      simp only [List.length_take,Nat.min_eq_left within]; exact fits
    simp only [ReadAt.spec,if_pos fitsCapacity,if_pos fitsPrefix,ReadAt.row]
    have same : ((bytes.take ending).drop offset.toNat).take width = (bytes.drop offset.toNat).take width := by
      rw [List.drop_take,List.take_take,Nat.min_eq_left (show width ≤ ending-offset.toNat by omega)]
    rw [same]
  · rw [if_neg fits,Unpad.choose_reject _ _ lengths,
      ReadAt.readCore_spec _ _ _ offset.isLt (by simp only [List.length_take]; omega)]
    have noFit : ¬offset.toNat+width ≤ (bytes.take ending).length := by
      simpa only [List.length_take,Nat.min_eq_left within] using fits
    simp only [ReadAt.spec,if_neg noFit]

#print axioms word_bytes
#print axioms bounded_mask
#print axioms read_take
end PrivateLengthV1.Read
