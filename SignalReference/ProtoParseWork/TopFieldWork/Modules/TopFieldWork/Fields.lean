import SkipPlanWork.Group

namespace LibSignalReference.Candidate.ProstTopField
open TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstSkipKey LibSignalReference.Candidate.ProstSkipPlan
set_option maxHeartbeats 500000

theorem select_field_full (yes no : ProtoParse.Field (BitVec 8) (BitVec 64)) :
    ProtoParse.selectField Word64.concrete ByteAuth.concrete 255 yes no = yes := by
  cases yes
  simp [ProtoParse.selectField,Word64.concrete,Unpad.chooseByte,ByteAuth.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and,BitVec.xor_assoc,BitVec.xor_self,BitVec.xor_zero,and_self]

theorem write_fields_length (enabled : BitVec 8) (tag : BitVec 64)
    (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) :
    (ProtoParse.writeFields Word64.concrete ByteAuth.concrete enabled tag payload fields).length = fields.length := by
  simp [ProtoParse.writeFields]

/-- A successful field replaces exactly its indexed metadata; a later duplicate
therefore overwrites the earlier record in this Lean parser. Actual Prost merge
wrappers still need their own reference bridge. -/
theorem write_fields_get (tag : BitVec 64)
    (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (i : Nat) (hi : i < fields.length) :
    (ProtoParse.writeFields Word64.concrete ByteAuth.concrete 255 tag payload fields)[i]'(by
      rw [write_fields_length]; exact hi) =
      if tag = BitVec.ofNat 64 (i+1) then
        ⟨255,payload.stop,payload.value,payload.value⟩ else fields[i] := by
  simp only [ProtoParse.writeFields,List.getElem_map,List.getElem_zipIdx,Nat.zero_add,word_eq_value]
  by_cases h : tag = BitVec.ofNat 64 (i+1)
  · have hc : tag = Word64.concrete.const (i+1) := h
    simp only [if_pos hc,if_pos h]
    change ProtoParse.selectField Word64.concrete ByteAuth.concrete 255 _ _ = _
    exact select_field_full _ _
  · have hc : tag ≠ Word64.concrete.const (i+1) := h
    simp only [if_neg hc,if_neg h]
    change ProtoParse.selectField Word64.concrete ByteAuth.concrete 0 _ _ = _
    exact select_field_zero _ _


theorem duplicate_last_value (first last : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) (i : Nat) (hi : i < fields.length) :
    (ProtoParse.writeFields Word64.concrete ByteAuth.concrete 255 (BitVec.ofNat 64 (i+1)) last
      (ProtoParse.writeFields Word64.concrete ByteAuth.concrete 255 (BitVec.ofNat 64 (i+1)) first fields))[i]'(by
        rw [write_fields_length,write_fields_length]; exact hi) =
      ⟨255,last.stop,last.value,last.value⟩ := by
  rw [write_fields_get]
  · exact if_pos rfl
  · rw [write_fields_length]; exact hi

#print axioms select_field_full
#print axioms write_fields_length
#print axioms write_fields_get
#print axioms duplicate_last_value
end LibSignalReference.Candidate.ProstTopField
