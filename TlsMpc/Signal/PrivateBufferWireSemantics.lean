import TlsMpc.Signal.PrivateBufferLengthEncoding
namespace TlsMpc.Signal.PrivateBuffer

theorem appendWire_decoded (capacity : Nat) (hc : capacity<65536)
    (status hi lo status' hi' lo' : BitVec 8) (raw raw' : List (BitVec 8))
    (hlength : raw.length=capacity) (hrlength : raw'.length=capacity) :
    appendWire ByteAuth.concrete capacity (status::hi::lo::raw) (status'::hi'::lo'::raw') =
      if status=255 ∧ status'=255 ∧ (hi++lo).toNat+(hi'++lo').toNat≤capacity then
        255 :: ([BitVec.ofNat 8 (((hi++lo).toNat+(hi'++lo').toNat)/256),
          BitVec.ofNat 8 ((hi++lo).toNat+(hi'++lo').toNat)] ++
          (raw.take (hi++lo).toNat ++ raw'.take (hi'++lo').toNat ++
            List.replicate (capacity-((hi++lo).toNat+(hi'++lo').toNat)) 0))
      else List.replicate (capacity+3) 0 := by
  unfold appendWire
  rw [fromWire_decoded capacity hc status hi lo raw hlength,fromWire_decoded capacity hc status' hi' lo' raw' hrlength]
  by_cases left : status=255 ∧ (hi++lo).toNat≤capacity
  · rw [if_pos left]
    by_cases right : status'=255 ∧ (hi'++lo').toNat≤capacity
    · rw [if_pos right,append_decoded capacity hc hi lo hi' lo' raw raw' left.2 right.2]
      by_cases fits : (hi++lo).toNat+(hi'++lo').toNat≤capacity
      · rw [if_pos fits,if_pos ⟨left.1,right.1,fits⟩]
        unfold output
        rw [encode_added_decoded_of_fits capacity hc hi lo hi' lo' fits,
          joinedData_as_append ByteAuth.concrete capacity (hi++lo).toNat (hi'++lo').toNat raw raw'
            (by omega) (by omega) fits]
        rfl
      · rw [if_neg fits,output_zero]
        have bad : ¬(status=255 ∧ status'=255 ∧ (hi++lo).toNat+(hi'++lo').toNat≤capacity) := fun h => fits h.2.2
        rw [if_neg bad]
    · rw [if_neg right,append_zero_right,output_zero]
      have bad : ¬(status=255 ∧ status'=255 ∧ (hi++lo).toNat+(hi'++lo').toNat≤capacity) := by
        intro h
        apply right
        exact ⟨h.2.1,by omega⟩
      rw [if_neg bad]
  · rw [if_neg left,append_zero_left,output_zero]
    have bad : ¬(status=255 ∧ status'=255 ∧ (hi++lo).toNat+(hi'++lo').toNat≤capacity) := by
      intro h
      apply left
      exact ⟨h.1,by omega⟩
    rw [if_neg bad]

theorem appendWire_wrong_left (capacity : Nat) (left right : List (BitVec 8)) (hl : left.length≠capacity+3) :
    appendWire ByteAuth.concrete capacity left right=List.replicate (capacity+3) 0 := by
  unfold appendWire fromWire
  rw [if_neg hl,append_zero_left,output_zero]

theorem appendWire_wrong_right (capacity : Nat) (left right : List (BitVec 8)) (hr : right.length≠capacity+3) :
    appendWire ByteAuth.concrete capacity left right=List.replicate (capacity+3) 0 := by
  unfold appendWire fromWire
  rw [if_neg hr,append_zero_right,output_zero]

end TlsMpc.Signal.PrivateBuffer
