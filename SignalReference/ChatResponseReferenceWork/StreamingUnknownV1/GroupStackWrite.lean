import ChatResponseReferenceWork.StreamingUnknownV1.GroupStackLookup
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1

/-- Actual masked stack write updates exactly its selected slot. All prior active
slots are retained; bounded indices exclude modular aliasing. -/
theorem group_stack_write_slot (stack : List (BitVec 64)) (index slot : Nat) (tag : BitVec 64)
    (size : stack.length ≤ 100) (indexBound : index < 100) (slotBound : slot < stack.length) :
    (TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete 255 (BitVec.ofNat 64 index) tag stack)[slot]'(by
      simp only [TlsChatResponse.writeStack,List.length_map,List.length_zipIdx]; exact slotBound) =
      if index = slot then tag else stack[slot] := by
  simp only [TlsChatResponse.writeStack,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
  have hotAnd (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  rw [hotAnd,stack_index_eq index slot (by omega) (by omega)]
  by_cases same : index = slot
  · simp only [if_pos same,Word64.select_accept]
  · simp only [if_neg same,Word64.select_reject]

#print axioms group_stack_write_slot
end ChatResponseReference.StreamingUnknownV1
