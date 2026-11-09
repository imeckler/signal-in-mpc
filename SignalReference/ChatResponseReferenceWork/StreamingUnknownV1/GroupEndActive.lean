import ChatResponseReferenceWork.StreamingUnknownV1.GroupStackLookup
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

/-- Closing group validation reads the real last active slot, including at depth
99. No unwitnessed table lookup or assumed acceptance mask is used. -/
theorem nested_end_active_slot (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (native : U64) (tag : U32) (depth : Nat)
    (positive : 0 < depth) (bound : depth ≤ 100) (shape : state.stack.length = 100)
    (depthEq : state.depth = BitVec.ofNat 64 depth)
    (decoded : coreDecoded state byte = native.bv) (accepted : keyResult native = .Ok (tag,.EndGroup)) :
    actualKeyGood state byte = Word64.eq Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 tag.val)
      (state.stack[depth-1]'(by omega)) := by
  rw [nested_end_native_key_guard state byte native tag (nested_depth_not_top state depth positive bound depthEq) decoded accepted]
  rw [depthEq]
  change Word64.eq Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 tag.val)
    (TlsChatResponse.lookup Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 depth-BitVec.ofNat 64 1) 0 state.stack) = _
  rw [BitVec.ofNat_sub_ofNat_of_le depth 1 (by decide) (by omega)]
  rw [group_stack_lookup state.stack 0 (depth-1) (by omega) (by omega) (by omega)]
  simp only [Nat.sub_zero]

/-- Exact source group-close decision against its numeric active-stack encoding.
Both matching acceptance and mismatched-end rejection remain represented. -/
theorem nested_end_parent_guard (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (native : U64) (tag parent : U32) (depth : Nat)
    (positive : 0 < depth) (bound : depth ≤ 100) (shape : state.stack.length = 100)
    (depthEq : state.depth = BitVec.ofNat 64 depth)
    (parentSlot : state.stack[depth-1]'(by omega) = BitVec.ofNat 64 parent.val)
    (decoded : coreDecoded state byte = native.bv) (accepted : keyResult native = .Ok (tag,.EndGroup)) :
    actualKeyGood state byte = if tag = parent then 255 else 0 := by
  rw [nested_end_active_slot state byte native tag depth positive bound shape depthEq decoded accepted,parentSlot]
  rw [word_eq_value]
  have equal : BitVec.ofNat 64 tag.val = BitVec.ofNat 64 parent.val ↔ tag = parent := by
    constructor
    · intro same
      apply UScalar.eq_of_val_eq
      have numeric := congrArg BitVec.toNat same
      have tagBound : tag.val < 2^64 := by have := tag.hBounds; scalar_tac
      have parentBound : parent.val < 2^64 := by have := parent.hBounds; scalar_tac
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt tagBound,Nat.mod_eq_of_lt parentBound] using numeric
    · intro same; rw [same]
  simp only [equal]

#print axioms nested_end_active_slot
#print axioms nested_end_parent_guard
end ChatResponseReference.StreamingUnknownV1
