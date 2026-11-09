import ChatResponseReferenceWork.StreamingUnknownV1.GroupLimitSource
import ChatResponseReferenceWork.StreamingUnknownV1.GroupEndActive
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip LibSignalReference.Candidate.ProstSkipKey

/-- Exact actual default-group merger whose next real key is an end tag. Matching
and mismatched tags preserve their native result and exact post-key suffix. -/
theorem actual_unknown_group_close_source (source : InnerResponseV1.Message) (parent child count : U32)
    (before after : Slice U8) (unknown : 5 < parent.val) (positive : count ≠ 0#u32)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (child,.EndGroup),after)) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source parent .StartGroup before ⟨count⟩ =
      .ok (unchangedSkipResult source (groupClose parent child after)) := by
  apply unknown_from_native_skip source parent .StartGroup before ⟨count⟩ unknown
  simp only [ActualInnerResponseV1.toSkipWire]
  rw [start_group before parent count positive]
  apply group_loop_done
  exact group_end_after before after parent child ⟨count⟩ keyRun

/-- Source end-tag result and exact numeric active-parent guard agree, including
mismatched-tag rejection. Native prefix/terminal alignment and the recursive
stack/context invariant remain separate full-group composition obligations. -/
theorem actual_group_close_guard (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (native : U64) (parent child : U32) (after : Slice U8) (depth : Nat)
    (positive : 0 < depth) (bound : depth ≤ 100) (shape : state.stack.length = 100)
    (depthEq : state.depth = BitVec.ofNat 64 depth)
    (parentSlot : state.stack[depth-1]'(by omega) = BitVec.ofNat 64 parent.val)
    (decoded : coreDecoded state byte = native.bv) (accepted : keyResult native = .Ok (child,.EndGroup)) :
    actualKeyGood state byte =
      match (groupClose parent child after).1 with | .Ok _ => 255 | .Err _ => 0 := by
  rw [nested_end_parent_guard state byte native child parent depth positive bound shape depthEq parentSlot decoded accepted]
  unfold groupClose
  by_cases same : child = parent <;> simp only [same,if_true,if_false]

#print axioms actual_unknown_group_close_source
#print axioms actual_group_close_guard
end ChatResponseReference.StreamingUnknownV1
