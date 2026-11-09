import ChatResponseReferenceWork.StreamingUnknownV1.GroupBudget
import ChatResponseReferenceWork.StreamingUnknownV1.FixedSource
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip

/-- Actual source group at its last recursion level decodes a non-end child key,
then rejects before touching that child's value. Schema-known child tags receive
exactly the same recursion-limit outcome as any other child tag. -/
theorem actual_unknown_group_limit_source (source : InnerResponseV1.Message) (parent child : U32)
    (before middle : Slice U8) (wire : LoopSupportSkip.encoding.wire_type.WireType)
    (unknown : 5 < parent.val) (notEnd : wire ≠ .EndGroup)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (child,wire),middle)) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source parent .StartGroup before ⟨1#u32⟩ =
      .ok (unchangedSkipResult source (.Err (decodeError .RecursionLimitReached),middle)) := by
  apply unknown_from_native_skip source parent .StartGroup before ⟨1#u32⟩ unknown
  simp only [ActualInnerResponseV1.toSkipWire]
  rw [start_group before parent (1#u32) (by decide)]
  apply group_loop_done
  exact group_child_after before middle middle parent child ⟨1#u32⟩ ⟨0#u32⟩ wire
    (.Err (decodeError .RecursionLimitReached)) notEnd keyRun
    (enter_recursion_value (1#u32) (0#u32) (by decide))
    (recursion_limit_first sliceBuf wire child middle)

#print axioms actual_unknown_group_limit_source
end ChatResponseReference.StreamingUnknownV1
