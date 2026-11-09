import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
import ChatResponseReferenceWork.StreamingV1.NativePendingKey
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkipKey

/-- A pending scalar/fixed/length key at or past the private child end rejects
inside any active group, before parent suffix/padding can become a field value. -/
theorem group_pending_key_not_inside_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : WireType) (budget remaining : Nat) (parents : List U32) (count : U32)
    (ready : GroupLoopReady state before budget remaining parents count)
    (pending : wireNumber wire = 0 ∨ wireNumber wire = 1 ∨ wireNumber wire = 2 ∨ wireNumber wire = 5)
    (notInside : after.length ≤ before.length-remaining)
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  by_cases past : after.length < before.length-remaining
  · obtain ⟨native,run,_⟩ := native_key_success_varint before after tag wire actual
    exact native_varint_child_overrun_reject state before after native remaining 0 (by decide)
      ready.common.remainingBound ready.common.positive ready.common.physical past ready.modes ready.common.inner ready.common.childCounter run
  · exact native_pending_key_at_child_end state before after tag wire remaining ready.common.remainingBound
      (by have := ready.common.physical; omega) pending ready.modes ready.common.positions ready.common.value ready.common.inner ready.common.childCounter actual

#print axioms group_pending_key_not_inside_reject
end ChatResponseReference.StreamingUnknownV1
