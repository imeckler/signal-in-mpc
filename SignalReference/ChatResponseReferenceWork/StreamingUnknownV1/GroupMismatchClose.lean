import ChatResponseReferenceWork.StreamingUnknownV1.GroupEndMismatch
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip

/-- Actual mismatched group close exits with the precise native error/suffix and
rejects the full numeric input. The current parent slot is derived from the
witnessed recursive stack, including native keys past the private boundary. -/
theorem actual_group_mismatched_close (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (parent child count : U32) (older : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining (older++[parent]) count)
    (mismatch : child ≠ parent)
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (child,.EndGroup),after)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before =
      .ok (.done (.Err (decodeError .UnexpectedEndGroupTag),after)) ∧
    LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ =
      .ok (.Err (decodeError .UnexpectedEndGroupTag),after) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have step : LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before =
      .ok (.done (.Err (decodeError .UnexpectedEndGroupTag),after)) := by
    have result := group_end_after before after parent child ⟨count⟩ actual
    simpa only [groupClose,if_neg mismatch,if_false] using result
  have offset : (older++[parent]).length-1 = older.length := by simp only [List.length_append,List.length_cons,List.length_nil]; omega
  have parentSlot : state.stack[(older++[parent]).length-1]'(by have size : state.stack.length = 100 := ready.common.shape.stack; have := ready.bounded; omega) = BitVec.ofNat 64 parent.val := by
    have slot := ready.slots older.length (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
    simpa only [offset,List.getElem_append_right (by omega : older.length ≤ older.length),Nat.sub_self,List.getElem_cons_zero] using slot
  exact ⟨step,group_loop_done _ _ _ _ step,native_group_end_mismatch_reject state before after child parent (older++[parent]).length remaining
    ready.common.remainingBound ready.common.positive ready.common.physical ready.positive ready.bounded ready.common.shape.stack ready.depth parentSlot
    mismatch ready.modes ready.common.positions ready.common.value ready.common.inner ready.common.childCounter actual⟩

#print axioms actual_group_mismatched_close
end ChatResponseReference.StreamingUnknownV1
