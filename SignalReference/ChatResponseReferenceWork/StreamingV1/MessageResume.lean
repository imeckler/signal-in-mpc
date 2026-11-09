import ChatResponseReferenceWork.StreamingV1.BodyResume
import ChatResponseReferenceWork.StreamingV1.MessageFieldScoped
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual accepted message String resumes the complete bounded key-loop
invariant, retaining exact source copied content and suffix. -/
theorem actual_message_resumes (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (ready : ChildReady state before budget remaining)
    (physical : native.val ≤ after.length) (fits : native.val + (before.length-after.length) ≤ remaining)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,0,255,0])
    (accepted : Utf8.accepts ((copiedString after native).val.map (fun byte => byte.bv)) = true)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (3#u32) .LengthDelimited before ctx =
      .ok (.Ok (),{source with message := some (copiedString after native)},
        LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
      responseData (feed state consumed) = {responseData state with messagePresent := 255} ∧
      ChildAtKey (feed state consumed) (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val)
        (budget-consumed.length) (remaining-consumed.length) := by
  obtain ⟨sourceResult,consumed,span,data,completeValid,finalModes,finalSkip,finalBudget,finalRemaining,finalInner,finalDepth⟩ :=
    actual_message_field_scoped source ctx state before after native budget remaining ready.budgetBound ready.remainingBound ready.budgetEnough ready.physical
      physical fits modes ready.positions ready.shape.utf ready.value kinds ready.valid ready.seen ready.finished ready.inner ready.depth ready.budgetCounter ready.childCounter sourceSuccess
  rw [messageFieldOutcome,if_pos accepted] at sourceResult
  rw [accepted] at completeValid
  obtain ⟨controlConsumed,controlSpan,finalPositions,finalValue⟩ := native_length_field_controls state before after native physical modes ready.positions ready.value
    ready.shape.kinds (by rw [kinds]; rfl) sourceSuccess
  have unique : controlConsumed = consumed := consumed_prefix_unique _ _ _ _ controlSpan span
  subst controlConsumed
  have droppedLength : (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val).length = after.length-native.val := by
    change (after.val.drop native.val).length = _
    rw [List.length_drop]
  have inputLength : before.length = consumed.length+(after.length-native.val) := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,droppedLength] using result
  exact ⟨sourceResult,consumed,span,data,child_boundary_after state before _ budget remaining ready consumed span (by omega)
    finalPositions finalValue completeValid finalModes finalDepth finalRemaining finalInner⟩

#print axioms actual_message_resumes
end ChatResponseReference.StreamingV1
