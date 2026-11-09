import ChatResponseReferenceWork.StreamingV1.ScalarResume
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual native body copy resumes the complete bounded key-loop invariant,
while retaining exact source content and copied payload events. -/
theorem actual_body_resumes (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (ready : ChildReady state before budget remaining)
    (physical : native.val ≤ after.length) (fits : native.val + (before.length-after.length) ≤ remaining)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,255,0,0])
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (4#u32) .LengthDelimited before ctx =
      .ok (.Ok (),{source with body := some ⟨ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val⟩},
        LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
      responseData (feed state consumed) = {responseData state with bodyPresent := 255,bodyLength := native.bv} ∧
      ChildAtKey (feed state consumed) (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val)
        (budget-consumed.length) (remaining-consumed.length) ∧
      ∃ header,
        consumed = header ++ contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val) ∧
        bodyTrace (feed state header) (contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val)) =
          (contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val)).map (fun byte => (255,0,0,byte)) := by
  obtain ⟨sourceResult,consumed,span,data,completeValid,finalModes,finalSkip,finalBudget,finalRemaining,finalInner,finalDepth,header,headerEq,events⟩ :=
    actual_body_field_scoped source ctx state before after native budget remaining ready.budgetBound ready.remainingBound ready.budgetEnough ready.physical
      physical fits modes ready.positions ready.value kinds ready.valid ready.seen ready.finished ready.inner ready.depth ready.budgetCounter ready.childCounter sourceSuccess
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
    finalPositions finalValue completeValid finalModes finalDepth finalRemaining finalInner,header,headerEq,events⟩

#print axioms actual_body_resumes
end ChatResponseReference.StreamingV1
