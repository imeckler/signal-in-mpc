import ChatResponseReferenceWork.StreamingV1.MessageResume
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipSlice

/-- Actual generated driver key success establishes the full bounded field
context used by the source-field resume theorems; cache is unchanged. -/
theorem actual_known_key_ready (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : ActualInnerScanV1.prost.encoding.wire_type.WireType)
    (budget remaining : Nat) (boundary : ChildAtKey state before budget remaining)
    (positive : 0 < remaining) (fits : before.length-remaining < after.length)
    (known : (tag.val = 1 ∨ tag.val = 2) ∧ wire = .Varint ∨
      (tag.val = 3 ∨ tag.val = 4 ∨ tag.val = 5) ∧ wire = .LengthDelimited)
    (sourceSuccess : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,wire),after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      responseData (feed state consumed) = responseData state ∧
      ChildReady (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) ∧
      (feed state consumed).modes = lane (wireLane (wireNumber (ActualInnerResponseV1.toSkipWire wire))) ∧
      (feed state consumed).tag = BitVec.ofNat 64 tag.val ∧
      (feed state consumed).scalarKnown = (if tag.val = 1 ∨ tag.val = 2 then 255 else 0) ∧
      (feed state consumed).kinds = [0,if tag.val = 4 then 255 else 0,if tag.val = 3 then 255 else 0,if tag.val = 5 then 255 else 0] := by
  have ready := ready_of_key state before budget remaining boundary positive
  obtain ⟨consumed,span,data,nextValid,nextModes,nextPositions,nextValue,nextTag,nextKnown,nextKinds,nextInner,nextDepth,nextBudget,nextRemaining,nextSeen,nextFinished,nextUtf⟩ :=
    actual_driver_known_key_entry state before after tag wire budget remaining ready.budgetBound ready.remainingBound ready.budgetEnough ready.physical
      fits boundary.modes ready.positions ready.shape.kinds ready.shape.utf ready.value ready.valid ready.seen ready.finished ready.inner ready.depth
      ready.budgetCounter ready.childCounter known sourceSuccess
  have inputLength : before.length = consumed.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  have childPositive : 0 < remaining-consumed.length := by have := ready.physical; omega
  refine ⟨consumed,span,data,?_,nextModes,nextTag,nextKnown,nextKinds⟩
  exact ⟨⟨by have := ready.budgetBound; omega,by have := ready.remainingBound; omega,
      by have := ready.physical; omega,by have := ready.budgetEnough; omega,
      feed_shape state consumed ready.shape,nextPositions,nextValue,nextValid,nextSeen,nextFinished,nextDepth,nextBudget,nextRemaining⟩,
    childPositive,nextInner⟩

#print axioms actual_known_key_ready
end ChatResponseReference.StreamingV1
