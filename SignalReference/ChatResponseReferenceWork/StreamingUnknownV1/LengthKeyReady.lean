import ChatResponseReferenceWork.StreamingUnknownV1.LengthKeyEntry
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Actual generated key success establishes the full unknown-length field entry
without assuming Core recognition/validity or a decoded table row. -/
theorem actual_unknown_length_key_ready (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (tag : U32)
    (budget remaining : Nat) (boundary : ChildAtKey state before budget remaining)
    (cache : CacheAgrees outer source state) (positive : 0 < remaining)
    (fits : before.length-remaining < after.length) (unknownTag : 5 < tag.val)
    (actual : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.LengthDelimited),after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      CacheAgrees outer source (feed state consumed) ∧
      ChildReady (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) ∧
      (feed state consumed).modes = lane 2 ∧ (feed state consumed).scalarKnown = 0 ∧
      (feed state consumed).kinds = [0,0,0,0] := by
  have ready := ready_of_key state before budget remaining boundary positive
  have native := actual_driver_key_native before after tag .LengthDelimited actual
  simp only [ActualInnerResponseV1.toSkipWire] at native
  obtain ⟨consumed,span,data,nextValid,nextModes,nextPositions,nextValue,nextTag,nextKnown,nextKinds,nextInner,nextDepth,nextBudget,nextRemaining,nextSeen,nextFinished,nextUtf⟩ :=
    unknown_native_length_key_entry state before after tag .LengthDelimited budget remaining ready.budgetBound ready.remainingBound ready.budgetEnough ready.physical
      fits boundary.modes ready.positions ready.shape.kinds ready.shape.utf ready.value ready.valid ready.seen ready.finished ready.inner ready.depth
      ready.budgetCounter ready.childCounter unknownTag rfl native
  have inputLength : before.length = consumed.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  have childPositive : 0 < remaining-consumed.length := by have := ready.physical; omega
  have notScalar : ¬(tag.val = 1 ∨ tag.val = 2) := by omega
  have notThree : tag.val ≠ 3 := by omega
  have notFour : tag.val ≠ 4 := by omega
  have notFive : tag.val ≠ 5 := by omega
  simp only [if_neg notScalar] at nextKnown
  simp only [if_neg notThree,if_neg notFour,if_neg notFive] at nextKinds
  refine ⟨consumed,span,data.trans cache,?_,nextModes,nextKnown,nextKinds⟩
  exact ⟨⟨by have := ready.budgetBound; omega,by have := ready.remainingBound; omega,
      by have := ready.physical; omega,by have := ready.budgetEnough; omega,
      feed_shape state consumed ready.shape,nextPositions,nextValue,nextValid,nextSeen,nextFinished,nextDepth,nextBudget,nextRemaining⟩,
    childPositive,nextInner⟩

#print axioms actual_unknown_length_key_ready
end ChatResponseReference.StreamingUnknownV1
