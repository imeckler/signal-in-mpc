import ChatResponseReferenceWork.StreamingUnknownV1.FixedKeyEntry
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem actual_unknown_fixed_key_ready (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (tag : U32)
    (budget remaining : Nat) (wide : Bool) (boundary : ChildAtKey state before budget remaining)
    (cache : CacheAgrees outer source state) (positive : 0 < remaining) (unknownTag : 5 < tag.val)
    (fixedFits : (if wide then 8 else 4) + (before.length-after.length) ≤ remaining)
    (actual : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before =
      .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧ CacheAgrees outer source (feed state consumed) ∧
      ChildReady (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) ∧
      (feed state consumed).modes = lane 3 ∧ (feed state consumed).kinds = [0,0,0,0] ∧
      (feed state consumed).skip = BitVec.ofNat 64 (if wide then 8 else 4) ∧
      (if wide then 8 else 4) ≤ remaining-consumed.length := by
  have ready := ready_of_key state before budget remaining boundary positive
  have widthPositive : 0 < (if wide then 8 else 4) := by cases wide <;> decide
  have childFits : before.length-remaining < after.length := by have := ready.physical; omega
  have native := actual_driver_key_native before after tag _ actual
  have wireMap : ActualInnerResponseV1.toSkipWire (if wide then .SixtyFourBit else .ThirtyTwoBit) =
      (if wide then LoopSupportSkip.encoding.wire_type.WireType.SixtyFourBit else .ThirtyTwoBit) := by cases wide <;> rfl
  rw [wireMap] at native
  obtain ⟨consumed,span,data,nextValid,nextModes,nextPositions,nextValue,nextTag,nextKnown,nextKinds,nextInner,nextDepth,nextBudget,nextRemaining,nextSeen,nextFinished,nextUtf,nextSkip⟩ :=
    unknown_native_fixed_key_entry state before after tag _ budget remaining ready.budgetBound ready.remainingBound ready.budgetEnough ready.physical
      childFits boundary.modes ready.positions ready.shape.kinds ready.shape.utf ready.value ready.valid ready.seen ready.finished ready.inner ready.depth
      ready.budgetCounter ready.childCounter unknownTag wide rfl fixedFits native
  have inputLength : before.length = consumed.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  have countFits : (if wide then 8 else 4) ≤ remaining-consumed.length := by omega
  have childPositive : 0 < remaining-consumed.length := by omega
  have notThree : tag.val ≠ 3 := by omega
  have notFour : tag.val ≠ 4 := by omega
  have notFive : tag.val ≠ 5 := by omega
  simp only [if_neg notThree,if_neg notFour,if_neg notFive] at nextKinds
  have payloadModes : (feed state consumed).modes = lane 3 := by
    cases wide <;> exact nextModes
  refine ⟨consumed,span,data.trans cache,?_,payloadModes,nextKinds,nextSkip,countFits⟩
  exact ⟨⟨by have := ready.budgetBound; omega,by have := ready.remainingBound; omega,
      by have := ready.physical; omega,by have := ready.budgetEnough; omega,
      feed_shape state consumed ready.shape,nextPositions,nextValue,nextValid,nextSeen,nextFinished,nextDepth,nextBudget,nextRemaining⟩,
    childPositive,nextInner⟩

#print axioms actual_unknown_fixed_key_ready
end ChatResponseReference.StreamingUnknownV1
