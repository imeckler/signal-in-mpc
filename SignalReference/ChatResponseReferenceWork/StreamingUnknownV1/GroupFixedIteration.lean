import ChatResponseReferenceWork.StreamingUnknownV1.GroupFixedKeyEntry
import ChatResponseReferenceWork.StreamingUnknownV1.GroupOpaqueComplete
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLeafBoundary
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual fixed32/fixed64 group-loop key/context/skip iteration composes with
complete numeric private counters/cache/active parent stack and source context. -/
theorem actual_group_fixed_loop_step (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (parent tag count : U32) (parents : List U32) (budget remaining : Nat) (wide : Bool)
    (ready : GroupLoopReady state before budget remaining parents count)
    (cache : CacheAgrees outer source state) (depthBound : parents.length ≤ 98)
    (strictFit : (if wide then 8 else 4) + (before.length-middle.length) < remaining)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.cont (drop middle (if wide then 8 else 4))) ∧
    ∃ consumed,
      contents before = consumed ++ contents (drop middle (if wide then 8 else 4)) ∧ CacheAgrees outer source (feed state consumed) ∧
      GroupLoopReady (feed state consumed) (drop middle (if wide then 8 else 4)) (budget-consumed.length) (remaining-consumed.length) parents count := by
  have widthPositive : 0 < (if wide then 8 else 4) := by cases wide <;> decide
  have keyFits : before.length-remaining < middle.length := by have := ready.common.physical; omega
  obtain ⟨keyConsumed,keySpan,keyData,keyValid,keyModes,keyPositions,keyValue,keyTag,keyKnown,keyKinds,keyInner,keyDepth,keyStack,keyBudget,keyRemaining,keySeen,keyFinished,keyUtf,keySkip⟩ :=
    nested_native_fixed_key_entry state before middle tag (if wide then .SixtyFourBit else .ThirtyTwoBit) parents.length budget remaining
      ready.common.budgetBound ready.common.remainingBound ready.common.budgetEnough ready.common.physical keyFits ready.modes ready.common.positions
      ready.common.shape.kinds ready.common.shape.utf ready.common.value ready.common.valid ready.common.seen ready.common.finished ready.common.inner ready.depth
      ready.common.budgetCounter ready.common.childCounter ready.positive depthBound wide rfl (by omega) keyRun
  have keyMode : (feed state keyConsumed).modes = lane 3 := by cases wide <;> exact keyModes
  have keyLength : before.length = keyConsumed.length+middle.length := by
    have result := congrArg List.length keySpan
    simpa only [contents,List.length_map,List.length_append] using result
  have keyShape := feed_shape state keyConsumed
    (show StateShape state from ⟨ready.common.shape.modes,ready.common.shape.positions,ready.common.shape.kinds,ready.common.shape.stack,ready.common.shape.utf⟩)
  have erasedShape : StateShape (eraseGroupDepth (feed state keyConsumed)) := ⟨keyShape.modes,keyShape.positions,keyShape.kinds,keyShape.stack,keyShape.utf⟩
  have fieldReady : ChildReady (eraseGroupDepth (feed state keyConsumed)) middle (budget-keyConsumed.length) (remaining-keyConsumed.length) :=
    ⟨⟨by have := ready.common.budgetBound; omega,by have := ready.common.remainingBound; omega,
      by have := ready.common.physical; omega,by have := ready.common.budgetEnough; omega,
      erasedShape,keyPositions,keyValue,keyValid,keySeen,keyFinished,rfl,keyBudget,keyRemaining⟩,
      by have := ready.common.physical; omega,keyInner⟩
  have physical : (if wide then 8 else 4) ≤ middle.length := by have := ready.common.physical; omega
  have countPositive : 1 < count.val := by have := ready.context; omega
  let child := U32.ofNatCore (count.val-1) (by have h := count.hmax; scalar_tac)
  have decremented : count.val = child.val+1 := by change count.val = (count.val-1)+1; omega
  have childPositive : child ≠ 0#u32 := by
    intro zero
    have numeric := congrArg UScalar.val zero
    change child.val = 0 at numeric
    omega
  have childRun : LoopSupportSkip.encoding.skip_field sliceBuf (if wide then .SixtyFourBit else .ThirtyTwoBit) tag middle ⟨child⟩ =
      .ok (.Ok (),drop middle (if wide then 8 else 4)) := by
    cases wide with
    | false =>
      change LoopSupportSkip.encoding.skip_field sliceBuf .ThirtyTwoBit tag middle ⟨child⟩ = .ok (.Ok (),drop middle 4)
      have fit : 4 ≤ middle.length := physical
      rw [fixed32_reference middle tag child childPositive]
      simp only [fixedResult,if_neg (by omega : ¬middle.length < 4)]
    | true =>
      change LoopSupportSkip.encoding.skip_field sliceBuf .SixtyFourBit tag middle ⟨child⟩ = .ok (.Ok (),drop middle 8)
      have fit : 8 ≤ middle.length := physical
      rw [fixed64_reference middle tag child childPositive]
      simp only [fixedResult,if_neg (by omega : ¬middle.length < 8)]
  have sourceStep : LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.cont (drop middle (if wide then 8 else 4))) :=
    group_child_after before middle _ parent tag ⟨count⟩ ⟨child⟩ _ (.Ok ())
      (by cases wide <;> intro same <;> cases same) keyRun (enter_recursion_value count child decremented) childRun
  refine ⟨sourceStep,?_⟩
  obtain ⟨fieldConsumed,fieldBytes,fieldSpan,fieldCache,fieldModes,fieldPositions,fieldValue,fieldValid,fieldDepth,fieldStack,fieldRemaining,fieldInner⟩ :=
    group_opaque_value_complete outer source (feed state keyConsumed) middle (if wide then 8 else 4) (budget-keyConsumed.length) (remaining-keyConsumed.length)
      fieldReady (keyData.trans cache) widthPositive (by omega) keyMode keyKinds keySkip
  have fieldLength : fieldConsumed.length = (if wide then 8 else 4) := by
    rw [fieldBytes,List.length_take]
    have length : (contents middle).length = middle.length := by simp only [contents,List.length_map]
    rw [length,Nat.min_eq_left physical]
  let consumed := keyConsumed++fieldConsumed
  have span : contents before = consumed ++ contents (drop middle (if wide then 8 else 4)) := by rw [keySpan,fieldSpan,List.append_assoc]
  have complete := group_leaf_boundary_after state before _ budget remaining parents count ready consumed span
    (by simp only [consumed,List.length_append,fieldLength]; omega)
    (by simpa only [consumed,feed,List.foldl_append] using fieldPositions)
    (by simpa only [consumed,feed,List.foldl_append] using fieldValue)
    (by simpa only [consumed,feed,List.foldl_append] using fieldValid)
    (by simpa only [consumed,feed,List.foldl_append] using fieldModes)
    (by simpa only [consumed,feed,List.foldl_append] using fieldDepth.trans keyDepth)
    (by simpa only [consumed,feed,List.foldl_append] using fieldStack.trans keyStack)
    (by simpa only [consumed,feed,List.foldl_append,List.length_append,fieldLength,Nat.sub_sub] using fieldRemaining)
    (by simpa only [consumed,feed,List.foldl_append] using fieldInner)
  exact ⟨consumed,span,by simpa only [consumed,feed,List.foldl_append] using fieldCache,complete⟩

#print axioms actual_group_fixed_loop_step
end ChatResponseReference.StreamingUnknownV1
