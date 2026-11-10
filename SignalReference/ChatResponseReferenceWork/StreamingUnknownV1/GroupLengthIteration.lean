import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthComplete
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLeafBoundary
import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyEntry
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual source group-loop key/context/length body iteration agrees with the
complete numeric recursive invariant for arbitrary tags/lengths/payload bytes. Known
response tag numbers remain ignored; exact suffix/cache/private counters/active
stack/source context are retained. -/
theorem actual_group_length_loop_step (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8)
    (parent tag count : U32) (native : U64) (parents : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining parents count)
    (cache : CacheAgrees outer source state) (depthBound : parents.length ≤ 98)
    (strictFit : native.val+(before.length-after.length) < remaining)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.cont (drop after native.val)) ∧
    ∃ consumed,
      contents before = consumed ++ contents (drop after native.val) ∧ CacheAgrees outer source (feed state consumed) ∧
      GroupLoopReady (feed state consumed) (drop after native.val) (budget-consumed.length) (remaining-consumed.length) parents count := by
  have countPositive : 1 < count.val := by have := ready.context; omega
  let child := U32.ofNatCore (count.val-1) (by have h := count.hmax; scalar_tac)
  have decremented : count.val = child.val+1 := by change count.val = (count.val-1)+1; omega
  have childPositive : child ≠ 0#u32 := by
    intro zero
    have numeric := congrArg UScalar.val zero
    change child.val = 0 at numeric
    omega
  obtain ⟨leading,byte,tail,valueSpan,valueSuffix,_,_,_,_,_⟩ := native_success_span middle after native valueRun
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length valueSuffix
    simpa only [contents,List.length_map] using result.symm
  have middleLength : middle.length = leading.length+1+after.length := by
    have result := congrArg List.length valueSpan
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  have keyFits : before.length-remaining < middle.length := by have := ready.common.physical; omega
  obtain ⟨keyConsumed,keySpan,keyData,keyValid,keyModes,keyPositions,keyValue,keyTag,keyKnown,keyKinds,keyInner,keyDepth,keyStack,keyBudget,keyRemaining,keySeen,keyFinished,keyUtf⟩ :=
    nested_native_nonfixed_key_entry state before middle tag .LengthDelimited parents.length budget remaining ready.common.budgetBound ready.common.remainingBound
      ready.common.budgetEnough ready.common.physical keyFits ready.modes ready.common.positions ready.common.shape.kinds ready.common.shape.utf
      ready.common.value ready.common.valid ready.common.seen ready.common.finished ready.common.inner ready.depth ready.common.budgetCounter ready.common.childCounter
      ready.positive depthBound (.inr (.inl rfl)) keyRun
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
  have physical : native.val ≤ after.length := by have := ready.common.physical; omega
  have childRun := length_delimited_after middle after native tag child childPositive valueRun
  simp only [fixedResult,if_neg (by omega : ¬after.length < native.val)] at childRun
  have sourceStep : LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.cont (drop after native.val)) :=
    group_child_after before middle _ parent tag ⟨count⟩ ⟨child⟩ .LengthDelimited (.Ok ())
      (by intro same; cases same) keyRun (enter_recursion_value count child decremented) childRun
  refine ⟨sourceStep,?_⟩
  obtain ⟨fieldConsumed,fieldSpan,fieldCache,fieldModes,fieldPositions,fieldValue,fieldValid,fieldDepth,fieldStack,fieldRemaining,fieldInner⟩ :=
    group_length_value_complete outer source (feed state keyConsumed) middle after native (budget-keyConsumed.length) (remaining-keyConsumed.length)
      fieldReady (keyData.trans cache) (by omega) keyModes keyKinds valueRun
  have fieldLength : middle.length = fieldConsumed.length+(drop after native.val).length := by
    have result := congrArg List.length fieldSpan
    simpa only [contents,List.length_map,List.length_append] using result
  have dropped : (drop after native.val).length = after.length-native.val := by
    change (after.val.drop native.val).length = _
    rw [List.length_drop]
  simp only [wireNumber,if_neg (by decide : ¬(2:Nat) = 3)] at keyDepth keyStack
  let consumed := keyConsumed++fieldConsumed
  have span : contents before = consumed ++ contents (drop after native.val) := by rw [keySpan,fieldSpan,List.append_assoc]
  have complete := group_leaf_boundary_after state before (drop after native.val) budget remaining parents count ready consumed span
    (by simp only [consumed,List.length_append]; omega)
    (by simpa only [consumed,feed,List.foldl_append] using fieldPositions)
    (by simpa only [consumed,feed,List.foldl_append] using fieldValue)
    (by simpa only [consumed,feed,List.foldl_append] using fieldValid)
    (by simpa only [consumed,feed,List.foldl_append] using fieldModes)
    (by simpa only [consumed,feed,List.foldl_append] using fieldDepth.trans keyDepth)
    (by simpa only [consumed,feed,List.foldl_append] using fieldStack.trans keyStack)
    (by simpa only [consumed,feed,List.foldl_append,List.length_append,Nat.sub_sub] using fieldRemaining)
    (by simpa only [consumed,feed,List.foldl_append] using fieldInner)
  exact ⟨consumed,span,by simpa only [consumed,feed,List.foldl_append] using fieldCache,complete⟩

#print axioms actual_group_length_loop_step
end ChatResponseReference.StreamingUnknownV1
