import ChatResponseReferenceWork.StreamingUnknownV1.StartKeyEntry
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual generated unknown start key establishes the complete recursive group
entry, including its actual tag at active slot0 and source recursion context99.
The key must leave private child bytes for a real closing tag. -/
theorem actual_unknown_start_key_ready (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (tag : U32)
    (budget remaining : Nat) (boundary : ChildAtKey state before budget remaining)
    (cache : CacheAgrees outer source state) (positive : 0 < remaining)
    (fits : before.length-remaining < after.length) (unknown : 5 < tag.val)
    (actual : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.StartGroup),after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      CacheAgrees outer source (feed state consumed) ∧
      GroupLoopReady (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) [tag] (99#u32) ∧
      (feed state consumed).scalarKnown = 0 ∧ (feed state consumed).kinds = [0,0,0,0] := by
  have ready := ready_of_key state before budget remaining boundary positive
  have native := actual_driver_key_native before after tag .StartGroup actual
  simp only [ActualInnerResponseV1.toSkipWire] at native
  obtain ⟨consumed,span,data,nextValid,nextModes,nextPositions,nextValue,nextTag,nextKnown,nextKinds,nextInner,nextDepth,nextStack,nextBudget,nextRemaining,nextSeen,nextFinished,nextUtf⟩ :=
    unknown_native_start_key_entry state before after tag .StartGroup budget remaining ready.budgetBound ready.remainingBound ready.budgetEnough ready.physical
      fits boundary.modes ready.positions ready.shape.kinds ready.shape.utf ready.value ready.valid ready.seen ready.finished ready.inner ready.depth
      ready.budgetCounter ready.childCounter unknown rfl native
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
  have shape := feed_shape state consumed ready.shape
  have erasedShape : StateShape (eraseGroupDepth (feed state consumed)) := ⟨shape.modes,shape.positions,shape.kinds,shape.stack,shape.utf⟩
  have common : ChildReady (eraseGroupDepth (feed state consumed)) after (budget-consumed.length) (remaining-consumed.length) :=
    ⟨⟨by have := ready.budgetBound; omega,by have := ready.remainingBound; omega,
      by have := ready.physical; omega,by have := ready.budgetEnough; omega,
      erasedShape,nextPositions,nextValue,nextValid,nextSeen,nextFinished,rfl,nextBudget,nextRemaining⟩,childPositive,nextInner⟩
  have depthOne : (feed state consumed).depth = BitVec.ofNat 64 1 := by
    rw [nextDepth,ready.depth]
    rfl
  have group : GroupLoopReady (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) [tag] (99#u32) := by
    refine ⟨common,nextModes,by simp only [List.length_cons,List.length_nil]; decide,by simp only [List.length_cons,List.length_nil]; decide,depthOne,?_,by simp only [List.length_cons,List.length_nil]; decide⟩
    intro index inside
    have zero : index = 0 := by simp only [List.length_cons,List.length_nil] at inside; omega
    subst index
    have slot := group_stack_write_slot state.stack 0 0 (BitVec.ofNat 64 tag.val) (by have := ready.shape.stack; omega) (by decide)
      (by have := ready.shape.stack; omega)
    have zeroBits : BitVec.ofNat 64 0 = (0 : BitVec 64) := rfl
    simpa only [nextStack,ready.depth,zeroBits,if_true,List.getElem_cons_zero] using slot
  exact ⟨consumed,span,data.trans cache,group,nextKnown,nextKinds⟩

#print axioms actual_unknown_start_key_ready
end ChatResponseReference.StreamingUnknownV1
