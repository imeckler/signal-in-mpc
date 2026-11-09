import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyEntry
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual native nested start key extends the witnessed active parent stack and
performs the actual source context decrement. Child context, control/validity,
private counters and cache are derived rather than supplied as next-state facts. -/
theorem nested_group_push_ready (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (tag count : U32)
    (parents : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining parents count)
    (cache : CacheAgrees outer source state) (depthBound : parents.length ≤ 98)
    (fits : before.length-remaining < after.length)
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,.StartGroup),after)) :
    ∃ child consumed,
      LoopSupportSkip.encoding.DecodeContext.enter_recursion ⟨count⟩ = .ok ⟨child⟩ ∧
      contents before = consumed ++ contents after ∧
      CacheAgrees outer source (feed state consumed) ∧
      GroupLoopReady (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) (parents++[tag]) child ∧
      (feed state consumed).scalarKnown = 0 ∧ (feed state consumed).kinds = [0,0,0,0] := by
  have countPositive : 0 < count.val := by have := ready.context; omega
  let child := U32.ofNatCore (count.val-1) (by have h := count.hmax; scalar_tac)
  have decremented : count.val = child.val+1 := by change count.val = (count.val-1)+1; omega
  obtain ⟨consumed,span,data,nextValid,nextModes,nextPositions,nextValue,nextTag,nextKnown,nextKinds,nextInner,nextDepth,nextStack,nextBudget,nextRemaining,nextSeen,nextFinished,nextUtf⟩ :=
    nested_native_nonfixed_key_entry state before after tag .StartGroup parents.length budget remaining ready.common.budgetBound ready.common.remainingBound
      ready.common.budgetEnough ready.common.physical fits ready.modes ready.common.positions ready.common.shape.kinds ready.common.shape.utf
      ready.common.value ready.common.valid ready.common.seen ready.common.finished ready.common.inner ready.depth ready.common.budgetCounter ready.common.childCounter
      ready.positive depthBound (.inr (.inr rfl)) actual
  have inputLength : before.length = consumed.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  have shape := feed_shape state consumed
    (show StateShape state from ⟨ready.common.shape.modes,ready.common.shape.positions,ready.common.shape.kinds,ready.common.shape.stack,ready.common.shape.utf⟩)
  have erasedShape : StateShape (eraseGroupDepth (feed state consumed)) := ⟨shape.modes,shape.positions,shape.kinds,shape.stack,shape.utf⟩
  have common : ChildReady (eraseGroupDepth (feed state consumed)) after (budget-consumed.length) (remaining-consumed.length) :=
    ⟨⟨by have := ready.common.budgetBound; omega,by have := ready.common.remainingBound; omega,
      by have := ready.common.physical; omega,by have := ready.common.budgetEnough; omega,
      erasedShape,nextPositions,nextValue,nextValid,nextSeen,nextFinished,rfl,nextBudget,nextRemaining⟩,
      by have := ready.common.physical; omega,nextInner⟩
  have newDepth : (feed state consumed).depth = BitVec.ofNat 64 (parents++[tag]).length := by
    simp only [wireNumber,if_pos rfl,if_true] at nextDepth
    rw [nextDepth,ready.depth]
    change BitVec.ofNat 64 parents.length + BitVec.ofNat 64 1 = _
    rw [←BitVec.ofNat_add]
    simp only [List.length_append,List.length_cons,List.length_nil]
  have group : GroupLoopReady (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) (parents++[tag]) child := by
    refine ⟨common,nextModes,by simp only [List.length_append,List.length_cons,List.length_nil]; omega,
      by simp only [List.length_append,List.length_cons,List.length_nil]; omega,newDepth,?_,?_⟩
    · intro index inside
      have indexBound : index < 100 := by simp only [List.length_append,List.length_cons,List.length_nil] at inside; omega
      have slot := group_stack_write_slot state.stack parents.length index (BitVec.ofNat 64 tag.val)
        (by have size : state.stack.length = 100 := ready.common.shape.stack; omega) (by omega)
        (by have size : state.stack.length = 100 := ready.common.shape.stack; omega)
      have numericSlot : (feed state consumed).stack[index]'(by have := shape.stack; omega) =
          if parents.length = index then BitVec.ofNat 64 tag.val else state.stack[index]'(by have size : state.stack.length = 100 := ready.common.shape.stack; omega) := by
        simpa only [nextStack,wireNumber,if_pos rfl,if_true,ready.depth] using slot
      by_cases old : index < parents.length
      · rw [if_neg (by omega : parents.length ≠ index)] at numericSlot
        rw [numericSlot,ready.slots index old]
        simp only [List.getElem_append_left old]
      · have equal : index = parents.length := by simp only [List.length_append,List.length_cons,List.length_nil] at inside; omega
        subst index
        simp only [if_pos rfl,if_true] at numericSlot
        rw [numericSlot]
        simp only [List.getElem_append_right (by omega : parents.length ≤ parents.length),Nat.sub_self,List.getElem_cons_zero]
    · have sourceCount := ready.context
      simp only [List.length_append,List.length_cons,List.length_nil]
      omega
  exact ⟨child,consumed,enter_recursion_value count child decremented,span,data.trans cache,group,nextKnown,nextKinds⟩

#print axioms nested_group_push_ready
end ChatResponseReference.StreamingUnknownV1
