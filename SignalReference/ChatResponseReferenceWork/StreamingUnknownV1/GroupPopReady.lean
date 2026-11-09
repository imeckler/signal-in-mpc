import ChatResponseReferenceWork.StreamingUnknownV1.GroupEndKeyEntry
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual matching group loop exit restores its witnessed enclosing stack and
source context, or returns to the ordinary response parser for the outermost
end. Exact private-child closure is allowed only in that outermost case. -/
theorem actual_group_pop_ready (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8)
    (parent count : U32) (older : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining (older++[parent]) count)
    (cache : CacheAgrees outer source state) (fits : before.length-remaining ≤ after.length)
    (closing : after.length = before.length-remaining → older = [])
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (parent,.EndGroup),after)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.done (.Ok (),after)) ∧
    LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok (.Ok (),after) ∧
    ∃ consumed,
      contents before = consumed ++ contents after ∧ CacheAgrees outer source (feed state consumed) ∧
      if older = [] then count = 99#u32 ∧
        ChildAtKey (feed state consumed) after (budget-consumed.length) (remaining-consumed.length)
      else ∃ parentCount : U32,
        LoopSupportSkip.encoding.DecodeContext.enter_recursion ⟨parentCount⟩ = .ok ⟨count⟩ ∧
        GroupLoopReady (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) older parentCount := by
  have step : LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.done (.Ok (),after)) := by
    have result := group_end_after before after parent parent ⟨count⟩ actual
    simpa only [groupClose,if_pos rfl,if_true] using result
  refine ⟨step,group_loop_done _ _ _ _ step,?_⟩
  have offset : (older++[parent]).length-1 = older.length := by simp only [List.length_append,List.length_cons,List.length_nil]; omega
  have parentSlot : state.stack[(older++[parent]).length-1]'(by have size : state.stack.length = 100 := ready.common.shape.stack; have := ready.bounded; omega) = BitVec.ofNat 64 parent.val := by
    have slot := ready.slots older.length (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
    simpa only [offset,List.getElem_append_right (by omega : older.length ≤ older.length),Nat.sub_self,List.getElem_cons_zero] using slot
  obtain ⟨consumed,span,data,nextValid,nextModes,nextPositions,nextValue,nextTag,nextKnown,nextKinds,nextInner,nextDepth,nextStack,nextBudget,nextRemaining,nextSeen,nextFinished,nextUtf⟩ :=
    nested_native_end_key_entry state before after parent (older++[parent]).length budget remaining ready.common.budgetBound ready.common.remainingBound
      ready.common.budgetEnough ready.common.physical fits (by intro atEnd; rw [closing atEnd]; rfl) ready.modes ready.common.positions ready.common.shape.kinds ready.common.shape.utf
      ready.common.value ready.common.valid ready.common.seen ready.common.finished ready.common.inner ready.depth ready.common.budgetCounter ready.common.childCounter
      ready.positive ready.bounded ready.common.shape.stack parentSlot actual
  have inputLength : before.length = consumed.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  have consumedFits : consumed.length ≤ remaining := by have := ready.common.physical; omega
  have nextDepthOlder : (feed state consumed).depth = BitVec.ofNat 64 older.length := by
    rw [nextDepth,ready.depth]
    change BitVec.ofNat 64 (older++[parent]).length - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ 1 (by decide) (by simp only [List.length_append,List.length_cons,List.length_nil]; omega),offset]
  have oldShape : StateShape state := ⟨ready.common.shape.modes,ready.common.shape.positions,ready.common.shape.kinds,ready.common.shape.stack,ready.common.shape.utf⟩
  have shape := feed_shape state consumed oldShape
  refine ⟨consumed,span,data.trans cache,?_⟩
  by_cases empty : older = []
  · rw [if_pos empty]
    have sourceCount : count = 99#u32 := by
      apply UScalar.eq_of_val_eq
      have context := ready.context
      rw [empty] at context
      simp only [List.nil_append,List.length_cons,List.length_nil] at context
      change count.val = 99
      omega
    have zeroBits : BitVec.ofNat 64 0 = (0 : BitVec 64) := rfl
    refine ⟨sourceCount,?_,nextModes,?_⟩
    · exact ⟨by have := ready.common.budgetBound; omega,by have := ready.common.remainingBound; omega,
        by have := ready.common.physical; omega,by have := ready.common.budgetEnough; omega,
        shape,nextPositions,nextValue,nextValid,nextSeen,nextFinished,by simpa only [empty,List.length_nil,zeroBits] using nextDepthOlder,nextBudget,nextRemaining⟩
    · have equal : consumed.length = remaining ↔ remaining-consumed.length = 0 := by omega
      simpa only [equal] using nextInner
  · rw [if_neg empty]
    have olderPositive : 0 < older.length := List.length_pos_iff.mpr empty
    have remainingPositive : 0 < remaining-consumed.length := by
      by_contra no
      have atEnd : after.length = before.length-remaining := by omega
      exact empty (closing atEnd)
    let parentCount := U32.ofNatCore (count.val+1) (by have := ready.context; have := ready.positive; scalar_tac)
    have parentValue : parentCount.val = count.val+1 := rfl
    have erasedShape : StateShape (eraseGroupDepth (feed state consumed)) := ⟨shape.modes,shape.positions,shape.kinds,shape.stack,shape.utf⟩
    have common : ChildReady (eraseGroupDepth (feed state consumed)) after (budget-consumed.length) (remaining-consumed.length) :=
      ⟨⟨by have := ready.common.budgetBound; omega,by have := ready.common.remainingBound; omega,
        by have := ready.common.physical; omega,by have := ready.common.budgetEnough; omega,
        erasedShape,nextPositions,nextValue,nextValid,nextSeen,nextFinished,rfl,nextBudget,nextRemaining⟩,
        remainingPositive,by rw [if_neg (by omega : consumed.length ≠ remaining)] at nextInner; exact nextInner⟩
    refine ⟨parentCount,enter_recursion_value parentCount count parentValue,common,nextModes,olderPositive,?_,nextDepthOlder,?_,?_⟩
    · have oldBound := ready.bounded
      simp only [List.length_append,List.length_cons,List.length_nil] at oldBound
      omega
    · intro index inside
      have slot := ready.slots index (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
      simpa only [nextStack,List.getElem_append_left inside] using slot
    · have context := ready.context
      simp only [List.length_append,List.length_cons,List.length_nil] at context
      omega

#print axioms actual_group_pop_ready
end ChatResponseReference.StreamingUnknownV1
