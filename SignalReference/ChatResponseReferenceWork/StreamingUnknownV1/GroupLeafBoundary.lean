import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipSlice

/-- Assemble separately proved ordinary-field facts into the same recursive
source-context/active-stack relation. Callers derive every supplied transition
fact from actual field/decoder execution; this is not an assumed skip model. -/
theorem group_leaf_boundary_after (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (budget remaining : Nat) (parents : List U32) (count : U32)
    (ready : GroupLoopReady state before budget remaining parents count)
    (consumed : List (BitVec 8)) (span : contents before = consumed ++ contents after)
    (fits : consumed.length < remaining)
    (positions : (feed state consumed).positions = oneHot 0) (value : (feed state consumed).value = 0)
    (valid : (feed state consumed).valid = 255) (modes : (feed state consumed).modes = lane 0)
    (depth : (feed state consumed).depth = state.depth) (stack : (feed state consumed).stack = state.stack)
    (counter : (feed state consumed).responseRemaining = BitVec.ofNat 64 (remaining-consumed.length))
    (inner : (feed state consumed).inner = 255) :
    GroupLoopReady (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) parents count := by
  have inputLength : before.length = consumed.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  have oldShape : StateShape state := ⟨ready.common.shape.modes,ready.common.shape.positions,ready.common.shape.kinds,ready.common.shape.stack,ready.common.shape.utf⟩
  have shape := feed_shape state consumed oldShape
  have erasedShape : StateShape (eraseGroupDepth (feed state consumed)) := ⟨shape.modes,shape.positions,shape.kinds,shape.stack,shape.utf⟩
  have common : ChildReady (eraseGroupDepth (feed state consumed)) after (budget-consumed.length) (remaining-consumed.length) :=
    ⟨⟨by have := ready.common.budgetBound; omega,by have := ready.common.remainingBound; omega,
      by have := ready.common.physical; omega,by have := ready.common.budgetEnough; omega,
      erasedShape,positions,value,valid,(feed_seen state consumed).trans ready.common.seen,
      (feed_finished state consumed).trans ready.common.finished,rfl,
      feed_budget state consumed budget (by have := ready.common.budgetEnough; have := ready.common.physical; omega) ready.common.budgetCounter,counter⟩,
      by omega,inner⟩
  refine ⟨common,modes,ready.positive,ready.bounded,depth.trans ready.depth,?_,ready.context⟩
  intro index inside
  simpa only [stack] using ready.slots index inside

#print axioms group_leaf_boundary_after
end ChatResponseReference.StreamingUnknownV1
