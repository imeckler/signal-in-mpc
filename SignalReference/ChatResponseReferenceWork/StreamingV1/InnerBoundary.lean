import ChatResponseReferenceWork.StreamingV1.NativeLengthControls
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipSlice

/-- Common bounded child-loop state; source content/cache relation is separate.
The actual parent buffer retains its suffix beyond the private child limit. -/
structure ChildCommon (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (view : Slice U8)
    (budget remaining : Nat) : Prop where
  budgetBound : budget ≤ 4096
  remainingBound : remaining ≤ 4096
  physical : remaining ≤ view.length
  budgetEnough : view.length ≤ budget
  shape : StateShape state
  positions : state.positions = oneHot 0
  value : state.value = 0
  valid : state.valid = 255
  seen : state.seen = 255
  finished : state.finished = 0
  depth : state.depth = 0
  budgetCounter : state.budget = BitVec.ofNat 64 budget
  childCounter : state.responseRemaining = BitVec.ofNat 64 remaining

structure ChildAtKey (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (view : Slice U8)
    (budget remaining : Nat) : Prop extends ChildCommon state view budget remaining where
  modes : state.modes = lane 0
  inner : state.inner = if remaining = 0 then 0 else 255

structure ChildReady (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (view : Slice U8)
    (budget remaining : Nat) : Prop extends ChildCommon state view budget remaining where
  positive : 0 < remaining
  inner : state.inner = 255

theorem ready_of_key (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (view : Slice U8)
    (budget remaining : Nat) (ready : ChildAtKey state view budget remaining) (positive : 0 < remaining) :
    ChildReady state view budget remaining :=
  ⟨ready.toChildCommon,positive,by simpa only [if_neg (by omega : remaining ≠ 0)] using ready.inner⟩

/-- Assembly of established post-field facts into the next-key invariant. No
source parsing/validity assumption is hidden: each transition fact is supplied
by a checked native field composition theorem at its call site. -/
theorem child_boundary_after (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8)
    (budget remaining : Nat) (ready : ChildReady state before budget remaining)
    (consumed : List (BitVec 8)) (span : contents before = consumed ++ contents after)
    (fits : consumed.length ≤ remaining)
    (positions : (feed state consumed).positions = oneHot 0) (value : (feed state consumed).value = 0)
    (valid : (feed state consumed).valid = 255) (modes : (feed state consumed).modes = lane 0)
    (depth : (feed state consumed).depth = state.depth)
    (counter : (feed state consumed).responseRemaining = BitVec.ofNat 64 (remaining-consumed.length))
    (inner : (feed state consumed).inner = if consumed.length = remaining then 0 else 255) :
    ChildAtKey (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) := by
  have inputLength : before.length = consumed.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  refine ⟨⟨by have := ready.budgetBound; omega,by have := ready.remainingBound; omega,
    by have := ready.physical; omega,by have := ready.budgetEnough; omega,
    feed_shape state consumed ready.shape,positions,value,valid,(feed_seen state consumed).trans ready.seen,
    (feed_finished state consumed).trans ready.finished,depth.trans ready.depth,
    feed_budget state consumed budget (by have := ready.budgetEnough; omega) ready.budgetCounter,counter⟩,modes,?_⟩
  have equal : consumed.length = remaining ↔ remaining-consumed.length = 0 := by omega
  simpa only [equal] using inner

#print axioms ready_of_key
#print axioms child_boundary_after
end ChatResponseReference.StreamingV1
