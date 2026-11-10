import ChatResponseReferenceWork.StreamingUnknownV1.GroupPopReady
import ChatResponseReferenceWork.StreamingUnknownV1.GroupMismatchClose
import ChatResponseReferenceWork.StreamingUnknownV1.GroupPopBoundary
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- All actual decoded end-key decisions: source matching/mismatched result and
exact suffix are preserved; numeric success restores the frame only within the
private child, otherwise rejection retains the real source success/error. -/
theorem actual_group_close_attempt_all (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8)
    (parent child count : U32) (older : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining (older++[parent]) count)
    (cache : CacheAgrees outer source state)
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (child,.EndGroup),after)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.done (groupClose parent child after)) ∧
    LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok (groupClose parent child after) ∧
    if child = parent then
      if before.length-remaining ≤ after.length ∧ (after.length = before.length-remaining → older = []) then
        ∃ consumed,
          contents before = consumed ++ contents after ∧ CacheAgrees outer source (feed state consumed) ∧
          if older = [] then count = 99#u32 ∧
            ChildAtKey (feed state consumed) after (budget-consumed.length) (remaining-consumed.length)
          else ∃ parentCount : U32,
            LoopSupportSkip.encoding.DecodeContext.enter_recursion ⟨parentCount⟩ = .ok ⟨count⟩ ∧
            GroupLoopReady (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) older parentCount
      else (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
    else (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have step := group_end_after before after parent child ⟨count⟩ actual
  refine ⟨step,group_loop_done _ _ _ _ step,?_⟩
  by_cases same : child = parent
  · subst child
    simp only [if_pos rfl,if_true]
    by_cases safe : before.length-remaining ≤ after.length ∧ (after.length = before.length-remaining → older = [])
    · rw [if_pos safe]
      obtain ⟨_,_,result⟩ := actual_group_pop_ready outer source state before after parent count older budget remaining ready cache safe.1 safe.2 actual
      exact result
    · rw [if_neg safe]
      have atOrPast : after.length ≤ before.length-remaining := by
        by_contra no
        apply safe
        exact ⟨by omega,by intro impossible; omega⟩
      have unfinished : after.length < before.length-remaining ∨ older ≠ [] := by
        by_cases past : after.length < before.length-remaining
        · exact .inl past
        · right
          intro empty
          exact safe ⟨by omega,fun _ => empty⟩
      exact (actual_group_pop_boundary_reject state before after parent count older budget remaining ready atOrPast unfinished actual).2.2
  · rw [if_neg same]
    exact (actual_group_mismatched_close state before after parent child count older budget remaining ready same actual).2.2

#print axioms actual_group_close_attempt_all
end ChatResponseReference.StreamingUnknownV1
