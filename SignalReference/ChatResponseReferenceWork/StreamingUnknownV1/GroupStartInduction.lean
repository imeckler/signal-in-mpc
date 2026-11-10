import ChatResponseReferenceWork.StreamingUnknownV1.GroupContinuation
import ChatResponseReferenceWork.StreamingUnknownV1.GroupContextInvariant
import ChatResponseReferenceWork.StreamingUnknownV1.GroupPushReady
import ChatResponseReferenceWork.StreamingUnknownV1.GroupStartBoundary
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkip
open LoopSupportSkip
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Nested start-group branch, with recursion on both the actual nested group
and the actual enclosing-group remainder, each strictly shorter physically. -/
theorem group_start_induction_step (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (parent tag count : U32) (older : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining (older++[parent]) count)
    (cache : CacheAgrees outer source state) (depthBound : (older++[parent]).length ≤ 98)
    (keyRun : encoding.decode_key sliceBuf before = .ok (.Ok (tag,.StartGroup),middle))
    (recursive : ∀ (after : Slice U8), after.length < before.length →
      ∀ (next : TlsChatResponse.State (BitVec 8) (BitVec 64)) (nextParent nextCount : U32) (nextOlder : List U32) (nextBudget nextRemaining : Nat),
      GroupLoopReady next after nextBudget nextRemaining (nextOlder++[nextParent]) nextCount → CacheAgrees outer source next →
      ∃ result, encoding.skip_field_loop sliceBuf nextParent after ⟨nextCount⟩ = .ok result ∧
        GroupOutcome outer source next after nextBudget nextRemaining nextOlder nextCount result) :
    ∃ result, encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok result ∧
      GroupOutcome outer source state before budget remaining older count result := by
  classical
  have positive := group_context_positive state before budget remaining (older++[parent]) count ready
  by_cases inside : before.length-remaining < middle.length
  · obtain ⟨child,header,entered,span,childCache,childReady,known,kinds⟩ :=
      nested_group_push_ready outer source state before middle tag count (older++[parent]) budget remaining ready cache depthBound inside keyRun
    have keyStrict := source_key_decreases before middle tag .StartGroup keyRun
    have childPositive := group_context_positive (feed state header) middle (budget-header.length) (remaining-header.length) ((older++[parent])++[tag]) child childReady
    obtain ⟨result,childRun,childPost⟩ := recursive middle keyStrict (feed state header) tag child (older++[parent]) (budget-header.length) (remaining-header.length) childReady childCache
    rcases result with ⟨status,after⟩
    have childSkip : encoding.skip_field sliceBuf .StartGroup tag middle ⟨child⟩ = .ok (status,after) := by
      rw [start_group middle tag child childPositive]
      exact childRun
    have body := group_child_after before middle after parent tag ⟨count⟩ ⟨child⟩ .StartGroup status (by intro same; cases same) keyRun entered childSkip
    have lengths : before.length = header.length+middle.length := by
      simpa only [contents,List.length_map,List.length_append] using congrArg List.length span
    have headerFits : header.length ≤ remaining := by omega
    have limit : middle.length-(remaining-header.length) = before.length-remaining := by omega
    cases status with
    | Err error =>
      have run := group_loop_done before parent ⟨count⟩ (.Err error,after) body
      refine ⟨(.Err error,after),run,?_⟩
      change (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed (feed state header) (contents middle))).valid = 0 at childPost
      change (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
      rw [span]
      simpa only [feed,List.foldl_append] using childPost
    | Ok unitValue =>
      cases unitValue
      change encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.cont after) at body
      change (if GroupCompatibleEnd middle after (remaining-header.length) (older++[parent]) then _ else _) at childPost
      by_cases compatible : GroupCompatibleEnd middle after (remaining-header.length) (older++[parent])
      · rw [if_pos compatible] at childPost
        obtain ⟨payload,payloadSpan,nextCache,frame⟩ := childPost
        have nonempty : older++[parent] ≠ [] := by simp
        unfold GroupReturnedFrame at frame
        rw [if_neg nonempty] at frame
        obtain ⟨restoredCount,restoredEnter,restoredReady⟩ := frame
        have sameCount := group_context_unique state (feed (feed state header) payload) before after budget remaining ((budget-header.length)-payload.length) ((remaining-header.length)-payload.length) (older++[parent]) count restoredCount ready restoredReady
        subst restoredCount
        have childBound := source_group_nonincrease middle after tag child childPositive (.Ok ()) childRun
        have afterStrict : after.length < before.length := by omega
        obtain ⟨last,restRun,restPost⟩ := recursive after afterStrict (feed (feed state header) payload) parent count older ((budget-header.length)-payload.length) ((remaining-header.length)-payload.length) restoredReady nextCache
        have combinedSpan : contents before = (header++payload)++contents after := by rw [span,payloadSpan,List.append_assoc]
        have payloadLengths : middle.length = payload.length+after.length := by
          simpa only [contents,List.length_map,List.length_append] using congrArg List.length payloadSpan
        have combinedFits : (header++payload).length ≤ remaining := by
          have bound := compatible.1
          rw [limit] at bound
          simp only [List.length_append]
          omega
        refine ⟨last,?_⟩
        apply group_continue_outcome outer source state before after parent count older budget remaining last (header++payload) body restRun combinedSpan combinedFits
        simpa only [feed,List.foldl_append,List.length_append,Nat.sub_sub] using restPost
      · rw [if_neg compatible] at childPost
        have rejected : (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
          rw [span]
          simpa only [feed,List.foldl_append] using childPost
        apply group_exhausted_continue_outcome outer source state before after parent count older budget remaining positive body _ rejected
        have exhausted : after.length ≤ middle.length-(remaining-header.length) := by
          by_contra notExhausted
          apply compatible
          constructor
          · omega
          · intro equal
            omega
        rw [limit] at exhausted
        exact exhausted
  · have exhausted : middle.length ≤ before.length-remaining := by omega
    exact group_exhausted_nonend_outcome outer source state before middle parent tag count .StartGroup older budget remaining positive
      (by intro same; cases same) keyRun exhausted
      (group_start_key_not_inside_reject state before middle tag count (older++[parent]) budget remaining ready depthBound exhausted keyRun)

#print axioms group_start_induction_step
end ChatResponseReference.StreamingUnknownV1
