import ChatResponseReferenceWork.StreamingUnknownV1.GroupContinuation
import ChatResponseReferenceWork.StreamingUnknownV1.GroupContextInvariant
import ChatResponseReferenceWork.StreamingUnknownV1.GroupScalarAttempt
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LoopSupportSkip
set_option maxHeartbeats 1000000

/-- Varint branch of physical-input-length induction. The recursive premise is
restricted to strictly shorter actual source views with the complete live frame
and cache. Native malformed/error and private-exhaustion branches need no
recursive correctness premise. -/
theorem group_varint_induction_step (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (parent tag count : U32) (older : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining (older++[parent]) count)
    (cache : CacheAgrees outer source state) (depthBound : (older++[parent]).length ≤ 98)
    (keyRun : encoding.decode_key sliceBuf before = .ok (.Ok (tag,.Varint),middle))
    (recursive : ∀ (after : Slice U8), after.length < before.length →
      ∀ (next : TlsChatResponse.State (BitVec 8) (BitVec 64)) (nextBudget nextRemaining : Nat),
      GroupLoopReady next after nextBudget nextRemaining (older++[parent]) count → CacheAgrees outer source next →
      ∃ result, encoding.skip_field_loop sliceBuf parent after ⟨count⟩ = .ok result ∧
        GroupOutcome outer source next after nextBudget nextRemaining older count result) :
    ∃ result, encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok result ∧
      GroupOutcome outer source state before budget remaining older count result := by
  obtain ⟨decoded,after,native,prefixPost,errorPost,attempt⟩ :=
    actual_group_varint_attempt_all outer source state before middle parent tag count (older++[parent]) budget remaining ready cache depthBound keyRun
  cases decoded with
  | Err error =>
    obtain ⟨body,run,rejected⟩ := attempt
    exact ⟨(.Err error,after),run,rejected⟩
  | Ok value =>
    obtain ⟨body,decision⟩ := attempt
    have strict : after.length < before.length := by
      have keyStrict := source_key_decreases before middle tag .Varint keyRun
      have fieldBound := source_varint_nonincrease middle after (.Ok value) native
      omega
    by_cases fits : before.length-after.length < remaining
    · rw [if_pos fits] at decision
      obtain ⟨consumed,span,nextCache,nextReady⟩ := decision
      obtain ⟨result,run,post⟩ := recursive after strict (feed state consumed) (budget-consumed.length) (remaining-consumed.length) nextReady nextCache
      refine ⟨result,?_⟩
      apply group_continue_outcome outer source state before after parent count older budget remaining result consumed body run span _ post
      have lengths : before.length = consumed.length+after.length := by
        simpa only [contents,List.length_map,List.length_append] using congrArg List.length span
      omega
    · rw [if_neg fits] at decision
      apply group_exhausted_continue_outcome outer source state before after parent count older budget remaining
        (group_context_positive state before budget remaining (older++[parent]) count ready) body _ decision
      have := ready.common.physical
      omega

#print axioms group_varint_induction_step
end ChatResponseReference.StreamingUnknownV1
