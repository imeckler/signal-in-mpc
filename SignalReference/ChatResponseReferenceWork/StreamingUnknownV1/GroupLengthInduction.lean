import ChatResponseReferenceWork.StreamingUnknownV1.GroupContinuation
import ChatResponseReferenceWork.StreamingUnknownV1.GroupContextInvariant
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthAttempt
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkip
open LoopSupportSkip
set_option maxHeartbeats 1000000

theorem group_length_induction_step (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (parent tag count : U32) (older : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining (older++[parent]) count)
    (cache : CacheAgrees outer source state) (depthBound : (older++[parent]).length ≤ 98)
    (keyRun : encoding.decode_key sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (recursive : ∀ (after : Slice U8), after.length < before.length →
      ∀ (next : TlsChatResponse.State (BitVec 8) (BitVec 64)) (nextBudget nextRemaining : Nat),
      GroupLoopReady next after nextBudget nextRemaining (older++[parent]) count → CacheAgrees outer source next →
      ∃ result, encoding.skip_field_loop sliceBuf parent after ⟨count⟩ = .ok result ∧
        GroupOutcome outer source next after nextBudget nextRemaining older count result) :
    ∃ result, encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok result ∧
      GroupOutcome outer source state before budget remaining older count result := by
  obtain ⟨decoded,after,native,prefixPost,errorPost,body,attempt⟩ := actual_group_length_attempt_all outer source state before middle parent tag count (older++[parent]) budget remaining ready cache depthBound keyRun
  cases decoded with
  | Err error =>
    obtain ⟨run,rejected⟩ := attempt
    exact ⟨(.Err error,after),run,rejected⟩
  | Ok value =>
    dsimp only at attempt
    by_cases physical : value.val ≤ after.length
    · have notUnder : ¬ after.length < value.val := by omega
      simp only [groupLengthNativeResult,fixedResult,if_neg notUnder,groupChild] at body
      rw [if_pos physical] at attempt
      have dropLength : (drop after value.val).length = after.length-value.val := by
        simp only [drop,Slice.length,List.length_drop]
      have keyStrict := source_key_decreases before middle tag .LengthDelimited keyRun
      have headerBound := source_varint_nonincrease middle after (.Ok value) native
      have strict : (drop after value.val).length < before.length := by omega
      by_cases fits : value.val+(before.length-after.length) < remaining
      · rw [if_pos fits] at attempt
        obtain ⟨consumed,span,nextCache,nextReady⟩ := attempt
        obtain ⟨result,run,post⟩ := recursive (drop after value.val) strict (feed state consumed) (budget-consumed.length) (remaining-consumed.length) nextReady nextCache
        refine ⟨result,?_⟩
        apply group_continue_outcome outer source state before (drop after value.val) parent count older budget remaining result consumed body run span _ post
        have lengths : before.length = consumed.length+(drop after value.val).length := by
          simpa only [contents,List.length_map,List.length_append] using congrArg List.length span
        omega
      · rw [if_neg fits] at attempt
        apply group_exhausted_continue_outcome outer source state before (drop after value.val) parent count older budget remaining
          (group_context_positive state before budget remaining (older++[parent]) count ready) body _ attempt
        have := ready.common.physical
        omega
    · rw [if_neg physical] at attempt
      obtain ⟨run,rejected⟩ := attempt
      exact ⟨(.Err (decodeError .BufferUnderflow),after),run,rejected⟩

#print axioms group_length_induction_step
end ChatResponseReference.StreamingUnknownV1
