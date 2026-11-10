import ChatResponseReferenceWork.StreamingUnknownV1.GroupContinuation
import ChatResponseReferenceWork.StreamingUnknownV1.GroupContextInvariant
import ChatResponseReferenceWork.StreamingUnknownV1.GroupFixedAttempt
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkip
open LoopSupportSkip
set_option maxHeartbeats 1000000

theorem group_fixed_induction_step (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (parent tag count : U32) (older : List U32) (budget remaining : Nat) (wide : Bool)
    (ready : GroupLoopReady state before budget remaining (older++[parent]) count)
    (cache : CacheAgrees outer source state) (depthBound : (older++[parent]).length ≤ 98)
    (keyRun : encoding.decode_key sliceBuf before = .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle))
    (recursive : ∀ (after : Slice U8), after.length < before.length →
      ∀ (next : TlsChatResponse.State (BitVec 8) (BitVec 64)) (nextBudget nextRemaining : Nat),
      GroupLoopReady next after nextBudget nextRemaining (older++[parent]) count → CacheAgrees outer source next →
      ∃ result, encoding.skip_field_loop sliceBuf parent after ⟨count⟩ = .ok result ∧
        GroupOutcome outer source next after nextBudget nextRemaining older count result) :
    ∃ result, encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok result ∧
      GroupOutcome outer source state before budget remaining older count result := by
  obtain ⟨body,attempt⟩ := actual_group_fixed_attempt_all outer source state before middle parent tag count (older++[parent]) budget remaining wide ready cache depthBound keyRun
  let width : Nat := if wide then 8 else 4
  by_cases physical : width ≤ middle.length
  · have notUnder : ¬ middle.length < width := by omega
    change encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (groupChild (fixedResult middle width).1 (fixedResult middle width).2) at body
    simp only [fixedResult,if_neg notUnder,groupChild] at body
    change (if width ≤ middle.length then _ else _) at attempt
    rw [if_pos physical] at attempt
    have dropLength : (drop middle width).length = middle.length-width := by
      simp only [drop,Slice.length,List.length_drop]
    have keyStrict := source_key_decreases before middle tag (if wide then .SixtyFourBit else .ThirtyTwoBit) keyRun
    have strict : (drop middle width).length < before.length := by omega
    by_cases fits : width+(before.length-middle.length) < remaining
    · rw [if_pos fits] at attempt
      obtain ⟨consumed,span,nextCache,nextReady⟩ := attempt
      obtain ⟨result,run,post⟩ := recursive (drop middle width) strict (feed state consumed) (budget-consumed.length) (remaining-consumed.length) nextReady nextCache
      refine ⟨result,?_⟩
      apply group_continue_outcome outer source state before (drop middle width) parent count older budget remaining result consumed body run span _ post
      have lengths : before.length = consumed.length+(drop middle width).length := by
        simpa only [contents,List.length_map,List.length_append] using congrArg List.length span
      omega
    · rw [if_neg fits] at attempt
      apply group_exhausted_continue_outcome outer source state before (drop middle width) parent count older budget remaining
        (group_context_positive state before budget remaining (older++[parent]) count ready) body _ attempt
      have := ready.common.physical
      omega
  · change (if width ≤ middle.length then _ else _) at attempt
    rw [if_neg physical] at attempt
    obtain ⟨run,rejected⟩ := attempt
    exact ⟨(.Err (decodeError .BufferUnderflow),middle),run,rejected⟩

#print axioms group_fixed_induction_step
end ChatResponseReference.StreamingUnknownV1
