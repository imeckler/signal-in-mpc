import ChatResponseReferenceWork.StreamingUnknownV1.GroupOutcome
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000

/-- Compose full all-outcome group state agreement through a real consumed
prefix. Source private limit remains absolute; cache and returned frame are
unchanged, with exact counter subtraction and input/suffix decomposition. -/
theorem group_outcome_prefix (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (budget remaining : Nat) (older : List U32) (count : U32)
    (result : core.result.Result Unit LoopSupportSkip.error.DecodeError × Slice U8)
    (consumed : List (BitVec 8)) (span : contents before = consumed++contents middle) (fits : consumed.length ≤ remaining)
    (post : GroupOutcome outer source (feed state consumed) middle (budget-consumed.length) (remaining-consumed.length) older count result) :
    GroupOutcome outer source state before budget remaining older count result := by
  have inputLength : before.length = consumed.length+middle.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  have limit : middle.length-(remaining-consumed.length) = before.length-remaining := by omega
  rcases result with ⟨status,after⟩
  cases status with
  | Err error =>
    change (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed (feed state consumed) (contents middle))).valid = 0 at post
    change (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
    rw [span]
    simpa only [feed,List.foldl_append] using post
  | Ok unitValue =>
    unfold GroupOutcome at post ⊢
    dsimp only at post ⊢
    have compatible : GroupCompatibleEnd middle after (remaining-consumed.length) older ↔ GroupCompatibleEnd before after remaining older := by
      simp only [GroupCompatibleEnd,limit]
    simp only [compatible] at post
    by_cases safe : GroupCompatibleEnd before after remaining older
    · rw [if_pos safe] at post ⊢
      obtain ⟨rest,restSpan,cache,frame⟩ := post
      refine ⟨consumed++rest,?_,?_,?_⟩
      · rw [span,restSpan,List.append_assoc]
      · simpa only [feed,List.foldl_append] using cache
      · simpa only [feed,List.foldl_append,List.length_append,Nat.sub_sub] using frame
    · rw [if_neg safe] at post ⊢
      rw [span]
      simpa only [feed,List.foldl_append] using post

/-- Earlier numeric rejection is compatible with an actual source result only
when every source success lies outside the private domain. This condition keeps
the relation from weakening valid source successes to arbitrary rejection. -/
theorem group_outcome_of_rejected (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before : Slice U8)
    (budget remaining : Nat) (older : List U32) (count : U32)
    (result : core.result.Result Unit LoopSupportSkip.error.DecodeError × Slice U8)
    (rejected : (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0)
    (outside : result.1 = .Ok () → result.2.length < before.length-remaining) :
    GroupOutcome outer source state before budget remaining older count result := by
  rcases result with ⟨status,after⟩
  cases status with
  | Err error => exact rejected
  | Ok unitValue =>
    cases unitValue
    have past : after.length < before.length-remaining := outside rfl
    change (if GroupCompatibleEnd before after remaining older then _ else _) 
    rw [if_neg (by intro safe; have := safe.1; omega)]
    exact rejected

#print axioms group_outcome_prefix
#print axioms group_outcome_of_rejected
end ChatResponseReference.StreamingUnknownV1
