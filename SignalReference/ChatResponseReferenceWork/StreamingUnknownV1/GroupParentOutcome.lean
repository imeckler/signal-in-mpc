import ChatResponseReferenceWork.StreamingUnknownV1.GroupDispatcherAll
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkip
open LoopSupportSkip
set_option maxHeartbeats 2000000

/-- Exhaustive actual unknown-group parent iteration, including the real later
DelimitedLengthExceeded result on native successful overrun. No native result,
fit decision, primitive correctness or termination premise is supplied. -/
theorem actual_unknown_group_parent_all (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8) (tag : U32)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (limit : Usize)
    (limitExact : limit.val = before.length-remaining)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (unknown : 5 < tag.val) (context : ctx.recurse_count = 99#u32)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.StartGroup),middle)) :
    ∃ status after, encoding.skip_field_loop sliceBuf tag middle ⟨99#u32⟩ = .ok (status,after) ∧
      match status with
      | .Err error =>
        ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
          .ok (.Err (ActualResponseBytesV1.fromSkipError error),source,after) ∧
        (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
      | .Ok _ =>
        if before.length-remaining ≤ after.length then
          SubmessageV1.body ctx limit (source,before,()) = .ok (.cont (source,after,())) ∧
          ∃ consumed, contents before = consumed++contents after ∧ CacheAgrees outer source (feed state consumed) ∧
            ChildAtKey (feed state consumed) after (budget-consumed.length) (remaining-consumed.length)
        else
          ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
            .ok (.Err (SubmessageV1.decodeError .DelimitedLengthExceeded),source,after) ∧
          (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨result,run,body,post⟩ := actual_unknown_group_loop_step_all outer source state before middle tag ctx budget remaining limit limitExact boundary cache positive unknown context keyRun
  rcases result with ⟨status,after⟩
  refine ⟨status,after,run,?_⟩
  cases status with
  | Err error =>
    have finite : InnerScanV1.FiniteRun (SubmessageV1.body ctx limit) (source,before,())
        (.ok (.Err (ActualResponseBytesV1.fromSkipError error),source,after)) := .done body
    exact ⟨InnerScanV1.finite_run_actual finite,post⟩
  | Ok unitValue =>
    cases unitValue
    dsimp only
    have compatible : GroupCompatibleEnd before after remaining [] ↔ before.length-remaining ≤ after.length := by
      simp only [GroupCompatibleEnd,and_true,implies_true]
    change (if GroupCompatibleEnd before after remaining [] then _ else _) at post
    simp only [compatible] at post
    by_cases fits : before.length-remaining ≤ after.length
    · rw [if_pos fits] at post ⊢
      obtain ⟨consumed,span,nextCache,frame⟩ := post
      exact ⟨body,consumed,span,nextCache,frame.2⟩
    · rw [if_neg fits] at post ⊢
      have overrunScalar : after.len < limit := by scalar_tac
      have finished : SubmessageV1.body ctx limit (source,after,()) =
          .ok (.done (.Err (SubmessageV1.decodeError .DelimitedLengthExceeded),source,after)) :=
        SubmessageV1.delimited_overrun SubmessageV1.callback SubmessageV1.sliceBuf ctx limit after.len source after () rfl overrunScalar
      have finite : InnerScanV1.FiniteRun (SubmessageV1.body ctx limit) (source,before,())
          (.ok (.Err (SubmessageV1.decodeError .DelimitedLengthExceeded),source,after)) := .next body (.done finished)
      exact ⟨InnerScanV1.finite_run_actual finite,post⟩

#print axioms actual_unknown_group_parent_all
end ChatResponseReference.StreamingUnknownV1
