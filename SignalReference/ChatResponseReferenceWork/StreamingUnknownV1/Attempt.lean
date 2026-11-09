import ChatResponseReferenceWork.StreamingUnknownV1.Overrun
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def unknownCallbackResult (source : InnerResponseV1.Message)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :
    core.result.Result Unit ActualInnerResponseV1.prost.error.DecodeError × Unit × InnerResponseV1.Message × Slice U8 :=
  match decoded with
  | .Ok _ => (.Ok (),(),source,after)
  | .Err error => (.Err (ActualResponseBytesV1.fromSkipError error),(),source,after)

/-- Exhaustive actual unknown-varint field attempt following an actual key.
Native outcomes are derived, not supplied; source mutation/error/suffix and
post-callback child-overrun detection are retained separately from Core rejection. -/
theorem actual_unknown_varint_attempt_all (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (limit : Usize) (limitExact : limit.val = before.length-remaining)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.Varint),middle)) :
    ∃ decoded after,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (decoded,after) ∧
      PrefixPost middle decoded after ∧ ErrorPost middle decoded after ∧
      SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (unknownCallbackResult source decoded after) ∧
      match decoded with
      | .Ok _ =>
        if before.length-remaining ≤ after.length then
          SubmessageV1.body ctx limit (source,before,()) = .ok (.cont (source,after,())) ∧
          ∃ consumed,
            contents before = consumed ++ contents after ∧ CacheAgrees outer source (feed state consumed) ∧
            ChildAtKey (feed state consumed) after (budget-consumed.length) (remaining-consumed.length)
        else
          ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
            .ok (.Err (SubmessageV1.decodeError .DelimitedLengthExceeded),source,after) ∧
          (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
      | .Err error =>
        ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
          .ok (.Err (ActualResponseBytesV1.fromSkipError error),source,after) ∧
        (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨decoded,after,actual,prefixPost,errorPost⟩ := decode_full_reference middle
  refine ⟨decoded,after,actual,prefixPost,errorPost,?_⟩
  cases decoded with
  | Ok native =>
    have fieldRun := unknown_varint_from_decode source tag middle after ctx unknownTag count (.Ok native) actual
    refine ⟨actual_response_callback source source before middle after tag .Varint ctx (.Ok ()) keyRun fieldRun,?_⟩
    by_cases fits : before.length-remaining ≤ after.length
    · simp only [if_pos fits]
      exact actual_unknown_varint_loop_step outer source tag state before middle after native ctx budget remaining limit
        unknownTag count limitExact boundary cache positive fits keyRun actual
    · simp only [if_neg fits]
      exact actual_unknown_varint_overrun_loop outer source tag state before middle after native ctx budget remaining limit limitExact
        unknownTag count boundary cache positive (by omega) keyRun actual
  | Err error =>
    obtain ⟨called,rejected⟩ := actual_unknown_varint_error_iteration outer source tag state before middle after error ctx budget remaining
      unknownTag count boundary cache positive keyRun actual
    obtain ⟨step,_⟩ := actual_unknown_varint_error_loop_step outer source tag state before middle after error ctx budget remaining limit limitExact
      unknownTag count boundary cache positive keyRun actual
    exact ⟨called,InnerScanV1.finite_run_actual (.done step),rejected⟩

#print axioms actual_unknown_varint_attempt_all
end ChatResponseReference.StreamingUnknownV1
