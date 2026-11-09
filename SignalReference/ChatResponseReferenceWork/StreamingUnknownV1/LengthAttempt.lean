import ChatResponseReferenceWork.StreamingUnknownV1.LengthOverrun
import ChatResponseReferenceWork.StreamingUnknownV1.LengthIteration
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def unknownLengthCallbackResult (source : InnerResponseV1.Message)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :
    core.result.Result Unit ActualInnerResponseV1.prost.error.DecodeError × Unit × InnerResponseV1.Message × Slice U8 :=
  match decoded with
  | .Err error => (.Err (ActualResponseBytesV1.fromSkipError error),(),source,after)
  | .Ok native => if native.val ≤ after.length then (.Ok (),(),source,drop after native.val)
      else (.Err fixedUnderflowError,(),source,after)

/-- Exhaustive actual unknown length-delimited field attempt. Native length,
termination, physical fit and private child fit are derived rather than supplied.
Every error retains the actual source record/error/suffix and numeric rejection. -/
theorem actual_unknown_length_attempt_all (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (limit : Usize) (limitExact : limit.val = before.length-remaining)
    (unknown : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle)) :
    ∃ decoded after,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (decoded,after) ∧
      PrefixPost middle decoded after ∧ ErrorPost middle decoded after ∧
      SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (unknownLengthCallbackResult source decoded after) ∧
      match decoded with
      | .Err error =>
        ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
          .ok (.Err (ActualResponseBytesV1.fromSkipError error),source,after) ∧
        (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
      | .Ok native =>
        if native.val ≤ after.length then
          if native.val + (before.length-after.length) ≤ remaining then
            SubmessageV1.body ctx limit (source,before,()) = .ok (.cont (source,drop after native.val,())) ∧
            ∃ consumed,
              contents before = consumed ++ contents (drop after native.val) ∧ CacheAgrees outer source (feed state consumed) ∧
              ChildAtKey (feed state consumed) (drop after native.val) (budget-consumed.length) (remaining-consumed.length)
          else
            ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
              .ok (.Err (SubmessageV1.decodeError .DelimitedLengthExceeded),source,drop after native.val) ∧
            (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
        else
          ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
            .ok (.Err fixedUnderflowError,source,after) ∧
          (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨decoded,after,actual,prefixPost,errorPost⟩ := decode_full_reference middle
  refine ⟨decoded,after,actual,prefixPost,errorPost,?_⟩
  cases decoded with
  | Err error =>
    obtain ⟨called,rejected⟩ := actual_unknown_length_error_iteration outer source tag state before middle after error ctx budget remaining
      unknown count boundary cache positive keyRun actual
    obtain ⟨step,_⟩ := actual_unknown_length_error_loop_step outer source tag state before middle after error ctx budget remaining limit limitExact
      unknown count boundary cache positive keyRun actual
    exact ⟨called,InnerScanV1.finite_run_actual (.done step),rejected⟩
  | Ok native =>
    by_cases physical : native.val ≤ after.length
    · simp only [unknownLengthCallbackResult,if_pos physical]
      have fieldRun := unknown_length_from_decode source tag middle after ctx unknown count (.Ok native) actual
      have exactResult : unknownLengthResult source (.Ok native) after = (.Ok (),source,drop after native.val) := by
        simp only [unknownLengthResult,unchangedSkipResult,LibSignalReference.Candidate.ProstSkip.fixedResult,if_neg (by omega : ¬after.length < native.val)]
        rfl
      rw [exactResult] at fieldRun
      refine ⟨actual_response_callback source source before middle (drop after native.val) tag .LengthDelimited ctx (.Ok ()) keyRun fieldRun,?_⟩
      by_cases fits : native.val + (before.length-after.length) ≤ remaining
      · simp only [if_pos fits]
        exact actual_unknown_length_loop_step outer source tag state before middle after native ctx budget remaining limit limitExact
          unknown count boundary cache positive fits keyRun actual
      · simp only [if_neg fits]
        have decrease := actual_key_success_decreases before middle tag .LengthDelimited keyRun
        obtain ⟨leading,byte,tail,span,suffix,_,_,_,_,_⟩ := native_success_span middle after native actual
        have tailLength : tail.length = after.length := by
          have result := congrArg List.length suffix
          simpa only [contents,List.length_map] using result.symm
        have inputLength : middle.length = leading.length+1+after.length := by
          have result := congrArg List.length span
          simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
        have dropped : (drop after native.val).length = after.length-native.val := by
          change (after.val.drop native.val).length = _
          rw [List.length_drop]
        exact actual_unknown_length_overrun_loop outer source tag state before middle after native ctx budget remaining limit limitExact
          unknown count boundary cache positive physical (by rw [dropped]; omega) keyRun actual
    · simp only [unknownLengthCallbackResult,if_neg physical]
      obtain ⟨called,_⟩ := actual_unknown_length_underflow_iteration outer source tag state before middle after native ctx budget remaining
        unknown count boundary cache positive (by omega) keyRun actual
      exact ⟨called,actual_unknown_length_underflow_loop outer source tag state before middle after native ctx budget remaining limit limitExact
        unknown count boundary cache positive (by omega) keyRun actual⟩

#print axioms actual_unknown_length_attempt_all
end ChatResponseReference.StreamingUnknownV1
