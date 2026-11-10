import ChatResponseReferenceWork.StreamingUnknownV1.GroupRefinement
import ChatResponseReferenceWork.StreamingUnknownV1.StartKeyReady
import ChatResponseReferenceWork.StreamingUnknownV1.FixedSource
import ChatResponseReferenceWork.StreamingV1.MessageErrorLoop
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkip
open LoopSupportSkip
set_option maxHeartbeats 2000000

/-- Actual generated unknown-group dispatch and callback compose the complete
native group scan with its numeric all-outcome observation. This is a real
callback result (with error projection), not assumed skip correctness. -/
theorem actual_unknown_group_callback (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8) (tag : U32)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (fits : before.length-remaining < middle.length) (unknown : 5 < tag.val)
    (context : ctx.recurse_count = 99#u32)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.StartGroup),middle)) :
    ∃ result,
      encoding.skip_field_loop sliceBuf tag middle ⟨99#u32⟩ = .ok result ∧
      SubmessageV1.callback.call_mut () (source,before,ctx) =
        .ok ((InnerResponseV1.skipResult result).1,(),source,(InnerResponseV1.skipResult result).2) ∧
      GroupOutcome outer source state before budget remaining [] (99#u32) result := by
  obtain ⟨header,span,nextCache,nextReady,known,kinds⟩ := actual_unknown_start_key_ready outer source state before middle tag budget remaining boundary cache positive fits unknown keyRun
  obtain ⟨result,run,post⟩ := actual_inner_group_refinement outer source middle (feed state header) tag (99#u32) [] (budget-header.length) (remaining-header.length) nextReady nextCache
  have nativeSkip : encoding.skip_field sliceBuf .StartGroup tag middle ⟨ctx.recurse_count⟩ = .ok result := by
    rw [context,start_group middle tag (99#u32) (by decide)]
    exact run
  have field := unknown_from_native_skip source tag .StartGroup middle ctx unknown result nativeSkip
  refine ⟨result,run,?_,?_⟩
  · exact actual_response_callback source source before middle (InnerResponseV1.skipResult result).2 tag .StartGroup ctx
      (InnerResponseV1.skipResult result).1 keyRun field
  · apply group_outcome_prefix outer source state before middle budget remaining [] (99#u32) result header span _ post
    have lengths : before.length = header.length+middle.length := by
      simpa only [contents,List.length_map,List.length_append] using congrArg List.length span
    omega

/-- Preserve the actual parent-loop control: even when a source group succeeds
past its private child and Core rejects, the real parent body first continues
with that native suffix; its later limit check remains a separate source step. -/
theorem actual_unknown_group_loop_step (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8) (tag : U32)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (limit : Usize)
    (limitExact : limit.val = before.length-remaining)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (fits : before.length-remaining < middle.length) (unknown : 5 < tag.val)
    (context : ctx.recurse_count = 99#u32)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.StartGroup),middle)) :
    ∃ result,
      encoding.skip_field_loop sliceBuf tag middle ⟨99#u32⟩ = .ok result ∧
      SubmessageV1.body ctx limit (source,before,()) = .ok
        (match (InnerResponseV1.skipResult result).1 with
         | .Ok () => .cont (source,(InnerResponseV1.skipResult result).2,())
         | .Err error => .done (.Err error,source,(InnerResponseV1.skipResult result).2)) ∧
      GroupOutcome outer source state before budget remaining [] (99#u32) result := by
  obtain ⟨result,run,called,post⟩ := actual_unknown_group_callback outer source state before middle tag ctx budget remaining boundary cache positive fits unknown context keyRun
  have more : limit.val < before.length := by rw [limitExact]; have := boundary.physical; omega
  refine ⟨result,run,?_,post⟩
  rcases result with ⟨status,after⟩
  cases status with
  | Err error => exact actual_response_step_error source source before after ctx limit _ more called
  | Ok unitValue =>
    cases unitValue
    exact actual_response_step_next source source before after ctx limit more called

#print axioms actual_unknown_group_callback
#print axioms actual_unknown_group_loop_step
end ChatResponseReference.StreamingUnknownV1
