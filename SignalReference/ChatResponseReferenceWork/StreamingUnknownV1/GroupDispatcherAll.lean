import ChatResponseReferenceWork.StreamingUnknownV1.GroupDispatcher
import ChatResponseReferenceWork.StreamingUnknownV1.UnknownStartBoundary
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkip
open LoopSupportSkip
set_option maxHeartbeats 2000000

/-- Exhaustive actual unknown StartGroup callback, including a key that itself
exhausts/crosses the private child. Physical native group result/termination
are derived; native error and source success outside the child remain exact. -/
theorem actual_unknown_group_callback_all (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8) (tag : U32)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (unknown : 5 < tag.val) (context : ctx.recurse_count = 99#u32)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.StartGroup),middle)) :
    ∃ result,
      encoding.skip_field_loop sliceBuf tag middle ⟨99#u32⟩ = .ok result ∧
      SubmessageV1.callback.call_mut () (source,before,ctx) =
        .ok ((InnerResponseV1.skipResult result).1,(),source,(InnerResponseV1.skipResult result).2) ∧
      GroupOutcome outer source state before budget remaining [] (99#u32) result := by
  by_cases inside : before.length-remaining < middle.length
  · exact actual_unknown_group_callback outer source state before middle tag ctx budget remaining boundary cache positive inside unknown context keyRun
  · have exhausted : middle.length ≤ before.length-remaining := by omega
    have rejected := unknown_start_key_not_inside_reject state before middle tag budget remaining boundary positive exhausted keyRun
    obtain ⟨result,derivation,run,bound⟩ := FullParserV3.skip_group_total tag (99#u32) middle (by decide)
    have nativeSkip : encoding.skip_field sliceBuf .StartGroup tag middle ⟨ctx.recurse_count⟩ = .ok result := by
      rw [context,start_group middle tag (99#u32) (by decide)]
      exact run
    have field := unknown_from_native_skip source tag .StartGroup middle ctx unknown result nativeSkip
    refine ⟨result,run,?_,?_⟩
    · exact actual_response_callback source source before middle (InnerResponseV1.skipResult result).2 tag .StartGroup ctx
        (InnerResponseV1.skipResult result).1 keyRun field
    · apply group_outcome_of_rejected outer source state before budget remaining [] (99#u32) result rejected
      intro success
      have strict := group_grammar_success_decreases derivation (by decide) success
      omega

/-- Complete parent-loop body result for the exhaustive callback. Successful
native private overruns really continue before the parent's later limit error;
Core rejection does not rewrite that source control or suffix. -/
theorem actual_unknown_group_loop_step_all (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8) (tag : U32)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (limit : Usize)
    (limitExact : limit.val = before.length-remaining)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (unknown : 5 < tag.val) (context : ctx.recurse_count = 99#u32)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.StartGroup),middle)) :
    ∃ result,
      encoding.skip_field_loop sliceBuf tag middle ⟨99#u32⟩ = .ok result ∧
      SubmessageV1.body ctx limit (source,before,()) = .ok
        (match (InnerResponseV1.skipResult result).1 with
         | .Ok () => .cont (source,(InnerResponseV1.skipResult result).2,())
         | .Err error => .done (.Err error,source,(InnerResponseV1.skipResult result).2)) ∧
      GroupOutcome outer source state before budget remaining [] (99#u32) result := by
  obtain ⟨result,run,called,post⟩ := actual_unknown_group_callback_all outer source state before middle tag ctx budget remaining boundary cache positive unknown context keyRun
  have more : limit.val < before.length := by rw [limitExact]; have := boundary.physical; omega
  refine ⟨result,run,?_,post⟩
  rcases result with ⟨status,after⟩
  cases status with
  | Err error => exact actual_response_step_error source source before after ctx limit _ more called
  | Ok unitValue =>
    cases unitValue
    exact actual_response_step_next source source before after ctx limit more called

#print axioms actual_unknown_group_callback_all
#print axioms actual_unknown_group_loop_step_all
end ChatResponseReference.StreamingUnknownV1
