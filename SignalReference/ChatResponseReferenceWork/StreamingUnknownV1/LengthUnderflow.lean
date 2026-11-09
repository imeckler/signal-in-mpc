import ChatResponseReferenceWork.StreamingUnknownV1.LengthErrors
import ChatResponseReferenceWork.StreamingUnknownV1.LengthTransition
import ChatResponseReferenceWork.StreamingUnknownV1.FixedErrors
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Physical payload underflow returns the actual post-length suffix, rather
than the post-key suffix. The source record is unchanged and Core rejects. -/
theorem actual_unknown_length_underflow_iteration (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8) (native : U64)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (unknown : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (underflow : after.length < native.val)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (lengthRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Err fixedUnderflowError,(),source,after) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have fieldRun := unknown_length_from_decode source tag middle after ctx unknown count (.Ok native) lengthRun
  simp only [unknownLengthResult,LibSignalReference.Candidate.ProstSkip.fixedResult,if_pos underflow,
    unchangedSkipResult,InnerResponseV1.skipResult] at fieldRun
  refine ⟨actual_response_callback source source before middle after tag .LengthDelimited ctx (.Err fixedUnderflowError) keyRun fieldRun,?_⟩
  by_cases inside : before.length-remaining < middle.length
  · obtain ⟨keyConsumed,keySpan,keyCache,keyReady,keyModes,keyUnknown,keyKinds⟩ :=
      actual_unknown_length_key_ready outer source state before middle tag budget remaining boundary cache positive inside unknown keyRun
    have rejected := native_unknown_length_underflow_reject (feed state keyConsumed) middle after native keyModes keyReady.positions keyReady.value keyKinds underflow lengthRun
    rw [keySpan]
    simpa only [feed,List.foldl_append] using rejected
  · exact actual_pending_key_not_inside_reject state before middle tag .LengthDelimited budget remaining
      (.inr (.inr (.inl rfl))) boundary positive (by omega) keyRun

theorem actual_unknown_length_underflow_loop (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8) (native : U64)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (limit : Usize) (limitExact : limit.val = before.length-remaining)
    (unknown : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (underflow : after.length < native.val)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (lengthRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
      .ok (.Err fixedUnderflowError,source,after) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨called,rejected⟩ := actual_unknown_length_underflow_iteration outer source tag state before middle after native ctx budget remaining unknown count
    boundary cache positive underflow keyRun lengthRun
  have step := actual_response_step_error source source before after ctx limit fixedUnderflowError
    (by rw [limitExact]; have := boundary.physical; omega) called
  exact ⟨InnerScanV1.finite_run_actual (.done step),rejected⟩

#print axioms actual_unknown_length_underflow_iteration
#print axioms actual_unknown_length_underflow_loop
end ChatResponseReference.StreamingUnknownV1
