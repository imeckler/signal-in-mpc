import ChatResponseReferenceWork.StreamingUnknownV1.LengthKeyReady
import ChatResponseReferenceWork.StreamingUnknownV1.LengthSource
import ChatResponseReferenceWork.StreamingUnknownV1.PendingKey
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Exact actual error callback and full Core rejection for unknown length varints,
including keys that exhaust/cross the child before any value is attempted. -/
theorem actual_unknown_length_error_iteration (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8)
    (error : LoopSupportSkip.error.DecodeError) (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Err error,after)) :
    SubmessageV1.callback.call_mut () (source,before,ctx) =
      .ok (.Err (ActualResponseBytesV1.fromSkipError error),(),source,after) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have fieldRun := unknown_length_from_decode source tag middle after ctx unknownTag count (.Err error) valueRun
  refine ⟨actual_response_callback source source before middle after tag .LengthDelimited ctx (.Err (ActualResponseBytesV1.fromSkipError error)) keyRun fieldRun,?_⟩
  by_cases inside : before.length-remaining < middle.length
  · obtain ⟨keyConsumed,keySpan,keyCache,keyReady,keyModes,keyUnknown,keyKinds⟩ :=
      actual_unknown_length_key_ready outer source state before middle tag budget remaining boundary cache positive inside unknownTag keyRun
    have rejected := any_native_varint_error_reject (feed state keyConsumed) middle after error 2 (by decide)
      keyModes keyReady.positions keyReady.value (.inl (by decide)) valueRun
    rw [keySpan]
    simpa only [feed,List.foldl_append] using rejected
  · exact actual_pending_key_not_inside_reject state before middle tag .LengthDelimited budget remaining (.inr (.inr (.inl rfl))) boundary positive (by omega) keyRun

theorem actual_unknown_length_error_loop_step (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8)
    (error : LoopSupportSkip.error.DecodeError) (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (limit : Usize) (limitExact : limit.val = before.length-remaining)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Err error,after)) :
    SubmessageV1.body ctx limit (source,before,()) =
      .ok (.done (.Err (ActualResponseBytesV1.fromSkipError error),source,after)) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨called,rejected⟩ := actual_unknown_length_error_iteration outer source tag state before middle after error ctx budget remaining
    unknownTag count boundary cache positive keyRun valueRun
  exact ⟨actual_response_step_error source source before after ctx limit _
    (by rw [limitExact]; have := boundary.physical; omega) called,rejected⟩

#print axioms actual_unknown_length_error_iteration
#print axioms actual_unknown_length_error_loop_step
end ChatResponseReference.StreamingUnknownV1
