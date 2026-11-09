import ChatResponseReferenceWork.StreamingUnknownV1.LengthUnderflow
import ChatResponseReferenceWork.StreamingV1.ChildLengthOverrun
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Prost may successfully consume an unknown length-delimited field past its child in the
parent buffer. The exact callback is retained; Core rejects the full input. -/
theorem actual_unknown_length_overrun_iteration (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8) (native : U64)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (physical : native.val ≤ after.length)
    (overrun : (drop after native.val).length < before.length-remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Ok (),(),source,drop after native.val) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have fieldRun := unknown_length_from_decode source tag middle after ctx unknownTag count (.Ok native) valueRun
  have exactResult : unknownLengthResult source (.Ok native) after = (.Ok (),source,drop after native.val) := by
    simp only [unknownLengthResult,unchangedSkipResult,LibSignalReference.Candidate.ProstSkip.fixedResult,if_neg (by omega : ¬after.length < native.val)]
    rfl
  rw [exactResult] at fieldRun
  refine ⟨actual_response_callback source source before middle (drop after native.val) tag .LengthDelimited ctx (.Ok ()) keyRun fieldRun,?_⟩
  by_cases inside : before.length-remaining < middle.length
  · obtain ⟨keyConsumed,keySpan,keyCache,keyReady,keyModes,keyUnknown,keyKinds⟩ :=
      actual_unknown_length_key_ready outer source state before middle tag budget remaining boundary cache positive inside unknownTag keyRun
    have keyLength : before.length = keyConsumed.length+middle.length := by
      have result := congrArg List.length keySpan
      simpa only [contents,List.length_map,List.length_append] using result
    have rejected := native_length_child_overrun_reject (feed state keyConsumed) middle after native
      (remaining-keyConsumed.length) keyReady.remainingBound keyReady.positive keyReady.physical physical
      (by have := keyReady.positive; exact (show (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val).length < middle.length-(remaining-keyConsumed.length) from by change (drop after native.val).length < _; omega))
      keyModes keyReady.positions keyReady.value keyReady.inner keyReady.childCounter valueRun
    rw [keySpan]
    simpa only [feed,List.foldl_append] using rejected
  · exact actual_pending_key_not_inside_reject state before middle tag .LengthDelimited budget remaining (.inr (.inr (.inl rfl))) boundary positive (by omega) keyRun

/-- Exact two-step source detection of child overrun, including the final actual
loop result/native suffix. It is not replaced by earlier numeric cursor state. -/
theorem actual_unknown_length_overrun_loop (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8) (native : U64)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (limit : Usize) (limitExact : limit.val = before.length-remaining)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (physical : native.val ≤ after.length)
    (overrun : (drop after native.val).length < before.length-remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
      .ok (.Err (SubmessageV1.decodeError .DelimitedLengthExceeded),source,drop after native.val) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨called,rejected⟩ := actual_unknown_length_overrun_iteration outer source tag state before middle after native ctx budget remaining
    unknownTag count boundary cache positive physical overrun keyRun valueRun
  have continued := actual_response_step_next source source before (drop after native.val) ctx limit
    (by rw [limitExact]; have := boundary.physical; omega) called
  have overrunScalar : (drop after native.val).len < limit := by scalar_tac
  have finished : SubmessageV1.body ctx limit (source,drop after native.val,()) =
      .ok (.done (.Err (SubmessageV1.decodeError .DelimitedLengthExceeded),source,drop after native.val)) :=
    SubmessageV1.delimited_overrun SubmessageV1.callback SubmessageV1.sliceBuf ctx limit (drop after native.val).len source (drop after native.val) () rfl overrunScalar
  have finite : InnerScanV1.FiniteRun (SubmessageV1.body ctx limit) (source,before,())
      (.ok (.Err (SubmessageV1.decodeError .DelimitedLengthExceeded),source,drop after native.val)) := .next continued (.done finished)
  exact ⟨InnerScanV1.finite_run_actual finite,rejected⟩

#print axioms actual_unknown_length_overrun_iteration
#print axioms actual_unknown_length_overrun_loop
end ChatResponseReference.StreamingUnknownV1
