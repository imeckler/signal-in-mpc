import ChatResponseReferenceWork.StreamingUnknownV1.FixedErrors
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem actual_unknown_fixed_overrun_iteration (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (wide : Bool)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (positive : 0 < remaining)
    (physical : (if wide then 8 else 4) ≤ middle.length)
    (notFit : ¬(if wide then 8 else 4) + (before.length-middle.length) ≤ remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before =
      .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Ok (),(),source,drop middle (if wide then 8 else 4)) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have fieldRun := unknown_fixed_source_all source tag middle ctx wide unknownTag count
  simp only [LibSignalReference.Candidate.ProstSkip.fixedResult,if_neg (by omega : ¬middle.length < (if wide then 8 else 4)),
    unchangedSkipResult,InnerResponseV1.skipResult] at fieldRun
  exact ⟨actual_response_callback source source before middle _ tag _ ctx (.Ok ()) keyRun fieldRun,
    actual_fixed_key_not_fit_reject state before middle tag budget remaining wide boundary positive notFit keyRun⟩

theorem actual_unknown_fixed_overrun_loop (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (wide : Bool)
    (limit : Usize) (limitExact : limit.val = before.length-remaining)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (positive : 0 < remaining)
    (physical : (if wide then 8 else 4) ≤ middle.length)
    (notFit : ¬(if wide then 8 else 4) + (before.length-middle.length) ≤ remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before =
      .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
      .ok (.Err (SubmessageV1.decodeError .DelimitedLengthExceeded),source,drop middle (if wide then 8 else 4)) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨called,rejected⟩ := actual_unknown_fixed_overrun_iteration source tag state before middle ctx budget remaining wide unknownTag count
    boundary positive physical notFit keyRun
  have continued := actual_response_step_next source source before _ ctx limit
    (by rw [limitExact]; have := boundary.physical; omega) called
  have keyStrict := actual_key_success_decreases before middle tag _ keyRun
  have afterLength := LibSignalReference.Candidate.ProstSkipBuf.drop_length middle (if wide then 8 else 4)
  have overrunScalar : (drop middle (if wide then 8 else 4)).len < limit := by
    have overrun : (drop middle (if wide then 8 else 4)).length < limit.val := by have := boundary.physical; omega
    scalar_tac
  have finished : SubmessageV1.body ctx limit (source,drop middle (if wide then 8 else 4),()) =
      .ok (.done (.Err (SubmessageV1.decodeError .DelimitedLengthExceeded),source,drop middle (if wide then 8 else 4))) :=
    SubmessageV1.delimited_overrun SubmessageV1.callback SubmessageV1.sliceBuf ctx limit _ source _ () rfl overrunScalar
  have finite : InnerScanV1.FiniteRun (SubmessageV1.body ctx limit) (source,before,())
      (.ok (.Err (SubmessageV1.decodeError .DelimitedLengthExceeded),source,drop middle (if wide then 8 else 4))) := .next continued (.done finished)
  exact ⟨InnerScanV1.finite_run_actual finite,rejected⟩

#print axioms actual_unknown_fixed_overrun_iteration
#print axioms actual_unknown_fixed_overrun_loop
end ChatResponseReference.StreamingUnknownV1
