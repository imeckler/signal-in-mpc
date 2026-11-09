import ChatResponseReferenceWork.StreamingUnknownV1.FixedNoFit
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def fixedUnderflowError := ActualResponseBytesV1.fromSkipError
  (LibSignalReference.Candidate.ProstSkip.decodeError .BufferUnderflow)

theorem actual_key_success_decreases (before after : Slice U8) (tag : U32)
    (wire : ActualInnerScanV1.prost.encoding.wire_type.WireType)
    (actual : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,wire),after)) :
    after.length < before.length := by
  have nativeKey := actual_driver_key_native before after tag wire actual
  obtain ⟨native,run,_⟩ := native_key_success_varint before after tag _ nativeKey
  obtain ⟨leading,byte,tail,span,suffix,_,_,_,_,_⟩ := native_success_span before after native run
  have inputLength := congrArg List.length span
  have tailLength := congrArg List.length suffix
  simp only [contents,List.length_map,List.length_append,List.length_cons] at inputLength tailLength
  change before.length = leading.length+(tail.length+1) at inputLength
  change after.length = tail.length at tailLength
  omega

theorem actual_unknown_fixed_underflow_iteration (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (wide : Bool)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (positive : 0 < remaining)
    (underflow : middle.length < (if wide then 8 else 4))
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before =
      .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Err fixedUnderflowError,(),source,middle) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have fieldRun := unknown_fixed_source_all source tag middle ctx wide unknownTag count
  simp only [LibSignalReference.Candidate.ProstSkip.fixedResult,if_pos underflow,
    unchangedSkipResult,InnerResponseV1.skipResult] at fieldRun
  exact ⟨actual_response_callback source source before middle middle tag _ ctx (.Err fixedUnderflowError) keyRun fieldRun,
    actual_fixed_key_not_fit_reject state before middle tag budget remaining wide boundary positive (by have := boundary.physical; omega) keyRun⟩

theorem actual_unknown_fixed_underflow_loop (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (wide : Bool)
    (limit : Usize) (limitExact : limit.val = before.length-remaining)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (positive : 0 < remaining)
    (underflow : middle.length < (if wide then 8 else 4))
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before =
      .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    ActualSubmessageV1.prost.encoding.merge_loop_loop SubmessageV1.callback SubmessageV1.sliceBuf source before ctx () limit =
      .ok (.Err fixedUnderflowError,source,middle) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨called,rejected⟩ := actual_unknown_fixed_underflow_iteration source tag state before middle ctx budget remaining wide unknownTag count
    boundary positive underflow keyRun
  have step := actual_response_step_error source source before middle ctx limit fixedUnderflowError
    (by rw [limitExact]; have := boundary.physical; omega) called
  exact ⟨InnerScanV1.finite_run_actual (.done step),rejected⟩

#print axioms actual_key_success_decreases
#print axioms actual_unknown_fixed_underflow_iteration
#print axioms actual_unknown_fixed_underflow_loop
end ChatResponseReference.StreamingUnknownV1
