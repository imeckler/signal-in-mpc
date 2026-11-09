import ChatResponseReferenceWork.StreamingV1.NativePendingKey
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual message String malformed/truncated length keeps its exact native
error/suffix, total clear and diagnostic Result effects; Core rejects all input. -/
theorem actual_message_length_error (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (error : LoopSupportSkip.error.DecodeError)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (sourceError : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after)) :
    merge_response InnerResponseV1.sliceBuf source (3#u32) .LengthDelimited before ctx =
      (do let observed ← InnerResponseV1.stamp diagnosticFrame2
            (.Err (fromStringError (ActualStringContentV3.fromSkipError error)))
          .ok (observed,{source with message := some (alloc.vec.Vec.new U8)},after)) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  refine ⟨?_,any_native_varint_error_reject state before after error 2 (by decide) modes positions value (.inl (by decide)) sourceError⟩
  rw [actual_message_field_decoded source before after ctx (.Err error) sourceError]
  rfl

/-- Actual Bytes malformed/truncated length preserves the exact source error
state/default/diagnostic/suffix expression; the same actual input rejects Core. -/
theorem actual_body_length_error (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (error : LoopSupportSkip.error.DecodeError)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (sourceError : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after)) :
    merge_response InnerResponseV1.sliceBuf source (4#u32) .LengthDelimited before ctx = bodyFieldDecoded source (.Err error) after ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  exact ⟨actual_body_field_decoded source before after ctx (.Err error) sourceError,
    any_native_varint_error_reject state before after error 2 (by decide) modes positions value (.inl (by decide)) sourceError⟩

#print axioms actual_message_length_error
#print axioms actual_body_length_error
end ChatResponseReference.StreamingV1
