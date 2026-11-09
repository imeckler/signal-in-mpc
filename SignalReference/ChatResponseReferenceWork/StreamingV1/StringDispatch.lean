import ChatResponseReferenceWork.StreamingV1.StringPayloadRejection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

def messageFieldDecoded (state : InnerResponseV1.Message)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (afterLength : Slice U8) :=
  let payload := InnerResponseV1.strongStringResult
    (StringContentV3.stringResult (StringContentV3.bytesResult (state.message.getD (alloc.vec.Vec.new U8)) decoded afterLength))
  do
    let observed ← InnerResponseV1.stamp diagnosticFrame2 payload.1
    Result.ok (observed,{state with message := some payload.2.1},payload.2.2)

/-- Actual generated message-String branch, preserving initialization, duplicate
replacement, total clear on every String error, native suffix and diagnostic
mutation/failure/divergence. UTF8 is the explicit executable content boundary. -/
theorem actual_message_field_decoded (state : InnerResponseV1.Message) (before afterLength : Slice U8)
    (ctx : prost.encoding.DecodeContext) (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (run : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (decoded,afterLength)) :
    merge_response InnerResponseV1.sliceBuf state (3#u32) .LengthDelimited before ctx = messageFieldDecoded state decoded afterLength := by
  rw [InnerResponseV1.dispatcher_reference]
  change InnerResponseV1.optionalField state.message (.ok (alloc.vec.Vec.new U8))
    (fun old => prost.encoding.string.merge InnerResponseV1.sliceBuf .LengthDelimited old before ctx)
    (fun next => {state with message := some next}) diagnosticFrame2 = _
  have native (old : ActualInnerResponseV1.String) :
      prost.encoding.string.merge InnerResponseV1.sliceBuf .LengthDelimited old before ctx =
      .ok (InnerResponseV1.strongStringResult (StringContentV3.stringResult (StringContentV3.bytesResult old decoded afterLength))) := by
    rw [InnerResponseV1.string_all_outcomes,InnerResponseV1.string_buffer_exact]
    change (do let result ← ActualStringContentV3.encoding.string.merge StringContentV3.sliceBuf .LengthDelimited old before (stringCtx ctx)
               .ok (InnerResponseV1.strongStringResult result)) = _
    rw [StringContentV3.string_from_decode before afterLength old decoded (stringCtx ctx) run]
    rfl
  cases initial : state.message with
  | none =>
    simp only [InnerResponseV1.optionalField,initial,bind_tc_ok,messageFieldDecoded,Option.getD_none]
    rw [native]
    rfl
  | some old =>
    simp only [InnerResponseV1.optionalField,initial,bind_tc_ok,messageFieldDecoded,Option.getD_some]
    rw [native]
    rfl

#print axioms actual_message_field_decoded
end ChatResponseReference.StreamingV1
