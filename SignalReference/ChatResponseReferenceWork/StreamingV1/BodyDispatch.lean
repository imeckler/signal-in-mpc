import ChatResponseReferenceWork.StreamingV1.NativeBodyLength
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

def emptyBody : bytes.bytes.Bytes := ⟨⟨[],by simp⟩⟩

def bodyFieldDecoded (state : InnerResponseV1.Message)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (afterLength : Slice U8) :=
  let payload := BytesContentV1.bytesResult (state.body.getD emptyBody) decoded afterLength
  do
    let observed ← InnerResponseV1.stamp diagnosticFrame3 payload.1
    Result.ok (observed,{state with body := some payload.2.1},payload.2.2)

/-- Actual generated body dispatcher composed with actual Bytes replacement and
length decode, retaining all errors, exact content/suffix, absent initialization,
duplicate replacement and diagnostic-stack effects. -/
theorem actual_body_field_decoded (state : InnerResponseV1.Message) (before afterLength : Slice U8)
    (ctx : prost.encoding.DecodeContext) (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (run : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (decoded,afterLength)) :
    merge_response InnerResponseV1.sliceBuf state (4#u32) .LengthDelimited before ctx = bodyFieldDecoded state decoded afterLength := by
  rw [InnerResponseV1.dispatcher_reference]
  change InnerResponseV1.optionalField state.body (bytes.bytes.Bytes.Insts.CoreDefaultDefault.default)
    (fun old => prost.encoding.bytes.merge bytes.bytes.Bytes.Insts.ProstEncodingBytesAdapter
      InnerResponseV1.sliceBuf .LengthDelimited old before ctx)
    (fun next => {state with body := some next}) diagnosticFrame3 = _
  have native (old : bytes.bytes.Bytes) :
      prost.encoding.bytes.merge bytes.bytes.Bytes.Insts.ProstEncodingBytesAdapter
        InnerResponseV1.sliceBuf .LengthDelimited old before ctx =
      .ok (BytesContentV1.bytesResult old decoded afterLength) := by
    rw [InnerResponseV1.bytes_source_exact]
    exact BytesContentV1.bytes_from_decode before afterLength old decoded ctx run
  have fallback : bytes.bytes.Bytes.Insts.CoreDefaultDefault.default = .ok emptyBody := rfl
  cases initial : state.body with
  | none =>
    simp only [InnerResponseV1.optionalField,initial,fallback,bind_tc_ok,bodyFieldDecoded,Option.getD_none]
    rw [native]
    rfl
  | some old =>
    simp only [InnerResponseV1.optionalField,initial,bind_tc_ok,bodyFieldDecoded,Option.getD_some]
    rw [native]
    rfl

#print axioms actual_body_field_decoded
end ChatResponseReference.StreamingV1
