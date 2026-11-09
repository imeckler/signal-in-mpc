import ChatResponseReferenceWork.StreamingV1.WrongWireRejection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

def idFieldDecoded (state : InnerResponseV1.Message)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :=
  let scalar := InnerResponseV1.scalarResult64 (state.id.getD core.default.DefaultU64.default) decoded after
  do
    let observed ← InnerResponseV1.stamp diagnosticFrame0 scalar.1
    Result.ok (observed,{state with id := some scalar.2.1},scalar.2.2)

def statusFieldDecoded (state : InnerResponseV1.Message)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :=
  let scalar := InnerResponseV1.scalarResult32 (state.status.getD core.default.DefaultU32.default) decoded after
  do
    let observed ← InnerResponseV1.stamp diagnosticFrame1 scalar.1
    Result.ok (observed,{state with status := some scalar.2.1},scalar.2.2)

/-- Actual generated ID dispatcher, including None→Some(default) initialization
before native decode Err, duplicate overwrite and exact diagnostic fail/div. -/
theorem actual_id_field_decoded (state : InnerResponseV1.Message) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (run : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (decoded,after)) :
    merge_response InnerResponseV1.sliceBuf state (1#u32) .Varint before ctx = idFieldDecoded state decoded after := by
  rw [InnerResponseV1.dispatcher_reference]
  change InnerResponseV1.optionalField state.id (.ok core.default.DefaultU64.default)
    (fun old => prost.encoding.uint64.merge InnerResponseV1.sliceBuf .Varint old before ctx)
    (fun next => {state with id := some next}) diagnosticFrame0 = _
  cases initial : state.id with
  | none =>
    simp only [InnerResponseV1.optionalField,initial,bind_tc_ok,idFieldDecoded,Option.getD_none]
    rw [InnerResponseV1.uint64_from_decode _ before after ctx decoded run]
    rfl
  | some old =>
    simp only [InnerResponseV1.optionalField,initial,bind_tc_ok,idFieldDecoded,Option.getD_some]
    rw [InnerResponseV1.uint64_from_decode _ before after ctx decoded run]
    rfl

/-- Actual generated status dispatcher has the same all-outcomes observation,
with exactly the pinned U64→U32 truncation and old/default mutation semantics. -/
theorem actual_status_field_decoded (state : InnerResponseV1.Message) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (run : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (decoded,after)) :
    merge_response InnerResponseV1.sliceBuf state (2#u32) .Varint before ctx = statusFieldDecoded state decoded after := by
  rw [InnerResponseV1.dispatcher_reference]
  change InnerResponseV1.optionalField state.status (.ok core.default.DefaultU32.default)
    (fun old => prost.encoding.uint32.merge InnerResponseV1.sliceBuf .Varint old before ctx)
    (fun next => {state with status := some next}) diagnosticFrame1 = _
  cases initial : state.status with
  | none =>
    simp only [InnerResponseV1.optionalField,initial,bind_tc_ok,statusFieldDecoded,Option.getD_none]
    rw [InnerResponseV1.uint32_from_decode _ before after ctx decoded run]
    rfl
  | some old =>
    simp only [InnerResponseV1.optionalField,initial,bind_tc_ok,statusFieldDecoded,Option.getD_some]
    rw [InnerResponseV1.uint32_from_decode _ before after ctx decoded run]
    rfl

#print axioms actual_id_field_decoded
#print axioms actual_status_field_decoded
end ChatResponseReference.StreamingV1
