import ChatResponseReferenceWork.StreamingUnknownV1.GroupEventPrimitives
import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyEntry
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipKey

/-- The exact prefix already used by the full state theorem has the native
varint event trace: suffix cancellation removes any independent span witness. -/
theorem native_key_scalar_exact_trace_zero (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (value : U64) (role : Nat) (bounded : role ≤ 1)
    (modes : state.modes = lane role) (consumed : List (BitVec 8))
    (span : contents before = consumed++contents after)
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,after)) :
    bodyTrace state consumed = consumed.map (fun byte => (0,0,0,byte)) := by
  obtain ⟨used,usedSpan,events⟩ := native_key_scalar_trace_zero state before after value role bounded modes actual
  have same : used = consumed := List.append_cancel_right (usedSpan.symm.trans span)
  simpa only [same] using events

/-- Every accepted actual source group key, including schema-looking inner
tags and every wire kind, emits zero events on precisely its consumed prefix. -/
theorem actual_group_key_trace_zero (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : WireType) (consumed : List (BitVec 8))
    (modes : state.modes = lane 0) (span : contents before = consumed++contents after)
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    bodyTrace state consumed = consumed.map (fun byte => (0,0,0,byte)) := by
  obtain ⟨value,native,accepted⟩ := native_key_success_varint before after tag wire actual
  exact native_key_scalar_exact_trace_zero state before after value 0 (by decide) modes consumed span native

#print axioms native_key_scalar_exact_trace_zero
#print axioms actual_group_key_trace_zero
end ChatResponseReference.StreamingUnknownV1
