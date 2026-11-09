import ChatResponseReferenceWork.StreamingV1.StringFieldResults
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual source invalid-UTF8 String result (including total clear, diagnostics
and exact suffix) and actual Core rejection refer to the same copied bytes.
The post-header state is explicit; its derivation and full scan remain separate. -/
theorem actual_message_utf_rejection (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (ctx : prost.encoding.DecodeContext) (fits : native.val ≤ after.length)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after))
    (bounded : ((copiedString after native).val.map (fun byte => byte.bv)).length < 2^64)
    (modes : state.modes = lane 3)
    (skip : state.skip = BitVec.ofNat 64 ((copiedString after native).val.map (fun byte => byte.bv)).length)
    (kindsShape : state.kinds.length = 4)
    (stringKind : TlsWebSocketUpgrade.either ByteAuth.concrete
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 2)
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 3) = 255)
    (utf : state.utf = Utf8.encode .ready)
    (bad : Utf8.accepts ((copiedString after native).val.map (fun byte => byte.bv)) = false) :
    merge_response InnerResponseV1.sliceBuf source (3#u32) .LengthDelimited before ctx =
      (do let observed ← InnerResponseV1.stamp diagnosticFrame2
            (.Err (fromStringError (StringContentV3.decodeError .InvalidString)))
          .ok (observed,{source with message := some (alloc.vec.Vec.new U8)},LibSignalReference.Candidate.ProstBytesBuf.drop after native.val)) ∧
    (feed state ((copiedString after native).val.map (fun byte => byte.bv))).valid = 0 := by
  refine ⟨?_,?_⟩
  · rw [actual_message_field_decoded source before after ctx (.Ok native) sourceSuccess]
    exact message_field_utf_failure source after native fits bad
  · have nonempty : (copiedString after native).val.map (fun byte => byte.bv) ≠ [] := by
      intro empty
      rw [empty] at bad
      cases bad
    exact string_payload_utf_reject state _ nonempty bounded modes skip kindsShape stringKind utf bad

#print axioms actual_message_utf_rejection
end ChatResponseReference.StreamingV1
