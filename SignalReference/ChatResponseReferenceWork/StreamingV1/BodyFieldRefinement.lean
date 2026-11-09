import ChatResponseReferenceWork.StreamingV1.BodyDispatch
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

def BodyStartSpan (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) : Prop :=
  ∃ leading byte tail,
    contents before = leading ++ byte::tail ∧ contents after = tail ∧
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
    next.bodyLength = native.bv ∧ next.bodyPresent = 255 ∧ next.skip = native.bv ∧
    next.modes = if native.bv = BitVec.ofNat 64 0 then lane 0 else lane 3

theorem copied_body_length (after : Slice U8) (native : U64) (fits : native.val ≤ after.length) :
    (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val).length = native.val := by
  rw [BytesContentV1.payload_length after native fits]
  change (after.val.take native.val).length = native.val
  rw [List.length_take]
  exact Nat.min_eq_left fits

theorem body_field_success (source : InnerResponseV1.Message) (after : Slice U8) (native : U64)
    (fits : native.val ≤ after.length) :
    bodyFieldDecoded source (.Ok native) after = .ok (.Ok (),
      {source with body := some ⟨ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val⟩},
      LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) := by
  simp only [bodyFieldDecoded,BytesContentV1.bytesResult,if_pos fits,InnerResponseV1.stamp,bind_tc_ok]

/-- Actual generated body field on every input/native outcome. Native varint and
physical body underflow errors imply actual Core EOF rejection. Successful copy
retains exact contents/suffix; its Core length/presence/mode is derived, without
assuming complete message validity or hiding source failed-record effects. -/
theorem actual_body_field_refinement (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (kinds : state.kinds = [0,255,0,0]) :
    ∃ decoded after,
      PrefixPost before decoded after ∧ ErrorPost before decoded after ∧
      ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (4#u32) .LengthDelimited before ctx =
        bodyFieldDecoded source decoded after ∧
      match decoded with
      | .Err _ => (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
      | .Ok native => BodyStartSpan state before after native ∧
          if native.val ≤ after.length then
            bodyFieldDecoded source decoded after = .ok (.Ok (),
              {source with body := some ⟨ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val⟩},
              LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
            (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val).length = native.val
          else (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨decoded,after,run,prefixPost,errorPost⟩ := decode_full_reference before
  refine ⟨decoded,after,prefixPost,errorPost,actual_body_field_decoded source before after ctx decoded run,?_⟩
  cases decoded with
  | Err error =>
    exact any_native_varint_error_reject state before after error 2 (by decide) modes positions value (.inl (by decide)) run
  | Ok native =>
    refine ⟨native_body_length_transition state before after native modes positions value kinds run,?_⟩
    by_cases fits : native.val ≤ after.length
    · rw [if_pos fits]
      exact ⟨body_field_success source after native fits,copied_body_length after native fits⟩
    · rw [if_neg fits]
      exact native_body_underflow_reject state before after native modes positions value kinds (by omega) run

#print axioms copied_body_length
#print axioms body_field_success
#print axioms actual_body_field_refinement
end ChatResponseReference.StreamingV1
