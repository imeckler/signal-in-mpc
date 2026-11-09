import ChatResponseReferenceWork.StreamingV1.BodySuccessNative
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual generated message String success forces the real native length/copy
and executable UTF8 success, exact content and suffix. No native-success or
UTF-validity premise is supplied; diagnostic errors cannot become success. -/
theorem actual_message_success_native (source next : InnerResponseV1.Message) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext)
    (observed : merge_response InnerResponseV1.sliceBuf source (3#u32) .LengthDelimited before ctx = .ok (.Ok (),next,after)) :
    ∃ native middle,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,middle) ∧ native.val ≤ middle.length ∧
      Utf8.accepts ((copiedString middle native).val.map (fun byte => byte.bv)) = true ∧
      next = {source with message := some (copiedString middle native)} ∧
      after = LibSignalReference.Candidate.ProstBytesBuf.drop middle native.val := by
  obtain ⟨decoded,middle,run,_,_⟩ := decode_full_reference before
  rw [actual_message_field_decoded source before middle ctx decoded run] at observed
  cases decoded with
  | Err error =>
    simp only [messageFieldDecoded,StringContentV3.bytesResult,StringContentV3.stringResult,InnerResponseV1.strongStringResult] at observed
    have success := stamped_field_success _ _ _ _ _ _ observed
    cases success.1
  | Ok native =>
    by_cases fits : native.val ≤ middle.length
    · by_cases accepted : Utf8.accepts ((copiedString middle native).val.map (fun byte => byte.bv)) = true
      · rw [message_field_utf_success source middle native fits accepted] at observed
        have same := Result.ok.inj observed
        have valueEq := congrArg (fun x => x.2.1) same
        have cursorEq := congrArg (fun x => x.2.2) same
        exact ⟨native,middle,run,fits,accepted,valueEq.symm,cursorEq.symm⟩
      · rw [message_field_utf_failure source middle native fits (Bool.eq_false_iff.mpr accepted)] at observed
        have success := stamped_field_success _ _ _ _ _ _ observed
        cases success.1
    · simp only [messageFieldDecoded,StringContentV3.bytesResult,if_neg fits,StringContentV3.stringResult,InnerResponseV1.strongStringResult] at observed
      have success := stamped_field_success _ _ _ _ _ _ observed
      cases success.1

#print axioms actual_message_success_native
end ChatResponseReference.StreamingV1
