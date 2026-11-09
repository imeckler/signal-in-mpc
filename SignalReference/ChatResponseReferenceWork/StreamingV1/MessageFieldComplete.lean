import ChatResponseReferenceWork.StreamingV1.NativeMessageData
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Complete message String field observation on one actual consumed prefix:
source result/content/error effects, numeric validity, cache and control. -/
theorem actual_message_field_complete (source : InnerResponseV1.Message)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (payloadPhysical : native.val ≤ after.length)
    (childFits : native.val + (before.length-after.length) ≤ remaining)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0)
    (utfShape : state.utf.length = 8) (value : state.value = 0) (kinds : state.kinds = [0,0,255,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    merge_response InnerResponseV1.sliceBuf source (3#u32) .LengthDelimited before ctx = messageFieldOutcome source after native ∧
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
      responseData (feed state consumed) = {responseData state with messagePresent := 255} ∧
      (feed state consumed).valid = (if Utf8.accepts ((copiedString after native).val.map (fun byte => byte.bv)) then 255 else 0) ∧
      (feed state consumed).modes = lane 0 ∧ (feed state consumed).skip = 0 := by
  obtain ⟨sourceResult,consumed,span,completeValid⟩ := actual_message_field_agreement source ctx state before after native budget remaining
    budgetBound remainingBound budgetEnough physical payloadPhysical childFits modes positions utfShape value kinds valid seen finished inner depth budgetCounter childCounter sourceSuccess
  obtain ⟨dataConsumed,dataSpan,data,finalModes,finalSkip⟩ := native_message_data_complete state before after native payloadPhysical modes positions value kinds sourceSuccess
  have unique : dataConsumed = consumed := consumed_prefix_unique _ _ _ _ dataSpan span
  subst dataConsumed
  exact ⟨sourceResult,consumed,span,data,completeValid,finalModes,finalSkip⟩

#print axioms actual_message_field_complete
end ChatResponseReference.StreamingV1
