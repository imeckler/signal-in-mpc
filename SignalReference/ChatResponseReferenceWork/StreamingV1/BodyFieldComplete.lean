import ChatResponseReferenceWork.StreamingV1.NativeBodyFieldEvents
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual generated body merger success agrees with the complete numeric
copied-data/cache/validity transition and exact payload events on one source span.
All-outcome error/mutation/suffix results remain in BodyFieldRefinement. -/
theorem actual_body_field_complete (source : InnerResponseV1.Message)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (payloadPhysical : native.val ≤ after.length)
    (childFits : native.val + (before.length-after.length) ≤ remaining)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0)
    (value : state.value = 0) (kinds : state.kinds = [0,255,0,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (4#u32) .LengthDelimited before ctx =
      .ok (.Ok (),{source with body := some ⟨ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val⟩},
        LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
      responseData (feed state consumed) = {responseData state with bodyPresent := 255,bodyLength := native.bv} ∧
      (feed state consumed).valid = 255 ∧ (feed state consumed).modes = lane 0 ∧ (feed state consumed).skip = 0 ∧
      ∃ header,
        consumed = header ++ contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val) ∧
        bodyTrace (feed state header) (contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val)) =
          (contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val)).map (fun byte => (255,0,0,byte)) := by
  obtain ⟨sourceResult,consumed,span,data,finalModes,finalSkip⟩ :=
    actual_body_field_data_success source state before after native ctx payloadPhysical modes positions value kinds sourceSuccess
  obtain ⟨header,headerSpan,events,completeValid⟩ := native_body_field_events state before after native budget remaining
    budgetBound remainingBound budgetEnough physical payloadPhysical childFits modes positions value kinds valid seen finished
    inner depth budgetCounter childCounter sourceSuccess
  let copied := ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val
  have joinedSpan : contents before = (header ++ contents copied) ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) := by
    rw [headerSpan,copied_body_partition after native payloadPhysical]
    simp only [List.append_assoc,copied]
  have unique : consumed = header ++ contents copied := consumed_prefix_unique _ _ _ _ span joinedSpan
  refine ⟨sourceResult,consumed,span,data,?_,finalModes,finalSkip,header,unique,events⟩
  rw [unique]
  exact completeValid

#print axioms actual_body_field_complete
end ChatResponseReference.StreamingV1
