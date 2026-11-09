import ChatResponseReferenceWork.StreamingV1.NativeBodyFieldScope
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

theorem actual_body_field_scoped (source : InnerResponseV1.Message)
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
      (feed state consumed).budget = BitVec.ofNat 64 (budget-consumed.length) ∧
      (feed state consumed).responseRemaining = BitVec.ofNat 64 (remaining-consumed.length) ∧
      (feed state consumed).inner = (if consumed.length = remaining then 0 else 255) ∧
      (feed state consumed).depth = state.depth ∧
      ∃ header,
        consumed = header ++ contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val) ∧
        bodyTrace (feed state header) (contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val)) =
          (contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val)).map (fun byte => (255,0,0,byte)) := by
  obtain ⟨sourceResult,consumed,span,data,completeValid,finalModes,finalSkip,header,headerEq,events⟩ :=
    actual_body_field_complete source ctx state before after native budget remaining budgetBound remainingBound budgetEnough physical payloadPhysical childFits
      modes positions value kinds valid seen finished inner depth budgetCounter childCounter sourceSuccess
  obtain ⟨scopeConsumed,scopeSpan,scopeBudget,scopeRemaining,scopeInner,scopeDepth⟩ :=
    native_body_field_scope state before after native budget remaining budgetBound remainingBound budgetEnough physical payloadPhysical childFits
      modes positions value kinds valid seen finished inner depth budgetCounter childCounter sourceSuccess
  have unique : scopeConsumed = consumed := consumed_prefix_unique _ _ _ _ scopeSpan span
  subst scopeConsumed
  exact ⟨sourceResult,consumed,span,data,completeValid,finalModes,finalSkip,scopeBudget,scopeRemaining,scopeInner,scopeDepth,header,headerEq,events⟩

#print axioms actual_body_field_scoped
end ChatResponseReference.StreamingV1
