import ChatResponseReferenceWork.OuterEnvelopeV1.SubmessageFinite
import ChatResponseReferenceWork.OuterEnvelopeV1.ScalarReference
import ChatResponseReferenceWork.SubmessageV1.MessageBounds
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.OuterEnvelopeV1
open ActualOuterEnvelopeV1

theorem envelope_field_consumption (state next : Message) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (status : core.result.Result Unit Error)
    (observed : merge_envelope InnerResponseV1.sliceBuf state tag wire before ctx = .ok (status,next,after)) :
    after.length ≤ before.length := by
  rw [dispatcher_reference] at observed
  unfold fieldSpec at observed
  split at observed
  · apply optional_consumption (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact InnerScanV1.bound_of_reference (int32_consumption initial wire before ctx) run
  · apply optional_consumption (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact SubmessageGenericV1.message_merge_bound _ request_fields_bound wire ctx initial value before suffix result run
  · apply optional_consumption (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact SubmessageGenericV1.message_merge_bound _ response_fields_bound wire ctx initial value before suffix result run
  · obtain ⟨result,semantics,run,bound⟩ := InnerResponseV1.skip_full_reference wire tag before ctx
    unfold prost.encoding.skip_field at observed
    rw [run] at observed
    rcases result with ⟨result,suffix⟩
    cases result <;> cases observed <;> exact bound
#print axioms envelope_field_consumption
end ChatResponseReference.OuterEnvelopeV1
