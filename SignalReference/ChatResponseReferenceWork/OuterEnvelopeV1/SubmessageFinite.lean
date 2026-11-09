import ChatResponseReferenceWork.OuterEnvelopeV1.RequestReference
import ChatResponseReferenceWork.OuterEnvelopeV1.ResponseBridge
import ChatResponseReferenceWork.SubmessageV1.GenericScan
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.OuterEnvelopeV1
open ActualOuterEnvelopeV1

theorem request_fields_bound : SubmessageGenericV1.FieldBound
    chat_websocket.WebSocketRequestMessage.Insts.ProstMessageMessage := by
  intro state next tag wire before after ctx status observed
  exact request_consumption state next tag wire before after ctx status observed

theorem response_fields_bound : SubmessageGenericV1.FieldBound
    chat_websocket.WebSocketResponseMessage.Insts.ProstMessageMessage := by
  intro state next tag wire before after ctx status observed
  change chat_websocket.WebSocketResponseMessage.Insts.ProstMessageMessage.merge_field
    InnerResponseV1.sliceBuf state tag wire before ctx = .ok (status,next,after) at observed
  rw [response_fields_exact,InnerResponseV1.dispatcher_reference] at observed
  exact InnerScanV1.field_consumption state next tag wire before after ctx status observed

/-- Both actual generated submessage dictionaries satisfy the full field bound;
these exports supply no primitive correctness/termination/validity hypothesis. -/
theorem request_submessage_finite (ctx : prost.encoding.DecodeContext) (limit : Usize)
    (state : Request) (before : Slice U8) :
    ∃ result,
      InnerScanV1.FiniteRun
        (SubmessageGenericV1.body chat_websocket.WebSocketRequestMessage.Insts.ProstMessageMessage ctx limit)
        (state,before,()) result ∧
      ActualSubmessageV1.prost.encoding.merge_loop_loop
        (SubmessageGenericV1.callback chat_websocket.WebSocketRequestMessage.Insts.ProstMessageMessage)
        InnerResponseV1.sliceBuf state before ctx () limit = result :=
  SubmessageGenericV1.actual_scan_finite _ request_fields_bound ctx limit state before

theorem response_submessage_finite (ctx : prost.encoding.DecodeContext) (limit : Usize)
    (state : chat_websocket.WebSocketResponseMessage) (before : Slice U8) :
    ∃ result,
      InnerScanV1.FiniteRun
        (SubmessageGenericV1.body chat_websocket.WebSocketResponseMessage.Insts.ProstMessageMessage ctx limit)
        (state,before,()) result ∧
      ActualSubmessageV1.prost.encoding.merge_loop_loop
        (SubmessageGenericV1.callback chat_websocket.WebSocketResponseMessage.Insts.ProstMessageMessage)
        InnerResponseV1.sliceBuf state before ctx () limit = result :=
  SubmessageGenericV1.actual_scan_finite _ response_fields_bound ctx limit state before
#print axioms request_fields_bound
#print axioms response_fields_bound
#print axioms request_submessage_finite
#print axioms response_submessage_finite
end ChatResponseReference.OuterEnvelopeV1
