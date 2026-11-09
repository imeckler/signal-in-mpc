import ChatResponseReferenceWork.OuterEnvelopeV1.Replayed.Funs
import ChatResponseReferenceWork.InnerResponseV1.Replayed.Funs
import ChatResponseReferenceWork.SubmessageV1.InnerScan
import ChatResponseReferenceWork.SubmessageV1.FieldOnly
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.OuterEnvelopeV1
open ActualOuterEnvelopeV1
/-- The response callback reachable from the real envelope is the same actual
response field computation already proved in InnerResponseV1, on all outcomes. -/
theorem response_fields_exact {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (state : chat_websocket.WebSocketResponseMessage) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before : B) (ctx : prost.encoding.DecodeContext) :
    chat_websocket.WebSocketResponseMessage.Insts.ProstMessageMessage.merge_field inst state tag wire before ctx =
      ActualInnerResponseV1.merge_response inst state tag wire before ctx := by
  rfl

theorem response_submessage_exact {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (state : chat_websocket.WebSocketResponseMessage) (wire : prost.encoding.wire_type.WireType)
    (before : B) (ctx : prost.encoding.DecodeContext) :
    ActualSubmessageV1.prost.encoding.message.merge
      chat_websocket.WebSocketResponseMessage.Insts.ProstMessageMessage inst wire state before ctx =
      ActualSubmessageV1.prost.encoding.message.merge SubmessageV1.schema inst wire state before ctx := by
  apply SubmessageV1.merge_field_only
  funext B inst state tag wire before ctx
  exact response_fields_exact inst state tag wire before ctx
#print axioms response_fields_exact
#print axioms response_submessage_exact
end ChatResponseReference.OuterEnvelopeV1
