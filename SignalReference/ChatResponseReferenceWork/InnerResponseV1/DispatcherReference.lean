import ChatResponseReferenceWork.InnerResponseV1.FieldSpec
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerResponseV1
open ActualInnerResponseV1
set_option maxHeartbeats 1000000

attribute [local simp]
  core.option.Option.get_or_insert_with
  core.result.Result.map_err
  P.Insts.CoreOpsFunctionFnOnceTupleString.call_once
  P.Insts.CoreOpsFunctionFnOnceTupleBytes.call_once
  alloc.string.String.Insts.CoreDefaultDefault.default
  bytes.bytes.Bytes.Insts.CoreDefaultDefault.default
  ActualResponseBytesV1.bytes.bytes.Bytes.Insts.CoreDefaultDefault.default
  chat_websocket.MessageWebSocketResponseMessage.merge_field.closure.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once
  chat_websocket.MessageWebSocketResponseMessage.merge_field.closure_1.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once
  chat_websocket.MessageWebSocketResponseMessage.merge_field.closure_2.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once
  chat_websocket.MessageWebSocketResponseMessage.merge_field.closure_3.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once
  chat_websocket.MessageWebSocketResponseMessage.merge_field.closure_4.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once

theorem default_exact : default_response =
    .ok ({id := none,status := none,message := none,headers := alloc.vec.Vec.new ActualInnerResponseV1.String,body := none} : Message) := rfl

/-- Actual generated dispatcher composed with the wired actual primitives and
explicit diagnostic content model. Includes absent/existing fields, all ordinary
errors, allocation/failure/divergence effects and exact returned suffix/state. -/
theorem dispatcher_reference {B : Type} (inst : bytes.buf.buf_impl.Buf B) (state : Message)
    (tag : U32) (wire : prost.encoding.wire_type.WireType) (before : B) (ctx : prost.encoding.DecodeContext) :
    merge_response inst state tag wire before ctx = fieldSpec inst state tag wire before ctx := by
  unfold merge_response chat_websocket.WebSocketResponseMessage.Insts.ProstMessageMessage.merge_field fieldSpec
  split
  · cases h : state.id <;> simp_all [optionalField,stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · cases h : state.status <;> simp_all [optionalField,stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · cases h : state.message <;> simp_all [optionalField,stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · cases h : state.body <;> simp_all [optionalField,stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · simp_all [optionalField,stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · simp_all [optionalField,stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
#print axioms default_exact
#print axioms dispatcher_reference
end ChatResponseReference.InnerResponseV1
