import ChatResponseReferenceWork.OuterEnvelopeV1.Replayed.Funs
import ChatResponseReferenceWork.InnerResponseV1.FieldSpec
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.OuterEnvelopeV1
open ActualOuterEnvelopeV1
abbrev Message := chat_websocket.WebSocketMessage
abbrev Error := prost.error.DecodeError
abbrev stamp := InnerResponseV1.stamp

def optionalField {T B : Type} (old : Option T) (defaults : Result T)
    (run : T → Result (core.result.Result Unit Error × T × B))
    (set : T → Message) (frame : Str × Str) : Result (core.result.Result Unit Error × Message × B) := do
  let initial ← match old with | some value => .ok value | none => defaults
  let (status,value,after) ← run initial
  let result ← stamp frame status
  .ok (result,set value,after)

noncomputable def fieldSpec {B : Type} (inst : bytes.buf.buf_impl.Buf B) (state : Message)
    (tag : U32) (wire : prost.encoding.wire_type.WireType) (before : B) (ctx : prost.encoding.DecodeContext) :
    Result (core.result.Result Unit Error × Message × B) :=
  match tag with
  | 1#uscalar => optionalField state.type (.ok core.default.DefaultI32.default)
      (fun old => prost.encoding.int32.merge inst wire old before ctx)
      (fun value => {state with type := some value}) diagnosticFrameWebSocketMessage0
  | 2#uscalar => optionalField state.request chat_websocket.WebSocketRequestMessage.Insts.CoreDefaultDefault.default
      (fun old => ActualSubmessageV1.prost.encoding.message.merge
        chat_websocket.WebSocketRequestMessage.Insts.ProstMessageMessage inst wire old before ctx)
      (fun value => {state with request := some value}) diagnosticFrameWebSocketMessage1
  | 3#uscalar => optionalField state.response chat_websocket.WebSocketResponseMessage.Insts.CoreDefaultDefault.default
      (fun old => ActualSubmessageV1.prost.encoding.message.merge
        chat_websocket.WebSocketResponseMessage.Insts.ProstMessageMessage inst wire old before ctx)
      (fun value => {state with response := some value}) diagnosticFrameWebSocketMessage2
  | _ => do
      let (result,after) ← prost.encoding.skip_field inst wire tag before ctx
      .ok (result,state,after)

attribute [local simp]
  core.option.Option.Insts.CoreDefaultDefault.default
  chat_websocket.WebSocketRequestMessage.Insts.CoreDefaultDefault.default
  chat_websocket.WebSocketResponseMessage.Insts.CoreDefaultDefault.default
  ActualInnerResponseV1.core.option.Option.get_or_insert_with
  ActualInnerResponseV1.core.result.Result.map_err
  P.Insts.CoreOpsFunctionFnOnceTupleI32.call_once
  P.Insts.CoreOpsFunctionFnOnceTupleWebSocketRequestMessage.call_once
  P.Insts.CoreOpsFunctionFnOnceTupleWebSocketResponseMessage.call_once
  chat_websocket.MessageWebSocketMessage.merge_field.closure.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once
  chat_websocket.MessageWebSocketMessage.merge_field.closure_1.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once
  chat_websocket.MessageWebSocketMessage.merge_field.closure_2.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once

theorem default_exact : default_envelope = .ok ({type := none,request := none,response := none} : Message) := rfl

/-- Actual generated envelope dispatcher, including absent/existing and duplicate
submessages, exact native submessage error/cursor/state and diagnostic effects.
Encode/clear trait slots are not invoked by these parsing computations. -/
theorem dispatcher_reference {B : Type} (inst : bytes.buf.buf_impl.Buf B) (state : Message)
    (tag : U32) (wire : prost.encoding.wire_type.WireType) (before : B) (ctx : prost.encoding.DecodeContext) :
    merge_envelope inst state tag wire before ctx = fieldSpec inst state tag wire before ctx := by
  unfold merge_envelope chat_websocket.WebSocketMessage.Insts.ProstMessageMessage.merge_field fieldSpec
  split
  · cases h : state.type <;> simp_all [optionalField,stamp,InnerResponseV1.stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · cases h : state.request <;> simp_all [optionalField,stamp,InnerResponseV1.stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · cases h : state.response <;> simp_all [optionalField,stamp,InnerResponseV1.stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · simp_all [optionalField,stamp,InnerResponseV1.stamp]
#print axioms default_exact
#print axioms dispatcher_reference
end ChatResponseReference.OuterEnvelopeV1
