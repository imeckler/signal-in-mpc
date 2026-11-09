import ChatResponseReferenceWork.OuterEnvelopeV1.GenericField
import ChatResponseReferenceWork.InnerScanV1.FieldConsumption
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.OuterEnvelopeV1
open ActualOuterEnvelopeV1
abbrev Request := chat_websocket.WebSocketRequestMessage
noncomputable def requestFieldSpec {B : Type} (inst : bytes.buf.buf_impl.Buf B) (state : Request)
    (tag : U32) (wire : prost.encoding.wire_type.WireType) (before : B) (ctx : prost.encoding.DecodeContext) :
    Result (core.result.Result Unit Error × Request × B) :=
  match tag with
  | 1#uscalar => optional state.verb alloc.string.String.Insts.CoreDefaultDefault.default
      (fun old => prost.encoding.string.merge inst wire old before ctx)
      (fun value => {state with verb := some value}) diagnosticFrameWebSocketRequestMessage0
  | 2#uscalar => optional state.path alloc.string.String.Insts.CoreDefaultDefault.default
      (fun old => prost.encoding.string.merge inst wire old before ctx)
      (fun value => {state with path := some value}) diagnosticFrameWebSocketRequestMessage1
  | 3#uscalar => optional state.body bytes.bytes.Bytes.Insts.CoreDefaultDefault.default
      (fun old => prost.encoding.bytes.merge bytes.bytes.Bytes.Insts.ProstEncodingBytesAdapter inst wire old before ctx)
      (fun value => {state with body := some value}) diagnosticFrameWebSocketRequestMessage2
  | 4#uscalar => optional state.id (.ok core.default.DefaultU64.default)
      (fun old => prost.encoding.uint64.merge inst wire old before ctx)
      (fun value => {state with id := some value}) diagnosticFrameWebSocketRequestMessage3
  | 5#uscalar => optional (some state.headers) (.ok state.headers)
      (fun old => prost.encoding.string.merge_repeated inst wire old before ctx)
      (fun value => {state with headers := value}) diagnosticFrameWebSocketRequestMessage4
  | _ => do
      let (result,after) ← prost.encoding.skip_field inst wire tag before ctx
      .ok (result,state,after)

attribute [local simp]
  ActualInnerResponseV1.core.option.Option.get_or_insert_with
  ActualInnerResponseV1.core.result.Result.map_err
  ActualInnerResponseV1.P.Insts.CoreOpsFunctionFnOnceTupleString.call_once
  ActualInnerResponseV1.P.Insts.CoreOpsFunctionFnOnceTupleBytes.call_once
  ActualInnerResponseV1.alloc.string.String.Insts.CoreDefaultDefault.default
  ActualInnerResponseV1.bytes.bytes.Bytes.Insts.CoreDefaultDefault.default
  ActualResponseBytesV1.bytes.bytes.Bytes.Insts.CoreDefaultDefault.default
  chat_websocket.MessageWebSocketRequestMessage.merge_field.closure.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once
  chat_websocket.MessageWebSocketRequestMessage.merge_field.closure_1.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once
  chat_websocket.MessageWebSocketRequestMessage.merge_field.closure_2.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once
  chat_websocket.MessageWebSocketRequestMessage.merge_field.closure_3.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once
  chat_websocket.MessageWebSocketRequestMessage.merge_field.closure_4.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once

theorem request_dispatcher {B : Type} (inst : bytes.buf.buf_impl.Buf B) (state : Request)
    (tag : U32) (wire : prost.encoding.wire_type.WireType) (before : B) (ctx : prost.encoding.DecodeContext) :
    chat_websocket.WebSocketRequestMessage.Insts.ProstMessageMessage.merge_field inst state tag wire before ctx =
      requestFieldSpec inst state tag wire before ctx := by
  unfold chat_websocket.WebSocketRequestMessage.Insts.ProstMessageMessage.merge_field requestFieldSpec
  split
  · cases h : state.verb <;> simp_all [optional,stamp,InnerResponseV1.stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · cases h : state.path <;> simp_all [optional,stamp,InnerResponseV1.stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · cases h : state.body <;> simp_all [optional,stamp,InnerResponseV1.stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · cases h : state.id <;> simp_all [optional,stamp,InnerResponseV1.stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · simp_all [optional,stamp,InnerResponseV1.stamp] <;> first | rfl | (intros result value after run; cases result <;> rfl)
  · simp_all [optional,stamp,InnerResponseV1.stamp]

/-- Actual request callback consumption is needed even though response validation
rejects envelopes containing request payloads. No request validity is assumed. -/
theorem request_consumption (state next : Request) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext) (status : core.result.Result Unit Error)
    (observed : chat_websocket.WebSocketRequestMessage.Insts.ProstMessageMessage.merge_field
      InnerResponseV1.sliceBuf state tag wire before ctx = .ok (status,next,after)) :
    after.length ≤ before.length := by
  rw [request_dispatcher] at observed
  unfold requestFieldSpec at observed
  split at observed
  · apply optional_consumption (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact InnerScanV1.bound_of_reference (InnerScanV1.string_all_wire_consumption initial wire before ctx) run
  · apply optional_consumption (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact InnerScanV1.bound_of_reference (InnerScanV1.string_all_wire_consumption initial wire before ctx) run
  · apply optional_consumption (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact InnerScanV1.bound_of_reference (InnerScanV1.bytes_consumption initial wire before ctx) run
  · apply optional_consumption (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact InnerScanV1.bound_of_reference (InnerScanV1.scalar_consumption initial 0#u32 wire before ctx).2 run
  · apply optional_consumption (primitive := ?_) (observed := observed)
    intro initial result value suffix run
    exact InnerScanV1.header_all_wire_consumption initial value wire before suffix ctx result run
  · obtain ⟨result,semantics,run,bound⟩ := InnerResponseV1.skip_full_reference wire tag before ctx
    unfold prost.encoding.skip_field at observed
    rw [run] at observed
    rcases result with ⟨result,suffix⟩
    cases result <;> cases observed <;> exact bound
#print axioms request_dispatcher
#print axioms request_consumption
end ChatResponseReference.OuterEnvelopeV1
