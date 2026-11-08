import ChatResponseReferenceWork.GeneratedValidation.Funs
namespace ChatResponseReference.Validation
open Aeneas Aeneas.Std ActualChatResponseValidation

/-- Executable envelope validation with all source rejection alternatives.
Parsing, HTTP validation and pending-request correlation are separate stages. -/
def validate (message : chat_websocket.WebSocketMessage) :
    core.result.Result validation_replay.ChatMessageProto validation_replay.ChatProtoDataError :=
  let type := message.type.getD 0#i32
  if type = 0#i32 then .Err .UnknownMessageType
  else if type = 1#i32 then
    match message.request, message.response with
    | some request, none => .Ok (.Request request)
    | none, none => .Err .MissingPayload
    | _, some _ => .Err .RequestHasResponse
  else if type = 2#i32 then
    match message.request, message.response with
    | none, some response => .Ok (.Response response)
    | none, none => .Err .MissingPayload
    | some _, _ => .Err .ResponseHasRequest
  else .Err (.InvalidMessageType type)

theorem actual_validation_reference (message : chat_websocket.WebSocketMessage) :
    validation_replay.validate_decoded message = .ok (validate message) := by
  rcases message with ⟨type, request, response⟩
  cases type with
  | none => rfl
  | some type =>
    simp only [validation_replay.validate_decoded, validate,
      core.option.Option.unwrap_or_default, Option.getD]
    by_cases h0 : type = 0#i32
    · subst type; rfl
    by_cases h1 : type = 1#i32
    · subst type; cases request <;> cases response <;> rfl
    by_cases h2 : type = 2#i32
    · subst type; cases request <;> cases response <;> rfl
    · simp [chat_websocket.web_socket_message.Type.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from,
        h0,h1,h2,core.result.Result.map_err,
        validation_replay.validate_decoded.closure.Insts.CoreOpsFunctionFnOnceTupleUnknownEnumValueChatProtoDataError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      split <;> simp_all
      all_goals
        exfalso
        first | exact h0 (by decide) | exact h1 (by decide) | exact h2 (by decide)

#print axioms actual_validation_reference
end ChatResponseReference.Validation
