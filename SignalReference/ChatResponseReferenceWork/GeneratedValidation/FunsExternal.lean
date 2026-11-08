import ChatResponseReferenceWork.GeneratedValidation.Types
namespace ActualChatResponseValidation
open Aeneas Aeneas.Std

def core.option.Option.unwrap_or_default {T : Type}
    (default : core.default.Default T) (value : Option T) : Result T :=
  match value with | some value => .ok value | none => default.default

def core.result.Result.map_err {T E F O : Type}
    (f : core.ops.function.FnOnce O E F) (value : core.result.Result T E) (closure : O) :
    Result (core.result.Result T F) := do
  match value with
  | .Ok result => .ok (.Ok result)
  | .Err error => let converted ← f.call_once closure error; .ok (.Err converted)
end ActualChatResponseValidation
