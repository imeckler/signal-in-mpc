import ChatResponseReferenceWork.GeneratedOwnedTransferred.Types
open Aeneas Aeneas.Std Result
/-- Exact Result.map control flow: the captured message is used only on Ok.
The unused default-merge template is intentionally not provided: merge remains
an explicit dictionary operation, not an assumed parser implementation. -/
def core.result.Result.map {T E U F : Type} (f : core.ops.function.FnOnce F T U)
    (r : core.result.Result T E) (closure : F) : Result (core.result.Result U E) := do
  match r with
  | .Ok value => let value1 ← f.call_once closure value; .ok (.Ok value1)
  | .Err error => .ok (.Err error)
