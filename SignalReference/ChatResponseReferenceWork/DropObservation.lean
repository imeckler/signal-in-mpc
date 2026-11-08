import ChatResponseReferenceWork.DropReferenceCore
namespace ChatResponseReference.DropObservation
open Aeneas Aeneas.Std ActualChatResponseString

/-- The actual translated native destructor has precisely one total content
mutation. No input buffer or error parameter occurs in its type or computation. -/
theorem actual_drop_clears (value : alloc.vec.Vec U8) :
    encoding.string.merge.DropGuard.Insts.CoreOpsDropDrop.drop value =
      .ok (Aeneas.Std.alloc.vec.Vec.new U8, fun value => value) := rfl

/-- Owned decoding exposes its Result, not its partial record or local cursor.
A failure preserves its exact error under this outer observation. -/
def ownedObservation {Record Buffer Value Error : Type}
    (outcome : core.result.Result Value Error × Record × Buffer) : core.result.Result Value Error :=
  outcome.1

/-- Explicitly execute the actual cleanup and retain the same error and cursor.
This models only this U8 cleanup: no arbitrary destructor is erased. -/
def clearThenError {Error Buffer : Type} (error : Error) (buffer : Buffer)
    (value : alloc.vec.Vec U8) : Result (core.result.Result Unit Error × alloc.vec.Vec U8 × Buffer) := do
  let (cleared, _) ← encoding.string.merge.DropGuard.Insts.CoreOpsDropDrop.drop value
  .ok (.Err error, cleared, buffer)

theorem clear_error_exact {Error Buffer : Type} (error : Error) (buffer : Buffer)
    (value : alloc.vec.Vec U8) :
    clearThenError error buffer value = .ok (.Err error, Aeneas.Std.alloc.vec.Vec.new U8, buffer) := rfl

/-- Cleanup neither adds a panic/error nor consumes input. Its state mutation
is hidden only at the actual owned Result boundary; strong state equality is
not asserted. This holds for every error payload and every local suffix. -/
theorem owned_cleanup_unobservable {Error Buffer : Type} (error : Error) (buffer : Buffer)
    (value : alloc.vec.Vec U8) :
    (do let outcome ← clearThenError error buffer value; pure (ownedObservation outcome)) =
      (.ok (ownedObservation (core.result.Result.Err error, value, buffer)) :
        Result (core.result.Result Unit Error)) := rfl

#print axioms actual_drop_clears
#print axioms clear_error_exact
#print axioms owned_cleanup_unobservable
end ChatResponseReference.DropObservation
