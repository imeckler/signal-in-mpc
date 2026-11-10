import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipSlice

/-- A successful native group end stays inside the real private child and may
close that child only if no enclosing group remains. -/
def GroupCompatibleEnd (before after : Slice U8) (remaining : Nat) (older : List U32) : Prop :=
  before.length-remaining ≤ after.length ∧ (after.length = before.length-remaining → older = [])

instance (before after : Slice U8) (remaining : Nat) (older : List U32) :
    Decidable (GroupCompatibleEnd before after remaining older) :=
  inferInstanceAs (Decidable (before.length-remaining ≤ after.length ∧ (after.length = before.length-remaining → older = [])))

/-- Exact frame returned after a successful group: restore the witnessed source
ancestor context, or return to ordinary response parsing at the outermost end. -/
def GroupReturnedFrame (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (after : Slice U8)
    (budget remaining : Nat) (older : List U32) (count : U32) : Prop :=
  if older = [] then count = 99#u32 ∧ ChildAtKey state after budget remaining
  else ∃ parentCount : U32,
    LoopSupportSkip.encoding.DecodeContext.enter_recursion ⟨parentCount⟩ = .ok ⟨count⟩ ∧
    GroupLoopReady state after budget remaining older parentCount

/-- All-outcome state relation; native status/error/suffix are independently
retained by the actual source run. A source success inside its private domain
must yield full numeric continuation, never an arbitrary rejection alternative. -/
def GroupOutcome (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before : Slice U8)
    (budget remaining : Nat) (older : List U32) (count : U32)
    (result : core.result.Result Unit LoopSupportSkip.error.DecodeError × Slice U8) : Prop :=
  match result.1 with
  | .Err _ => (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
  | .Ok _ =>
    if GroupCompatibleEnd before result.2 remaining older then
      ∃ consumed,
        contents before = consumed++contents result.2 ∧ CacheAgrees outer source (feed state consumed) ∧
        GroupReturnedFrame (feed state consumed) result.2 (budget-consumed.length) (remaining-consumed.length) older count
    else (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0

end ChatResponseReference.StreamingUnknownV1
