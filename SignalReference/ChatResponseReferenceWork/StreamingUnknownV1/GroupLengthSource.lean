import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
import ChatResponseReferenceWork.StreamingUnknownV1.FixedSource
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip

def groupLengthNativeResult (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :
    core.result.Result Unit LoopSupportSkip.error.DecodeError × Slice U8 :=
  match decoded with
  | .Ok native => fixedResult after native.val
  | .Err error => (.Err error,after)

/-- Actual source group length child on every native header/physical outcome.
Child context construction/decrement and real skip execution are derived. -/
theorem actual_group_length_source_from_decode (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before middle after : Slice U8) (parent tag count : U32) (parents : List U32) (budget remaining : Nat)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (ready : GroupLoopReady state before budget remaining parents count) (depthBound : parents.length ≤ 98)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (decoded,after)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before =
      .ok (groupChild (groupLengthNativeResult decoded after).1 (groupLengthNativeResult decoded after).2) := by
  have countPositive : 1 < count.val := by have := ready.context; omega
  let child := U32.ofNatCore (count.val-1) (by have h := count.hmax; scalar_tac)
  have decremented : count.val = child.val+1 := by change count.val = (count.val-1)+1; omega
  have childPositive : child ≠ 0#u32 := by
    intro zero
    have numeric := congrArg UScalar.val zero
    change child.val = 0 at numeric
    omega
  have childRun : LoopSupportSkip.encoding.skip_field sliceBuf .LengthDelimited tag middle ⟨child⟩ = .ok (groupLengthNativeResult decoded after) := by
    cases decoded with
    | Ok native => exact length_delimited_after middle after native tag child childPositive valueRun
    | Err error => exact length_delimited_error middle after error tag child childPositive valueRun
  exact group_child_after before middle _ parent tag ⟨count⟩ ⟨child⟩ .LengthDelimited _
    (by intro same; cases same) keyRun (enter_recursion_value count child decremented) childRun

#print axioms actual_group_length_source_from_decode
end ChatResponseReference.StreamingUnknownV1
