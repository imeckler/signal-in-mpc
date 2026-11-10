import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
import ChatResponseReferenceWork.StreamingUnknownV1.FixedSource
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip

/-- Actual fixed group child source body on every physical fit outcome. Context
construction/decrement and primitive execution are derived; no skip result or
termination premise is supplied. -/
theorem actual_group_fixed_source_all (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before middle : Slice U8) (parent tag count : U32) (parents : List U32) (budget remaining : Nat) (wide : Bool)
    (ready : GroupLoopReady state before budget remaining parents count) (depthBound : parents.length ≤ 98)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before =
      .ok (groupChild (fixedResult middle (if wide then 8 else 4)).1 (fixedResult middle (if wide then 8 else 4)).2) := by
  have countPositive : 1 < count.val := by have := ready.context; omega
  let child := U32.ofNatCore (count.val-1) (by have h := count.hmax; scalar_tac)
  have decremented : count.val = child.val+1 := by change count.val = (count.val-1)+1; omega
  have childPositive : child ≠ 0#u32 := by
    intro zero
    have numeric := congrArg UScalar.val zero
    change child.val = 0 at numeric
    omega
  have childRun : LoopSupportSkip.encoding.skip_field sliceBuf (if wide then .SixtyFourBit else .ThirtyTwoBit) tag middle ⟨child⟩ =
      .ok (fixedResult middle (if wide then 8 else 4)) := by
    cases wide with
    | false => exact fixed32_reference middle tag child childPositive
    | true => exact fixed64_reference middle tag child childPositive
  exact group_child_after before middle _ parent tag ⟨count⟩ ⟨child⟩ _ _
    (by cases wide <;> intro same <;> cases same) keyRun (enter_recursion_value count child decremented) childRun

#print axioms actual_group_fixed_source_all
end ChatResponseReference.StreamingUnknownV1
