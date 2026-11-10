import ChatResponseReferenceWork.StreamingUnknownV1.GroupFixedIteration
import ChatResponseReferenceWork.StreamingUnknownV1.GroupFixedError
import ChatResponseReferenceWork.StreamingUnknownV1.GroupFixedNotStrict
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Exhaustive actual fixed32/fixed64 child attempt in an inner group. Primitive
result/termination and physical/private fit are derived; exact source underflow
or real continuation/suffix are retained alongside numeric rejection/continuation. -/
theorem actual_group_fixed_attempt_all (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (parent tag count : U32) (parents : List U32) (budget remaining : Nat) (wide : Bool)
    (ready : GroupLoopReady state before budget remaining parents count)
    (cache : CacheAgrees outer source state) (depthBound : parents.length ≤ 98)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before =
      .ok (groupChild (fixedResult middle (if wide then 8 else 4)).1 (fixedResult middle (if wide then 8 else 4)).2) ∧
    if (if wide then 8 else 4) ≤ middle.length then
      if (if wide then 8 else 4) + (before.length-middle.length) < remaining then
        ∃ consumed,
          contents before = consumed ++ contents (drop middle (if wide then 8 else 4)) ∧ CacheAgrees outer source (feed state consumed) ∧
          GroupLoopReady (feed state consumed) (drop middle (if wide then 8 else 4)) (budget-consumed.length) (remaining-consumed.length) parents count
      else (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
    else
      LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok (.Err (decodeError .BufferUnderflow),middle) ∧
      (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  refine ⟨actual_group_fixed_source_all state before middle parent tag count parents budget remaining wide ready depthBound keyRun,?_⟩
  by_cases physical : (if wide then 8 else 4) ≤ middle.length
  · rw [if_pos physical]
    by_cases fits : (if wide then 8 else 4) + (before.length-middle.length) < remaining
    · rw [if_pos fits]
      exact (actual_group_fixed_loop_step outer source state before middle parent tag count parents budget remaining wide ready cache depthBound fits keyRun).2
    · rw [if_neg fits]
      exact (actual_group_fixed_not_strict state before middle parent tag count parents budget remaining wide ready depthBound physical fits keyRun).2
  · rw [if_neg physical]
    exact (actual_group_fixed_underflow state before middle parent tag count parents budget remaining wide ready depthBound (by omega) keyRun).2

#print axioms actual_group_fixed_attempt_all
end ChatResponseReference.StreamingUnknownV1
