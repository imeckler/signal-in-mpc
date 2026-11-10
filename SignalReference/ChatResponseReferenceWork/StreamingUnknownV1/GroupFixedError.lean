import ChatResponseReferenceWork.StreamingUnknownV1.GroupFixedSource
import ChatResponseReferenceWork.StreamingUnknownV1.GroupFixedNoFit
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual native fixed underflow preserves its unadvanced post-key suffix and
exact error, exits the real source group loop, and derives Core rejection. -/
theorem actual_group_fixed_underflow (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before middle : Slice U8) (parent tag count : U32) (parents : List U32) (budget remaining : Nat) (wide : Bool)
    (ready : GroupLoopReady state before budget remaining parents count) (depthBound : parents.length ≤ 98)
    (underflow : middle.length < (if wide then 8 else 4))
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before =
      .ok (.done (.Err (decodeError .BufferUnderflow),middle)) ∧
    LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok (.Err (decodeError .BufferUnderflow),middle) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have step := actual_group_fixed_source_all state before middle parent tag count parents budget remaining wide ready depthBound keyRun
  simp only [fixedResult,if_pos underflow,groupChild] at step
  obtain ⟨native,run,_⟩ := native_key_success_varint before middle tag _ keyRun
  obtain ⟨leading,byte,tail,span,suffix,_,_,_,_,_⟩ := native_success_span before middle native run
  have tailLength : tail.length = middle.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result.symm
  have inputLength : before.length = leading.length+1+middle.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  exact ⟨step,group_loop_done _ _ _ _ step,group_fixed_key_not_fit_reject state before middle tag budget remaining wide parents count ready
    (by have := ready.common.physical; omega) keyRun⟩

#print axioms actual_group_fixed_underflow
end ChatResponseReference.StreamingUnknownV1
