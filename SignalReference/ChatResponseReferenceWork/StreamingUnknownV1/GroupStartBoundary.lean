import ChatResponseReferenceWork.StreamingUnknownV1.GroupBoundaryRejection
import ChatResponseReferenceWork.StreamingUnknownV1.GroupDepthStep
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- A nested start key at/past the real child cannot borrow parent tail for its
end tag. Core rejects its crossing prefix or its actual terminal leaving a
positive incremented group depth, including rejected-state stack mutation. -/
theorem group_start_key_not_inside_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before middle : Slice U8) (tag count : U32) (parents : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining parents count) (depthBound : parents.length ≤ 98)
    (notInside : middle.length ≤ before.length-remaining)
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,.StartGroup),middle)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨native,run,accepted⟩ := native_key_success_varint before middle tag .StartGroup actual
  by_cases past : middle.length < before.length-remaining
  · exact native_varint_child_overrun_reject state before middle native remaining 0 (by decide)
      ready.common.remainingBound ready.common.positive ready.common.physical past ready.modes ready.common.inner ready.common.childCounter run
  · obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before middle native run
    have tailLength : tail.length = middle.length := by
      have result := congrArg List.length suffix
      simpa only [contents,List.length_map] using result.symm
    have inputLength : before.length = leading.length+1+middle.length := by
      have result := congrArg List.length span
      simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
    have context := bounded_varint_prefix_context state leading remaining ready.common.remainingBound
      (by have := ready.common.physical; omega) ready.common.inner ready.common.childCounter continues
    have invariant := core_prefix_invariant state leading 0 0 (by decide) (by omega) ready.modes ready.common.positions continues
    have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
    have initialValue : state.value = 0 := ready.common.value
    have currentValue : (feed state leading).value = accumulated leading 0 0 := by simpa only [initialValue] using invariant.2.2
    have decoded : coreDecoded (feed state leading) byte = native.bv := by
      unfold coreDecoded
      rw [currentPositions,currentValue,contribution_one_hot leading.length (by omega) byte]
      exact nativeValue.symm
    have currentCounter : (feed state leading).responseRemaining = BitVec.ofNat 64 1 := by
      rw [context.2.2.2.2]
      congr 1
      have := ready.common.physical
      omega
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
    have nextDepth : next.depth = BitVec.ofNat 64 (parents.length+1) := by
      have result := native_key_depth_transition (feed state leading) byte native tag .StartGroup invariant.1 terminal decoded accepted
      have nextEq : next.depth = Word64.concrete.add state.depth 1 := by
        simpa only [wireNumber,if_true,context.2.2.1] using result
      rw [nextEq,ready.depth]
      change BitVec.ofNat 64 parents.length + BitVec.ofNat 64 1 = _
      exact (BitVec.ofNat_add _ _).symm
    have notTop := nested_depth_not_top next (parents.length+1) (by omega) (by omega) nextDepth
    have rejected := core_close_active_group_reject (feed state leading) byte context.2.2.2.1 currentCounter notTop
    rw [span]
    apply finish_invalid_sticky
    simp only [feed,List.foldl_append,List.foldl_cons]
    exact feed_invalid_sticky _ tail rejected

#print axioms group_start_key_not_inside_reject
end ChatResponseReference.StreamingUnknownV1
