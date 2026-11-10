import ChatResponseReferenceWork.StreamingUnknownV1.GroupBoundaryRejection
import ChatResponseReferenceWork.StreamingUnknownV1.GroupDepthStep
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Native matching close may finish its source group at/past the child while
other groups remain active. Source success/suffix is retained; Core rejects an
overrun or an exact child end that still leaves an enclosing group unclosed. -/
theorem actual_group_pop_boundary_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (parent count : U32) (older : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining (older++[parent]) count)
    (atOrPast : after.length ≤ before.length-remaining)
    (unfinished : after.length < before.length-remaining ∨ older ≠ [])
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (parent,.EndGroup),after)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.done (.Ok (),after)) ∧
    LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok (.Ok (),after) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have step : LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.done (.Ok (),after)) := by
    have result := group_end_after before after parent parent ⟨count⟩ actual
    simpa only [groupClose,if_pos rfl,if_true] using result
  refine ⟨step,group_loop_done _ _ _ _ step,?_⟩
  obtain ⟨native,run,accepted⟩ := native_key_success_varint before after parent .EndGroup actual
  by_cases past : after.length < before.length-remaining
  · exact native_varint_child_overrun_reject state before after native remaining 0 (by decide)
      ready.common.remainingBound ready.common.positive ready.common.physical past ready.modes ready.common.inner ready.common.childCounter run
  · have olderNonempty : older ≠ [] := unfinished.resolve_left past
    have depthPositive : 1 < (older++[parent]).length := by
      have h := List.length_pos_iff.mpr olderNonempty
      simp only [List.length_append,List.length_cons,List.length_nil]
      omega
    obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native run
    have tailLength : tail.length = after.length := by
      have result := congrArg List.length suffix
      simpa only [contents,List.length_map] using result.symm
    have inputLength : before.length = leading.length+1+after.length := by
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
    have nextDepth : next.depth = BitVec.ofNat 64 ((older++[parent]).length-1) := by
      have result := native_key_depth_transition (feed state leading) byte native parent .EndGroup invariant.1 terminal decoded accepted
      have nextEq : next.depth = Word64.concrete.sub state.depth 1 := by
        simpa only [wireNumber,if_neg (by decide : ¬(4:Nat) = 3),if_true,context.2.2.1] using result
      rw [nextEq,ready.depth]
      change BitVec.ofNat 64 (older++[parent]).length-BitVec.ofNat 64 1 = _
      exact BitVec.ofNat_sub_ofNat_of_le _ 1 (by decide) (by omega)
    have notTop := nested_depth_not_top next ((older++[parent]).length-1) (by omega) (by have := ready.bounded; omega) nextDepth
    have rejected := core_close_active_group_reject (feed state leading) byte context.2.2.2.1 currentCounter notTop
    rw [span]
    apply finish_invalid_sticky
    simp only [feed,List.foldl_append,List.foldl_cons]
    exact feed_invalid_sticky _ tail rejected

#print axioms actual_group_pop_boundary_reject
end ChatResponseReference.StreamingUnknownV1
