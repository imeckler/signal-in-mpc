import ChatResponseReferenceWork.StreamingUnknownV1.GroupLoopReady
import ChatResponseReferenceWork.StreamingUnknownV1.GroupBudget
import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyRejection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- At actual depth99/source context1, every non-end child fails before its
value is read. Exact actual error/post-key suffix and full Core rejection are
joined, including native keys crossing the private child boundary. -/
theorem actual_group_limit_error (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (parent tag count : U32) (wire : WireType)
    (parents : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining parents count) (depthLimit : parents.length = 99)
    (notEnd : wire ≠ .EndGroup)
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before =
      .ok (.done (.Err (decodeError .RecursionLimitReached),after)) ∧
    LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ =
      .ok (.Err (decodeError .RecursionLimitReached),after) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have decremented : count.val = (0#u32).val+1 := by have := ready.context; rw [depthLimit] at this; change count.val = 0+1; omega
  have childRun := recursion_limit_first sliceBuf wire tag after
  have step : LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before =
      .ok (.done (.Err (decodeError .RecursionLimitReached),after)) :=
    group_child_after before after after parent tag ⟨count⟩ ⟨0#u32⟩ wire (.Err (decodeError .RecursionLimitReached)) notEnd actual
      (enter_recursion_value count (0#u32) decremented) childRun
  refine ⟨step,group_loop_done _ _ _ _ step,?_⟩
  obtain ⟨native,run,accepted⟩ := native_key_success_varint before after tag wire actual
  by_cases overrun : after.length < before.length-remaining
  · exact native_varint_child_overrun_reject state before after native remaining 0 (by decide)
      ready.common.remainingBound ready.common.positive ready.common.physical overrun ready.modes ready.common.inner ready.common.childCounter run
  · obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native run
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
    have currentDepth : (feed state leading).depth = BitVec.ofNat 64 99 := by rw [context.2.2.1,ready.depth,depthLimit]
    have bad := inner_group_limit_key_guard (feed state leading) byte native tag wire currentDepth context.2.2.2.1 notEnd decoded accepted
    have rejected := actual_key_guard_reject (feed state leading) byte invariant.1 terminal bad
    rw [span]
    apply finish_invalid_sticky
    simp only [feed,List.foldl_append,List.foldl_cons]
    exact feed_invalid_sticky _ tail rejected

#print axioms actual_group_limit_error
end ChatResponseReference.StreamingUnknownV1
