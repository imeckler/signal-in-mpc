import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyRejection
import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyStack
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Every actually decoded mismatched end tag rejects Core, including a source
key extending beyond the private child. Prefix/table alignment and the real
active-parent lookup are derived; no validity or guard oracle is supplied. -/
theorem native_group_end_mismatch_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag parent : U32) (depth remaining : Nat)
    (remainingBound : remaining ≤ 4096) (positive : 0 < remaining) (physical : remaining ≤ before.length)
    (positiveDepth : 0 < depth) (depthBound : depth ≤ 99) (stackShape : state.stack.length = 100)
    (depthEq : state.depth = BitVec.ofNat 64 depth)
    (parentSlot : state.stack[depth-1]'(by omega) = BitVec.ofNat 64 parent.val)
    (mismatch : tag ≠ parent) (modes : state.modes = lane 0) (positions : state.positions = oneHot 0)
    (value : state.value = 0) (inner : state.inner = 255)
    (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,.EndGroup),after)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨native,run,accepted⟩ := native_key_success_varint before after tag .EndGroup actual
  by_cases overrun : after.length < before.length-remaining
  · exact native_varint_child_overrun_reject state before after native remaining 0 (by decide)
      remainingBound positive physical overrun modes inner counter run
  · obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native run
    have tailLength : tail.length = after.length := by
      have result := congrArg List.length suffix
      simpa only [contents,List.length_map] using result.symm
    have inputLength : before.length = leading.length+1+after.length := by
      have result := congrArg List.length span
      simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
    have context := bounded_varint_prefix_context state leading remaining remainingBound (by omega) inner counter continues
    have invariant := core_prefix_invariant state leading 0 0 (by decide) (by omega) modes positions continues
    have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
    have currentValue : (feed state leading).value = accumulated leading 0 0 := by simpa only [value] using invariant.2.2
    have decoded : coreDecoded (feed state leading) byte = native.bv := by
      unfold coreDecoded
      rw [currentPositions,currentValue,contribution_one_hot leading.length (by omega) byte]
      exact nativeValue.symm
    have currentStack : (feed state leading).stack = state.stack := continuing_prefix_stack state leading continues
    have currentSlot : (feed state leading).stack[depth-1]'(by rw [currentStack]; omega) = BitVec.ofNat 64 parent.val := by
      simpa only [currentStack] using parentSlot
    have guard := nested_end_parent_guard (feed state leading) byte native tag parent depth positiveDepth (by omega)
      (by rw [currentStack]; exact stackShape) (context.2.2.1.trans depthEq) currentSlot decoded accepted
    rw [if_neg mismatch] at guard
    have rejected := actual_key_guard_reject (feed state leading) byte invariant.1 terminal guard
    rw [span]
    apply finish_invalid_sticky
    simp only [feed,List.foldl_append,List.foldl_cons]
    exact feed_invalid_sticky _ tail rejected

#print axioms native_group_end_mismatch_reject
end ChatResponseReference.StreamingUnknownV1
