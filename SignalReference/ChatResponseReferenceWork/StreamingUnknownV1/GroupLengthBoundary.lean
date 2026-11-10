import ChatResponseReferenceWork.StreamingUnknownV1.GroupBoundaryRejection
import ChatResponseReferenceWork.StreamingUnknownV1.GroupScalarStack
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- A length header ending exactly at the private child boundary still leaves its group
unclosed. Core rejects at that real byte, irrespective of physical parent tail. -/
theorem native_group_length_at_child_end_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (remaining : Nat)
    (bounded : remaining ≤ 4096) (atEnd : before.length = remaining+after.length)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (notTop : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0 = 0)
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native actual
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result.symm
  have inputLength : before.length = leading.length+1+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  have context := bounded_varint_prefix_context state leading remaining bounded (by omega) inner counter continues
  have invariant := core_prefix_invariant state leading 2 0 (by decide) (by omega) modes positions continues
  have currentCounter : (feed state leading).responseRemaining = BitVec.ofNat 64 1 := by
    rw [context.2.2.2.2]
    congr 1
    omega
  have nextNotTop : TlsChatResponse.weq Word64.concrete ByteAuth.concrete
      (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state.depth 0 = 0 := by
    rw [body_length_depth_step _ byte invariant.1,context.2.2.1]
    exact notTop
  have rejected := core_close_active_group_reject (feed state leading) byte context.2.2.2.1 currentCounter nextNotTop
  rw [span]
  apply finish_invalid_sticky
  simp only [feed,List.foldl_append,List.foldl_cons]
  exact feed_invalid_sticky _ tail rejected

#print axioms native_group_length_at_child_end_reject
end ChatResponseReference.StreamingUnknownV1
