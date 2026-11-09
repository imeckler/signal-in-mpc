import ChatResponseReferenceWork.StreamingV1.PendingChildRejection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkipKey

/-- A native key ending exactly at the private child boundary still requires a
value for scalar/fixed/length wires. Core rejects before later parent bytes, so a
zero-remaining field cannot borrow capacity padding or the parent suffix. -/
theorem native_pending_key_at_child_end (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : WireType) (remaining : Nat)
    (bounded : remaining ≤ 4096) (atEnd : before.length = remaining+after.length)
    (pending : wireNumber wire = 0 ∨ wireNumber wire = 1 ∨ wireNumber wire = 2 ∨ wireNumber wire = 5)
    (modes : state.modes = lane 0) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨native,run,accepted⟩ := native_key_success_varint before after tag wire sourceSuccess
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native run
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result.symm
  have inputLength : before.length = leading.length+1+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  have exactLength : remaining = leading.length+1 := by omega
  have context := bounded_varint_prefix_context state leading remaining bounded (by omega) inner counter continues
  have invariant := core_prefix_invariant state leading 0 0 (by decide) (by omega) modes positions continues
  have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
  have currentValue : (feed state leading).value = accumulated leading 0 0 := by simpa only [value] using invariant.2.2
  have decoded : coreDecoded (feed state leading) byte = native.bv := by
    unfold coreDecoded
    rw [currentPositions,currentValue,contribution_one_hot leading.length (by omega) byte]
    exact nativeValue.symm
  have nextModes := native_key_modes _ byte native tag wire invariant.1 terminal decoded.symm accepted
  have notKey : TlsWebSocketUpgrade.get ByteAuth.concrete
      (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state.modes 0 = 0 := by
    rw [nextModes]
    rcases pending with h|h|h|h <;> rw [h] <;> rfl
  have currentCounter : (feed state leading).responseRemaining = BitVec.ofNat 64 1 := by
    rw [context.2.2.2.2]
    congr 1
    omega
  have invalid := core_close_pending_reject _ byte context.2.2.2.1 currentCounter notKey
  rw [span]
  apply finish_invalid_sticky
  simp only [feed,List.foldl_append,List.foldl_cons]
  exact feed_invalid_sticky _ tail invalid

#print axioms native_pending_key_at_child_end
end ChatResponseReference.StreamingV1
