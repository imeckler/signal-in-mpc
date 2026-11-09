import ChatResponseReferenceWork.StreamingV1.VarintSpan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000

/-- A bounded parent/child cursor check, not a supplied prefix-length assumption,
keeps native scalar recognition and inner context alive until the terminal byte. -/
theorem bounded_scalar_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (remaining : Nat)
    (capacity : remaining ≤ 4096) (physical : remaining ≤ before.length)
    (fits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ leading byte tail,
      contents before = leading ++ byte::tail ∧ contents after = tail ∧ leading.length ≤ 9 ∧
      VarintDecode.Spqr.terminates byte = true ∧
      let current := feed state leading
      current.tag = state.tag ∧ current.scalarKnown = state.scalarKnown ∧ current.inner = 255 ∧
      current.modes = lane 1 ∧ current.positions = oneHot leading.length ∧
      coreDecoded current byte = native.bv := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ :=
    native_success_span before after native sourceSuccess
  have afterLen : after.length = tail.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result
  have beforeLen : before.length = leading.length+1+tail.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  have inside : leading.length < remaining := by omega
  have context := scalar_prefix_context state leading remaining capacity inside modes inner counter continues
  have invariant := core_prefix_invariant state leading 1 0 (by decide) (by omega) modes positions continues
  refine ⟨leading,byte,tail,span,suffix,bound,terminal,context.1,context.2.1,context.2.2.1,invariant.1,?_,?_⟩
  · simpa only [Nat.zero_add] using invariant.2.1
  · have afterPositions : (feed state leading).positions = oneHot leading.length := by
      simpa only [Nat.zero_add] using invariant.2.1
    have afterValue : (feed state leading).value = accumulated leading 0 0 := by
      simpa only [value] using invariant.2.2
    simp only [coreDecoded,afterPositions,afterValue,contribution_one_hot leading.length (by omega) byte]
    exact nativeValue.symm

/-- Full-width source ID reaches the actual Core ID update without assuming
prefix context or borrowing bytes beyond the explicit child limit. -/
theorem bounded_scalar_id_update (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (remaining : Nat)
    (capacity : remaining ≤ 4096) (physical : remaining ≤ before.length)
    (fits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (known : state.scalarKnown = 255) (tag : state.tag = 1)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ leading byte tail,
      contents before = leading ++ byte::tail ∧ contents after = tail ∧
      (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state.id = native.bv := by
  obtain ⟨leading,byte,tail,span,suffix,bound,terminal,tagEq,knownEq,inside,currentModes,currentPositions,decoded⟩ :=
    bounded_scalar_terminal state before after native remaining capacity physical fits modes positions value inner counter sourceSuccess
  have result := core_id_terminal (feed state leading) leading.length (by omega) byte currentModes currentPositions
    (knownEq.trans known) inside (tagEq.trans tag) terminal
  refine ⟨leading,byte,tail,span,suffix,result.trans ?_⟩
  unfold coreDecoded at decoded
  rw [currentPositions,contribution_one_hot leading.length (by omega) byte] at decoded
  exact decoded

/-- The bounded source uint32 status update uses exactly the pinned truncation,
including uint64 varints whose high 32 bits are nonzero. -/
theorem bounded_scalar_status_update (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (remaining : Nat)
    (capacity : remaining ≤ 4096) (physical : remaining ≤ before.length)
    (fits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (known : state.scalarKnown = 255) (tag : state.tag = 2)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ leading byte tail,
      contents before = leading ++ byte::tail ∧ contents after = tail ∧
      (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state.status =
        statusWord (UScalar.cast .U32 native) := by
  obtain ⟨leading,byte,tail,span,suffix,bound,terminal,tagEq,knownEq,inside,currentModes,currentPositions,decoded⟩ :=
    bounded_scalar_terminal state before after native remaining capacity physical fits modes positions value inner counter sourceSuccess
  have result := core_status_terminal (feed state leading) leading.length (by omega) byte currentModes currentPositions
    (knownEq.trans known) inside (tagEq.trans tag) terminal
  refine ⟨leading,byte,tail,span,suffix,?_⟩
  rw [result,status_cast_projection native]
  unfold coreDecoded at decoded
  rw [currentPositions,contribution_one_hot leading.length (by omega) byte] at decoded
  exact congrArg (fun word : BitVec 64 => word &&& 4294967295) decoded

#print axioms bounded_scalar_terminal
#print axioms bounded_scalar_id_update
#print axioms bounded_scalar_status_update
end ChatResponseReference.StreamingV1
