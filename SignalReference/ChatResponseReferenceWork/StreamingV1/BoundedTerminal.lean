import ChatResponseReferenceWork.StreamingV1.FieldRecognition
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000

/-- A bounded parent/child cursor check, not a supplied prefix-length assumption,
keeps native scalar recognition and inner context alive until the terminal byte. -/
theorem bounded_varint_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (remaining role : Nat) (roleBound : role < 3)
    (capacity : remaining ≤ 4096) (physical : remaining ≤ before.length)
    (fits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane role) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ leading byte tail,
      contents before = leading ++ byte::tail ∧ contents after = tail ∧ leading.length ≤ 9 ∧
      VarintDecode.Spqr.terminates byte = true ∧
      let current := feed state leading
      current.tag = state.tag ∧ current.scalarKnown = state.scalarKnown ∧ current.depth = state.depth ∧ current.inner = 255 ∧
      current.modes = lane role ∧ current.positions = oneHot leading.length ∧
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
  have context := bounded_varint_prefix_context state leading remaining capacity inside inner counter continues
  have invariant := core_prefix_invariant state leading role 0 roleBound (by omega) modes positions continues
  refine ⟨leading,byte,tail,span,suffix,bound,terminal,context.1,context.2.1,context.2.2.1,context.2.2.2.1,invariant.1,?_,?_⟩
  · simpa only [Nat.zero_add] using invariant.2.1
  · have afterPositions : (feed state leading).positions = oneHot leading.length := by
      simpa only [Nat.zero_add] using invariant.2.1
    have afterValue : (feed state leading).value = accumulated leading 0 0 := by
      simpa only [value] using invariant.2.2
    simp only [coreDecoded,afterPositions,afterValue,contribution_one_hot leading.length (by omega) byte]
    exact nativeValue.symm

/-- Native successful outer varints retain outer context through all prefix bytes;
no inner-response counter is consulted at this level. -/
theorem outer_varint_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (role : Nat) (roleBound : role < 3)
    (modes : state.modes = lane role) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (inner : state.inner = 0)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ leading byte tail,
      contents before = leading ++ byte::tail ∧ contents after = tail ∧ leading.length ≤ 9 ∧
      VarintDecode.Spqr.terminates byte = true ∧
      let current := feed state leading
      current.tag = state.tag ∧ current.scalarKnown = state.scalarKnown ∧ current.depth = state.depth ∧ current.inner = 0 ∧
      current.modes = lane role ∧ current.positions = oneHot leading.length ∧
      coreDecoded current byte = native.bv := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ :=
    native_success_span before after native sourceSuccess
  have context := outer_varint_prefix_context state leading inner continues
  have invariant := core_prefix_invariant state leading role 0 roleBound (by omega) modes positions continues
  refine ⟨leading,byte,tail,span,suffix,bound,terminal,context.1,context.2.1,context.2.2.1,context.2.2.2,invariant.1,?_,?_⟩
  · simpa only [Nat.zero_add] using invariant.2.1
  · have afterPositions : (feed state leading).positions = oneHot leading.length := by
      simpa only [Nat.zero_add] using invariant.2.1
    have afterValue : (feed state leading).value = accumulated leading 0 0 := by
      simpa only [value] using invariant.2.2
    simp only [coreDecoded,afterPositions,afterValue,contribution_one_hot leading.length (by omega) byte]
    exact nativeValue.symm

#print axioms bounded_varint_terminal
#print axioms outer_varint_terminal
end ChatResponseReference.StreamingV1
