import ChatResponseReferenceWork.StreamingV1.TerminalReader
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- The actual Core terminal value determines the actual pinned Prost result
and exact tail, with syntax/lookup conditions derived at the lexer boundary.
There is no native decode-result or response-validity premise. -/
theorem core_terminal_native (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before : Slice U8) (leading tail : List (BitVec 8)) (byte : BitVec 8)
    (role : Nat) (roleBound : role < 3) (bound : leading.length ≤ 9)
    (modes : state.modes = lane role) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (span : contents before = leading ++ byte::tail)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false)
    (terminal : VarintDecode.Spqr.terminates byte = true)
    (tenth : leading.length = 9 → byte.toNat < 2) :
    ∃ native after,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after) ∧
      native.bv = coreDecoded (feed state leading) byte ∧ contents after = tail ∧
      leading.length+1 ≤ before.length := by
  have numeric := core_terminal_row state leading tail byte role roleBound bound modes positions value continues terminal tenth
  rw [← span] at numeric
  obtain ⟨native,run,valueEq,lengthBound⟩ := native_prefix_success before (leading.length+1)
    (coreDecoded (feed state leading) byte) (by omega) numeric
  refine ⟨native,drop before (leading.length+1),run,valueEq,?_,lengthBound⟩
  rw [contents_drop,span]
  have split : (leading ++ byte::tail).drop (leading.length+1) =
      ((leading ++ byte::tail).drop leading.length).drop 1 := by rw [List.drop_drop]
  rw [split]
  simp
#print axioms core_terminal_native
end ChatResponseReference.StreamingV1
