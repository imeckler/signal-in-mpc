import ChatResponseReferenceWork.StreamingV1.AnyKeySuccess
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- All-input payload/length varint bridge. Exact source value/tail determines
actual Core accumulator and reset, without a supplied terminal-prefix premise. -/
theorem any_native_varint_success (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (role : Nat) (roleBound : role < 3)
    (modes : state.modes = lane role) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ leading byte tail,
      contents before = leading ++ byte::tail ∧ contents after = tail ∧
      leading.length+1 ≤ before.length ∧
      coreDecoded (feed state leading) byte = native.bv ∧
      let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (feed state leading) byte).state
      next.value = 0 ∧ next.positions = oneHot 0 := by
  cases lexer_shape (contents before) with
  | terminal leading tail byte span bound continues ended tenth =>
    obtain ⟨decoded,suffix,run,decodedValue,suffixTail,lengthBound⟩ :=
      core_terminal_native state before leading tail byte role roleBound bound modes positions value span continues ended tenth
    rw [sourceSuccess] at run
    have nativeEq : native = decoded := by
      have same := congrArg Prod.fst (Result.ok.inj run)
      exact core.result.Result.Ok.inj same
    have suffixEq : after = suffix := congrArg Prod.snd (Result.ok.inj run)
    have invariant := core_prefix_invariant state leading role 0 roleBound (by omega) modes positions continues
    refine ⟨leading,byte,tail,span,?_,lengthBound,?_,?_,?_⟩
    · rw [suffixEq]; exact suffixTail
    · rw [nativeEq]; exact decodedValue.symm
    · exact terminal_value_reset _ byte role roleBound invariant.1 ended
    · apply terminal_position_reset _ byte role leading.length roleBound invariant.1
      · simpa only [Nat.zero_add] using invariant.2.1
      · exact ended
  | malformed leading tail byte span length continues invalid =>
    have numeric := rejected_tenth_row leading tail byte length continues invalid
    rw [←span] at numeric
    obtain ⟨error,suffix,run,_,_⟩ := native_prefix_rejection before numeric
    rw [sourceSuccess] at run
    simp at run
  | truncated leading span bound continues =>
    have numeric := truncated_row leading (by omega) continues
    rw [←span] at numeric
    obtain ⟨error,suffix,run,_,_⟩ := native_prefix_rejection before numeric
    rw [sourceSuccess] at run
    simp at run

/-- Every actual varint error rejects Core through the remaining input and EOF.
An empty key boundary is not an attempted field; empty scalar/length payloads are. -/
theorem any_native_varint_error_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (error : LoopSupportSkip.error.DecodeError) (role : Nat) (roleBound : role < 3)
    (modes : state.modes = lane role) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (attempted : role ≠ 0 ∨ 0 < before.length)
    (sourceError : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  cases lexer_shape (contents before) with
  | terminal leading tail byte span bound continues ended tenth =>
    obtain ⟨native,suffix,run,_,_,_⟩ :=
      core_terminal_native state before leading tail byte role roleBound bound modes positions value span continues ended tenth
    rw [sourceError] at run
    simp at run
  | malformed leading tail byte span length continues invalid =>
    rw [span]
    exact bad_tenth_suffix_reject state leading tail byte role roleBound length modes positions continues invalid
  | truncated leading span bound continues =>
    rw [span]
    apply prefix_eof_reject state leading role roleBound bound modes positions continues
    rcases attempted with nonkey | nonempty
    · exact .inl nonkey
    · have len : (contents before).length = before.length := by simp only [contents,List.length_map]
      rw [span] at len
      exact .inr (by omega)

#print axioms any_native_varint_success
#print axioms any_native_varint_error_reject
end ChatResponseReference.StreamingV1
