import ChatResponseReferenceWork.StreamingV1.ScalarPrefixContext
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- An actual successful source varint derives its complete terminal span;
there is no prefix decomposition or decoder-correctness premise. -/
theorem native_success_span (before after : Slice U8) (native : U64)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ leading byte tail,
      contents before = leading ++ byte::tail ∧ contents after = tail ∧
      leading.length ≤ 9 ∧
      (∀ x ∈ leading, VarintDecode.Spqr.terminates x = false) ∧
      VarintDecode.Spqr.terminates byte = true ∧
      (leading.length = 9 → byte.toNat < 2) ∧
      native.bv = accumulated leading 0 0 ||| VarintDecode.Spqr.payload byte leading.length := by
  cases lexer_shape (contents before) with
  | terminal leading tail byte span bound continues ended tenth =>
    have row := strict_terminal_row leading tail byte bound continues ended tenth
    rw [←span] at row
    obtain ⟨decoded,run,decodedValue,_⟩ := native_prefix_success before (leading.length+1)
      (accumulated leading 0 0 ||| VarintDecode.Spqr.payload byte leading.length) (by omega) row
    rw [sourceSuccess] at run
    have nativeEq : native = decoded := core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj run))
    have suffixEq : after = drop before (leading.length+1) := congrArg Prod.snd (Result.ok.inj run)
    refine ⟨leading,byte,tail,span,?_,bound,continues,ended,tenth,?_,⟩
    · rw [suffixEq,contents_drop,span]
      have split : (leading ++ byte::tail).drop (leading.length+1) =
          ((leading ++ byte::tail).drop leading.length).drop 1 := by rw [List.drop_drop]
      rw [split]
      simp
    · rw [nativeEq]; exact decodedValue
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

#print axioms native_success_span
end ChatResponseReference.StreamingV1
