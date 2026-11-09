import ChatResponseReferenceWork.StreamingV1.RejectedReader
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- Exhaustive strict Prost varint shapes; the remainder is never read as padding. -/
inductive LexerShape (wire : List (BitVec 8)) : Prop where
  | terminal (leading tail : List (BitVec 8)) (byte : BitVec 8)
      (span : wire = leading ++ byte::tail) (bound : leading.length ≤ 9)
      (continues : ∀ x ∈ leading, VarintDecode.Spqr.terminates x = false)
      (ended : VarintDecode.Spqr.terminates byte = true)
      (tenth : leading.length = 9 → byte.toNat < 2) : LexerShape wire
  | malformed (leading tail : List (BitVec 8)) (byte : BitVec 8)
      (span : wire = leading ++ byte::tail) (length : leading.length = 9)
      (continues : ∀ x ∈ leading, VarintDecode.Spqr.terminates x = false)
      (invalid : 2 ≤ byte.toNat) : LexerShape wire
  | truncated (leading : List (BitVec 8)) (span : wire = leading) (bound : leading.length ≤ 9)
      (continues : ∀ x ∈ leading, VarintDecode.Spqr.terminates x = false) : LexerShape wire

theorem small_byte_terminal : ∀ byte : BitVec 8, byte.toNat < 2 → VarintDecode.Spqr.terminates byte = true := by
  decide +kernel

theorem lexer_shape_from (fuel : Nat) (leading remaining : List (BitVec 8))
    (budget : leading.length+fuel = 9)
    (continues : ∀ x ∈ leading, VarintDecode.Spqr.terminates x = false) :
    LexerShape (leading ++ remaining) := by
  induction fuel generalizing leading remaining with
  | zero =>
    have length : leading.length = 9 := by omega
    cases remaining with
    | nil => exact .truncated leading (by simp) (by omega) continues
    | cons byte tail =>
      by_cases small : byte.toNat < 2
      · exact .terminal leading tail byte rfl (by omega) continues (small_byte_terminal byte small) (by intro _; exact small)
      · exact .malformed leading tail byte rfl length continues (by omega)
  | succ fuel ih =>
    cases remaining with
    | nil => exact .truncated leading (by simp) (by omega) continues
    | cons byte tail =>
      cases ended : VarintDecode.Spqr.terminates byte with
      | true => exact .terminal leading tail byte rfl (by omega) continues ended (by intro impossible; omega)
      | false =>
        have next : ∀ x ∈ leading ++ [byte], VarintDecode.Spqr.terminates x = false := by
          intro x member
          rcases List.mem_append.mp member with before | last
          · exact continues x before
          · have same : x = byte := by simpa only [List.mem_singleton] using last
            simpa only [same] using ended
        have result := ih (leading ++ [byte]) tail (by simp only [List.length_append,List.length_singleton]; omega) next
        simpa only [List.append_assoc,List.singleton_append] using result

/-- Every input, including empty, overlong, noncanonical and truncated input,
has one of the three proved native/Core lexer cases. No decoder result premise. -/
theorem lexer_shape (wire : List (BitVec 8)) : LexerShape wire := by
  simpa only [List.nil_append] using lexer_shape_from 9 [] wire rfl (by simp)
#print axioms lexer_shape
end ChatResponseReference.StreamingV1
