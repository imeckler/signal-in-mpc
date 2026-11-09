import ChatResponseReferenceWork.StreamingV1.TerminalNative
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- EOF cannot acquire a zero terminator from capacity padding. -/
theorem truncated_reader (leading : List (BitVec 8)) (bound : leading.length ≤ 10)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false) :
    VarintDecode.Spqr.decode leading = ⟨accumulated leading 0 0,leading.length,false⟩ := by
  have result := spec_run_prefix leading leading [] 0 0 (by simp) continues
  simpa only [VarintDecode.Spqr.decode,Nat.min_eq_right bound,Nat.zero_add] using result

theorem truncated_row (leading : List (BitVec 8)) (bound : leading.length ≤ 10)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false) :
    (ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete leading 0).ok = 0 := by
  apply prefix_decode_failed
  rw [truncated_reader leading bound continues]

theorem tenth_reader (leading tail : List (BitVec 8)) (byte : BitVec 8)
    (length : leading.length = 9)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false) :
    VarintDecode.Spqr.decode (leading ++ byte::tail) =
      ⟨accumulated leading 0 0 ||| VarintDecode.Spqr.payload byte 9,10,VarintDecode.Spqr.terminates byte⟩ := by
  have before := spec_run_prefix (leading ++ byte::tail) leading (byte::tail) 0 0 (by rfl) continues
  simp only [Nat.zero_add,length] at before
  unfold VarintDecode.Spqr.decode
  have fuel : min 10 (leading ++ byte::tail).length = 10 := by simp only [List.length_append,List.length_cons,length]; omega
  rw [fuel,show (10:Nat)=9+1 from rfl,spec_run_add,before]
  have lookup := terminal_lookup leading tail byte
  rw [length] at lookup
  simp only [VarintDecode.Spqr.run,Bool.false_eq_true,if_false,lookup,Option.getD_some]

theorem rejected_tenth_row (leading tail : List (BitVec 8)) (byte : BitVec 8)
    (length : leading.length = 9)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false)
    (invalid : 2 ≤ byte.toNat) :
    (ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (leading ++ byte::tail) 0).ok = 0 := by
  have lookup := terminal_lookup leading tail byte
  rw [length] at lookup
  apply LibSignalReference.Candidate.ProstSkipSlice.prefix_rejected_tenth
    (leading ++ byte::tail) (accumulated leading 0 0 ||| VarintDecode.Spqr.payload byte 9)
  · simpa only [lookup,Option.getD_some] using tenth_reader leading tail byte length continues
  · simpa only [lookup,Option.getD_some] using invalid

/-- Native error cursor is preserved, including the unchanged fast-path cursor.
This is deliberately not equated to the streaming machine's consumed-byte count. -/
theorem truncated_native (before : Slice U8) (bound : before.length ≤ 10)
    (continues : ∀ byte ∈ contents before, VarintDecode.Spqr.terminates byte = false) :
    ∃ error after,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after) ∧
      error = invalidError ∧
      after = if FastGuard before then before else drop before (min 10 before.length) := by
  apply native_prefix_rejection
  apply truncated_row _ _ continues
  simpa only [contents,List.length_map] using bound

#print axioms truncated_reader
#print axioms truncated_row
#print axioms tenth_reader
#print axioms rejected_tenth_row
#print axioms truncated_native
end ChatResponseReference.StreamingV1
