import ChatResponseReferenceWork.StreamingV1.PrefixValue
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

theorem contents_drop (before : Slice U8) (count : Nat) :
    contents (drop before count) = (contents before).drop count := by
  simp only [contents,drop,List.map_drop]

/-- Native prefix success advances the absolute input cursor by exactly count,
with no wrapping inference or capacity-tail replacement for the actual suffix. -/
theorem native_prefix_absolute (before : Slice U8) (wire : List (BitVec 8))
    (start count : Nat) (value : BitVec 64) (startBound : start ≤ wire.length)
    (countBound : count ≤ 10) (span : contents before = wire.drop start)
    (numeric : ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (contents before) 0 = ⟨255,BitVec.ofNat 64 count,value⟩) :
    ∃ native after,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after) ∧
      native.bv = value ∧ contents after = wire.drop (start+count) ∧ start+count ≤ wire.length := by
  obtain ⟨native,run,valueEq,lengthBound⟩ := native_prefix_success before count value countBound numeric
  have lengthSpan := congrArg List.length span
  have lengths : before.length = wire.length-start := by
    simpa only [contents,List.length_map,List.length_drop] using lengthSpan
  refine ⟨native,drop before count,run,valueEq,?_,by omega⟩
  rw [contents_drop,span,List.drop_drop]

/-- Error suffixes remain exact before owned observation, including the native
fast decoder's unchanged cursor. No slow-path consumption is fabricated. -/
theorem native_rejection_absolute (before : Slice U8) (wire : List (BitVec 8))
    (start : Nat) (startBound : start ≤ wire.length) (span : contents before = wire.drop start)
    (numeric : (ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (contents before) 0).ok = 0) :
    ∃ after,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Err invalidError,after) ∧
      contents after = wire.drop (start + if FastGuard before then 0 else min 10 before.length) ∧
      start + (if FastGuard before then 0 else min 10 before.length) ≤ wire.length := by
  obtain ⟨error,after,run,errorEq,suffix⟩ := native_prefix_rejection before numeric
  subst error
  have lengthSpan := congrArg List.length span
  have lengths : before.length = wire.length-start := by
    simpa only [contents,List.length_map,List.length_drop] using lengthSpan
  refine ⟨after,run,?_,?_⟩
  · rw [suffix]
    split
    · simpa using span
    · rw [contents_drop,span,List.drop_drop]
  · split <;> omega

/-- Bounded absolute cursor arithmetic used by the streaming relation cannot
wrap at64bits; this is derived from the actual input bound. -/
theorem cursor_word_exact (wire : List (BitVec 8)) (start count : Nat)
    (capacity : wire.length ≤ 4096) (endBound : start+count ≤ wire.length) :
    (Word64.concrete.add (Word64.concrete.const start) (Word64.concrete.const count)).toNat = start+count := by
  have hs : start < 2^64 := by omega
  have hc : count < 2^64 := by omega
  have he : start+count < 2^64 := by omega
  simp only [Word64.concrete,BitVec.toNat_add,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hs,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt he]
#print axioms contents_drop
#print axioms native_prefix_absolute
#print axioms native_rejection_absolute
#print axioms cursor_word_exact
end ChatResponseReference.StreamingV1
