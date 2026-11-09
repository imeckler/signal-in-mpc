import ChatResponseReferenceWork.StreamingV1.VarintPrefix
import ChatResponseReferenceWork.OuterEnvelopeV1.FullScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Accepted numeric prefix rows identify the actual native value AND exact
relative suffix. Count injectivity is explicit, rather than inferred from a
wrapping 64-bit cursor equality. -/
theorem native_prefix_success (before : Slice U8) (count : Nat) (value : BitVec 64)
    (countBound : count ≤ 10)
    (numeric : ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (contents before) 0 = ⟨255,BitVec.ofNat 64 count,value⟩) :
    ∃ native : U64,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,drop before count) ∧
      native.bv = value ∧ count ≤ before.length := by
  obtain ⟨result,after,run,post,errorPost⟩ := decode_full_reference before
  cases result with
  | Ok native =>
    obtain ⟨nativeCount,lengthBound,nativeBound,row,suffix⟩ := post
    rw [numeric] at row
    have countEq := congrArg (fun row : ProtoParse.Decoded (BitVec 8) (BitVec 64) => row.stop) row
    have valueEq := congrArg (fun row : ProtoParse.Decoded (BitVec 8) (BitVec 64) => row.value) row
    have small : count < 2^64 := by omega
    have nativeSmall : nativeCount < 2^64 := by omega
    have counts : count = nativeCount := by
      have numericCounts := congrArg BitVec.toNat countEq
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt nativeSmall] using numericCounts
    rw [suffix,← counts] at run
    exact ⟨native,run,valueEq.symm,by simpa only [counts] using lengthBound⟩
  | Err error =>
    have rejected := post.2
    rw [numeric] at rejected
    exact False.elim ((by decide : (255 : BitVec 8) ≠ 0) rejected)

/-- Rejected numeric rows match actual native rejection, including exact
fast-path unchanged cursor versus short slow-path consumed suffix. This theorem
includes malformed and truncated inputs, not merely successful prefixes. -/
theorem native_prefix_rejection (before : Slice U8)
    (numeric : (ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (contents before) 0).ok = 0) :
    ∃ error after,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after) ∧
      error = invalidError ∧
      after = if FastGuard before then before else drop before (min 10 before.length) := by
  obtain ⟨result,after,run,post,errorPost⟩ := decode_full_reference before
  cases result with
  | Err error => exact ⟨error,after,run,post.1,errorPost⟩
  | Ok value =>
    obtain ⟨count,lengthBound,countBound,row,suffix⟩ := post
    have accepted := congrArg (fun row : ProtoParse.Decoded (BitVec 8) (BitVec 64) => row.ok) row
    rw [numeric] at accepted
    exact False.elim ((by decide : (0 : BitVec 8) ≠ 255) accepted)
#print axioms native_prefix_success
#print axioms native_prefix_rejection
end ChatResponseReference.StreamingV1
