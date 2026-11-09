import ChatResponseReferenceWork.StreamingV1.PrefixOverrun
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Physically available length-delimited payload that crosses the declared
child limit rejects the actual Core. The actual native field may copy/consume it
before its parent reports DelimitedLengthExceeded; that source cursor is not
equated to the earlier Core rejection point. Covers key/scalar length contents
independently of body/string/header recognition or payload values. -/
theorem native_length_child_overrun_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (remaining : Nat)
    (capacity : remaining ≤ 4096) (positive : 0 < remaining) (physical : remaining ≤ before.length)
    (payloadFits : native.val ≤ after.length)
    (overrun : (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val).length < before.length-remaining)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native sourceSuccess
  by_cases headerFits : leading.length+1 ≤ remaining
  · have inside : leading.length < remaining := by omega
    have context := bounded_varint_prefix_context state leading remaining capacity inside inner counter continues
    have invariant := core_prefix_invariant state leading 2 0 (by decide) (by omega) modes positions continues
    have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
    have currentValue : (feed state leading).value = accumulated leading 0 0 := by simpa only [value] using invariant.2.2
    have decoded : coreDecoded (feed state leading) byte = native.bv := by
      unfold coreDecoded
      rw [currentPositions,currentValue,contribution_one_hot leading.length (by omega) byte]
      exact nativeValue.symm
    have tailLength : tail.length = after.length := by
      have result := congrArg List.length suffix
      simpa only [contents,List.length_map] using result.symm
    have inputLength : before.length = leading.length+1+after.length := by
      have result := congrArg List.length span
      simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
    have dropped : (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val).length = after.length-native.val := by
      change (after.val.drop native.val).length = _
      rw [List.length_drop]
    have tooLarge : remaining-(leading.length+1) < native.val := by rw [dropped] at overrun; omega
    have available : availableLength (feed state leading) = BitVec.ofNat 64 (remaining-(leading.length+1)) := by
      unfold availableLength
      rw [context.2.2.2.1,Word64.select_accept,context.2.2.2.2]
      change BitVec.ofNat 64 (remaining-leading.length) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (remaining-leading.length) 1 (by decide) (by omega)]
      congr 1 <;> omega
    have rejected : Word64.concrete.ule (coreDecoded (feed state leading) byte) (availableLength (feed state leading)) = 0 := by
      rw [decoded,available,Word64.ule_value]
      have small : remaining-(leading.length+1) < 2^64 := by omega
      simp only [UScalar.bv_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
      exact if_neg (by omega)
    have invalid := core_length_reject (feed state leading) byte invariant.1 terminal rejected
    rw [span]
    apply finish_invalid_sticky
    simp only [feed,List.foldl_append,List.foldl_cons]
    exact feed_invalid_sticky _ tail invalid
  · have crosses : remaining ≤ leading.length := by omega
    rw [span]
    exact varint_child_prefix_overrun state leading (byte::tail) remaining 2 (by decide) capacity positive crosses modes inner counter continues

#print axioms native_length_child_overrun_reject
end ChatResponseReference.StreamingV1
