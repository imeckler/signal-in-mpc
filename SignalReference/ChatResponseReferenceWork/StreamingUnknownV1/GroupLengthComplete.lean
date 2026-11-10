import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthHeaderComplete
import ChatResponseReferenceWork.StreamingUnknownV1.GroupOpaqueComplete
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Complete actual native length/opaque field span inside a group, including
zero payload, arbitrary bytes and nonminimal accepted length encodings. Actual
known cache/depth/full stack and private bounds remain exact. -/
theorem group_length_value_complete (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (budget remaining : Nat) (ready : ChildReady (eraseGroupDepth state) before budget remaining)
    (cache : CacheAgrees outer source state) (strictFit : native.val+(before.length-after.length) < remaining)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,0,0,0])
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,
      contents before = consumed ++ contents (drop after native.val) ∧ CacheAgrees outer source (feed state consumed) ∧
      (feed state consumed).modes = lane 0 ∧ (feed state consumed).positions = oneHot 0 ∧
      (feed state consumed).value = 0 ∧ (feed state consumed).valid = 255 ∧
      (feed state consumed).depth = state.depth ∧ (feed state consumed).stack = state.stack ∧
      (feed state consumed).responseRemaining = BitVec.ofNat 64 (remaining-consumed.length) ∧
      (feed state consumed).inner = 255 := by
  obtain ⟨header,span,headerCache,headerKinds,headerSkip,headerReady,headerMode,headerDepth,headerStack⟩ :=
    group_length_header_complete outer source state before after native budget remaining ready cache strictFit modes kinds actual
  have inputLength : before.length = header.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  by_cases empty : native.val = 0
  · rw [if_pos empty] at headerMode
    have dropped : drop after native.val = after := by rw [empty]; simp only [drop,List.drop_zero]; cases after; rfl
    rw [dropped]
    exact ⟨header,span,headerCache,headerMode,headerReady.positions,headerReady.value,headerReady.valid,headerDepth,headerStack,headerReady.childCounter,headerReady.inner⟩
  · rw [if_neg empty] at headerMode
    have nativeBound : native.val < 2^64 := native.bv.isLt
    have nativeBits : native.bv = BitVec.ofNat 64 native.val := by
      apply BitVec.eq_of_toNat_eq
      simp only [UScalar.bv_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt nativeBound]
    obtain ⟨payload,payloadBytes,payloadSpan,payloadCache,payloadModes,payloadPositions,payloadValue,payloadValid,payloadDepth,payloadStack,payloadRemaining,payloadInner⟩ :=
      group_opaque_value_complete outer source (feed state header) after native.val (budget-header.length) (remaining-header.length)
        headerReady headerCache (by omega) (by omega) headerMode headerKinds (headerSkip.trans nativeBits)
    have physical : native.val ≤ after.length := by have := ready.physical; omega
    have payloadLength : payload.length = native.val := by
      rw [payloadBytes,List.length_take]
      have length : (contents after).length = after.length := by simp only [contents,List.length_map]
      rw [length,Nat.min_eq_left physical]
    let consumed := header++payload
    have completeSpan : contents before = consumed++contents (drop after native.val) := by rw [span,payloadSpan,List.append_assoc]
    refine ⟨consumed,completeSpan,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [consumed,feed,List.foldl_append] using payloadCache
    · simpa only [consumed,feed,List.foldl_append] using payloadModes
    · simpa only [consumed,feed,List.foldl_append] using payloadPositions
    · simpa only [consumed,feed,List.foldl_append] using payloadValue
    · simpa only [consumed,feed,List.foldl_append] using payloadValid
    · simpa only [consumed,feed,List.foldl_append] using payloadDepth.trans headerDepth
    · simpa only [consumed,feed,List.foldl_append] using payloadStack.trans headerStack
    · simpa only [consumed,feed,List.foldl_append,List.length_append,payloadLength,Nat.sub_sub] using payloadRemaining
    · simpa only [consumed,feed,List.foldl_append] using payloadInner

#print axioms group_length_value_complete
end ChatResponseReference.StreamingUnknownV1
