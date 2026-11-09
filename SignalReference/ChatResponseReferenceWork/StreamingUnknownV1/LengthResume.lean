import ChatResponseReferenceWork.StreamingUnknownV1.LengthHeaderReady
import ChatResponseReferenceWork.StreamingUnknownV1.OpaqueResume
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Complete fitting unknown length-delimited field: unchanged actual source
record and exact drop compose with the full numeric cache/private-child invariant.
Both empty exact-end fields and arbitrary nonempty opaque payloads are covered. -/
theorem actual_unknown_length_resumes (outer : ResponseData) (source : InnerResponseV1.Message)
    (tag : U32) (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (budget remaining : Nat) (ready : ChildReady state before budget remaining)
    (cache : CacheAgrees outer source state) (unknown : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (fits : native.val + (before.length-after.length) ≤ remaining)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,0,0,0])
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag .LengthDelimited before ctx =
      .ok (.Ok (),source,drop after native.val) ∧
    ∃ consumed,
      contents before = consumed ++ contents (drop after native.val) ∧
      CacheAgrees outer source (feed state consumed) ∧
      ChildAtKey (feed state consumed) (drop after native.val) (budget-consumed.length) (remaining-consumed.length) := by
  obtain ⟨header,span,headerCache,headerKinds,headerSkip,headerReady⟩ :=
    actual_unknown_length_header_ready outer source state before after native budget remaining ready cache fits modes kinds actual
  have inputLength : before.length = header.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  have headerFit : header.length ≤ remaining := by omega
  have physical : native.val ≤ after.length := by have := ready.physical; omega
  have sourceResult := unknown_length_from_decode source tag before after ctx unknown count (.Ok native) actual
  have exactResult : unknownLengthResult source (.Ok native) after = (.Ok (),source,drop after native.val) := by
    simp only [unknownLengthResult,unchangedSkipResult,LibSignalReference.Candidate.ProstSkip.fixedResult,if_neg (by omega : ¬after.length < native.val)]
    rfl
  rw [exactResult] at sourceResult
  refine ⟨sourceResult,?_⟩
  by_cases empty : native.val = 0
  · rw [if_pos empty] at headerReady
    have dropped : drop after native.val = after := by
      rw [empty]
      simp only [drop,List.drop_zero]
      cases after
      rfl
    rw [dropped]
    exact ⟨header,span,headerCache,headerReady⟩
  · rw [if_neg empty] at headerReady
    have nativeBound : native.val < 2^64 := native.bv.isLt
    have nativeBits : native.bv = BitVec.ofNat 64 native.val := by
      apply BitVec.eq_of_toNat_eq
      simp only [UScalar.bv_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt nativeBound]
    obtain ⟨payload,payloadEq,payloadSpan,payloadCache,payloadReady⟩ :=
      unknown_opaque_resumes outer source (feed state header) after native.val (budget-header.length) (remaining-header.length)
        headerReady.1 headerCache (by omega) (by omega) headerReady.2 headerKinds (headerSkip.trans nativeBits)
    have payloadLength : payload.length = native.val := by
      rw [payloadEq,List.length_take]
      have len : (contents after).length = after.length := by simp only [contents,List.length_map]
      rw [len,Nat.min_eq_left physical]
    let consumed := header ++ payload
    refine ⟨consumed,?_,?_,?_⟩
    · rw [span,payloadSpan]
      simp only [consumed,List.append_assoc]
    · simpa only [consumed,feed,List.foldl_append] using payloadCache
    · have budgetEq : budget-header.length-native.val = budget-consumed.length := by
        simp only [consumed,List.length_append,payloadLength]; omega
      have remainingEq : remaining-header.length-native.val = remaining-consumed.length := by
        simp only [consumed,List.length_append,payloadLength]; omega
      rw [budgetEq,remainingEq] at payloadReady
      simpa only [consumed,feed,List.foldl_append] using payloadReady

#print axioms actual_unknown_length_resumes
end ChatResponseReference.StreamingUnknownV1
