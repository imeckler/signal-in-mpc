import ChatResponseReferenceWork.StreamingV1.StringCopy
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Native-derived complete String field validity, including rejected UTF8,
empty fields/duplicates and exact consumed source suffix. No post-header premise. -/
theorem native_message_field_validity (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (payloadPhysical : native.val ≤ after.length)
    (childFits : native.val + (before.length-after.length) ≤ remaining)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0)
    (utfShape : state.utf.length = 8) (value : state.value = 0) (kinds : state.kinds = [0,0,255,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
      (feed state consumed).valid = if Utf8.accepts ((copiedString after native).val.map (fun byte => byte.bv)) then 255 else 0 := by
  let payload := (copiedString after native).val.map (fun byte => byte.bv)
  have payloadLength : payload.length = native.val := copied_string_length after native payloadPhysical
  obtain ⟨header,span,headerValid,headerUtf,headerBudget,headerRemaining,headerKinds,headerDepth,headerSkip,headerModes,headerInner⟩ :=
    native_message_header_state state before after native budget remaining budgetBound remainingBound budgetEnough physical childFits
      modes positions utfShape value kinds valid seen finished inner depth budgetCounter childCounter sourceSuccess
  have headerLength : before.length = header.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  have partition : contents before = (header ++ payload) ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) := by
    rw [span,copied_body_partition after native payloadPhysical]
    simp only [payload,copied_string_bytes,List.append_assoc]
  refine ⟨header ++ payload,partition,?_⟩
  by_cases empty : native.val = 0
  · have noPayload : payload = [] := List.length_eq_zero_iff.mp (payloadLength.trans empty)
    change (feed state (header ++ payload)).valid = if Utf8.accepts payload then 255 else 0
    rw [noPayload,List.append_nil]
    exact headerValid
  · rw [if_neg empty] at headerModes
    have nativeBound : native.val < 2^64 := native.bv.isLt
    have nativeBits : native.bv = BitVec.ofNat 64 native.val := by
      apply BitVec.eq_of_toNat_eq
      simp only [UScalar.bv_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt nativeBound]
    have result := message_payload_agreement (feed state header) payload (budget-header.length) (remaining-header.length)
      (by omega) (by omega) (by omega) (by omega) headerModes headerKinds headerValid
      ((feed_seen state header).trans seen) ((feed_finished state header).trans finished)
      (headerInner empty) headerDepth (by rw [payloadLength]; exact headerSkip.trans nativeBits)
      headerBudget headerRemaining headerUtf
    simpa only [feed,List.foldl_append,payload] using result

#print axioms native_message_field_validity
end ChatResponseReference.StreamingV1
