import ChatResponseReferenceWork.StreamingV1.NativeMessageHeaderScope
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Exact post-field private child/public budget/depth projection on the actual
native consumed String span; independent of payload UTF acceptance. -/
theorem native_message_field_scope (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
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
      (feed state consumed).budget = BitVec.ofNat 64 (budget-consumed.length) ∧
      (feed state consumed).responseRemaining = BitVec.ofNat 64 (remaining-consumed.length) ∧
      (feed state consumed).inner = (if consumed.length = remaining then 0 else 255) ∧
      (feed state consumed).depth = state.depth := by
  let payload := (copiedString after native).val.map (fun byte => byte.bv)
  have payloadLength : payload.length = native.val := copied_string_length after native payloadPhysical
  obtain ⟨header,span,headerValid,headerUtf,headerBudget,headerRemaining,headerKinds,headerDepth,headerSkip,headerModes,headerInner⟩ :=
    native_message_header_state state before after native budget remaining budgetBound remainingBound budgetEnough physical childFits
      modes positions utfShape value kinds valid seen finished inner depth budgetCounter childCounter sourceSuccess
  obtain ⟨scopeHeader,scopeSpan,scopeRemaining,scopeInner,scopeDepth⟩ :=
    native_message_header_scope state before after native remaining remainingBound physical (by omega) modes positions kinds inner childCounter sourceSuccess
  have unique : scopeHeader = header := consumed_prefix_unique _ _ _ _ scopeSpan span
  subst scopeHeader
  have headerLength : before.length = header.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  let consumed := header ++ payload
  have consumedLength : consumed.length = header.length+native.val := by simp only [consumed,List.length_append,payloadLength]
  have partition : contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) := by
    rw [span,copied_body_partition after native payloadPhysical]
    simp only [consumed,payload,copied_string_bytes,List.append_assoc]
  refine ⟨consumed,partition,feed_budget state consumed budget (by omega) budgetCounter,?_⟩
  by_cases empty : native.val = 0
  · have noPayload : payload = [] := List.length_eq_zero_iff.mp (payloadLength.trans empty)
    simpa only [consumed,noPayload,List.append_nil] using And.intro scopeRemaining (And.intro scopeInner scopeDepth)
  · rw [if_neg empty] at headerModes
    have nativeBound : native.val < 2^64 := native.bv.isLt
    have nativeBits : native.bv = BitVec.ofNat 64 native.val := by
      apply BitVec.eq_of_toNat_eq
      simp only [UScalar.bv_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt nativeBound]
    have result := opaque_scope_prefix (feed state header) payload native.val (remaining-header.length)
      (by omega) (by omega) (by rw [payloadLength]) (by omega) headerModes (headerSkip.trans nativeBits)
      (headerInner empty) headerRemaining
    refine ⟨?_,?_,?_⟩
    · simpa only [consumed,feed,List.foldl_append,Nat.sub_sub,List.length_append] using result.1
    · have equal : payload.length = remaining-header.length ↔ consumed.length = remaining := by omega
      simpa only [consumed,feed,List.foldl_append,equal] using result.2.1
    · simpa only [consumed,feed,List.foldl_append] using result.2.2.trans scopeDepth

#print axioms native_message_field_scope
end ChatResponseReference.StreamingV1
