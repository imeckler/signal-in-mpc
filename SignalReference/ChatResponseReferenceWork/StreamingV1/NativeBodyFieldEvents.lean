import ChatResponseReferenceWork.StreamingV1.NativeBodyHeaderState
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Header validity and native copied Bytes payload events joined on the exact
native suffix; includes empty bodies and exact child closure. -/
theorem native_body_field_events (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (payloadPhysical : native.val ≤ after.length)
    (childFits : native.val + (before.length-after.length) ≤ remaining)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0)
    (value : state.value = 0) (kinds : state.kinds = [0,255,0,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    let copied := ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val
    ∃ header,
      contents before = header ++ contents after ∧
      bodyTrace (feed state header) (contents copied) = (contents copied).map (fun byte => (255,0,0,byte)) ∧
      (feed state (header ++ contents copied)).valid = 255 := by
  let copied := ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val
  have copiedLength : (contents copied).length = native.val := by
    have result := copied_body_length after native payloadPhysical
    simpa only [contents,List.length_map] using result
  obtain ⟨header,span,headerValid,headerBudget,headerRemaining,headerKinds,headerDepth,headerSkip,headerModes,headerInner⟩ :=
    native_body_header_state state before after native budget remaining budgetBound remainingBound budgetEnough physical childFits
      modes positions value kinds valid seen finished inner depth budgetCounter childCounter sourceSuccess
  have headerLength : before.length = header.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  refine ⟨header,span,?_⟩
  by_cases empty : native.val = 0
  · have noPayload : contents copied = [] := List.length_eq_zero_iff.mp (copiedLength.trans empty)
    rw [noPayload]
    exact ⟨rfl,by simpa only [List.append_nil] using headerValid⟩
  · rw [if_neg empty] at headerModes
    have result := native_copied_body_events (feed state header) after native (budget-header.length) (remaining-header.length)
      payloadPhysical (by omega) (by omega) (by omega) (by omega) headerModes headerKinds headerValid
      ((feed_seen state header).trans seen) ((feed_finished state header).trans finished)
      (headerInner empty) headerDepth headerSkip headerBudget headerRemaining
    refine ⟨result.1,?_⟩
    simpa only [copied,feed,List.foldl_append] using result.2

#print axioms native_body_field_events
end ChatResponseReference.StreamingV1
