import ChatResponseReferenceWork.StreamingV1.NativeScalarScope
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

theorem actual_scalar_field_scoped (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (budget remaining : Nat) (isStatus : Bool)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (childFits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget) (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (known : state.scalarKnown = 255) (tag : state.tag = if isStatus then 2 else 1)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    (if isStatus then ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (2#u32) .Varint before ctx
      else ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (1#u32) .Varint before ctx) =
      .ok (.Ok (),if isStatus then {source with status := some (UScalar.cast .U32 native)} else {source with id := some native},after) ∧
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      responseData (feed state consumed) = scalarUpdateData isStatus (responseData state) native ∧
      (feed state consumed).valid = 255 ∧ (feed state consumed).modes = lane 0 ∧
      (feed state consumed).positions = oneHot 0 ∧ (feed state consumed).value = 0 ∧
      (feed state consumed).budget = BitVec.ofNat 64 (budget-consumed.length) ∧
      (feed state consumed).responseRemaining = BitVec.ofNat 64 (remaining-consumed.length) ∧
      (feed state consumed).inner = (if consumed.length = remaining then 0 else 255) ∧
      (feed state consumed).depth = state.depth := by
  obtain ⟨sourceResult,consumed,span,data,completeValid,finalModes,finalPositions,finalValue⟩ :=
    actual_scalar_field_complete source state before after native ctx budget remaining isStatus budgetBound remainingBound
      budgetEnough physical childFits modes positions value valid seen finished inner depth budgetCounter childCounter known tag sourceSuccess
  obtain ⟨scopeConsumed,scopeSpan,scopeRemaining,scopeInner,scopeDepth⟩ := native_scalar_scope state before after native remaining
    remainingBound physical childFits modes positions inner childCounter sourceSuccess
  have unique : scopeConsumed = consumed := consumed_prefix_unique _ _ _ _ scopeSpan span
  subst scopeConsumed
  have inputLength : consumed.length+after.length = before.length := by
    have result := consumed_prefix_length _ _ _ span
    simpa only [contents,List.length_map] using result
  exact ⟨sourceResult,consumed,span,data,completeValid,finalModes,finalPositions,finalValue,
    feed_budget state consumed budget (by omega) budgetCounter,scopeRemaining,scopeInner,scopeDepth⟩

#print axioms actual_scalar_field_scoped
end ChatResponseReference.StreamingV1
