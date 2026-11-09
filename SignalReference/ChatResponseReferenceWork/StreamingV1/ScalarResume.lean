import ChatResponseReferenceWork.StreamingV1.InnerBoundary
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual source scalar field produces the next bounded key-loop state. -/
theorem actual_scalar_resumes (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (budget remaining : Nat) (isStatus : Bool)
    (ready : ChildReady state before budget remaining)
    (fits : before.length-remaining ≤ after.length) (modes : state.modes = lane 1)
    (known : state.scalarKnown = 255) (tag : state.tag = if isStatus then 2 else 1)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    (if isStatus then ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (2#u32) .Varint before ctx
      else ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (1#u32) .Varint before ctx) =
      .ok (.Ok (),if isStatus then {source with status := some (UScalar.cast .U32 native)} else {source with id := some native},after) ∧
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      responseData (feed state consumed) = scalarUpdateData isStatus (responseData state) native ∧
      ChildAtKey (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) := by
  obtain ⟨sourceResult,consumed,span,data,completeValid,finalModes,finalPositions,finalValue,finalBudget,finalRemaining,finalInner,finalDepth⟩ :=
    actual_scalar_field_scoped source state before after native ctx budget remaining isStatus ready.budgetBound ready.remainingBound
      ready.budgetEnough ready.physical fits modes ready.positions ready.value ready.valid ready.seen ready.finished ready.inner ready.depth
      ready.budgetCounter ready.childCounter known tag sourceSuccess
  have inputLength : before.length = consumed.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  exact ⟨sourceResult,consumed,span,data,child_boundary_after state before after budget remaining ready consumed span (by have := ready.physical; omega)
    finalPositions finalValue completeValid finalModes finalDepth finalRemaining finalInner⟩

#print axioms actual_scalar_resumes
end ChatResponseReference.StreamingV1
