import ChatResponseReferenceWork.StreamingV1.StampedSuccess
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual generated id success forces actual native varint success and exact source update/suffix. -/
theorem actual_id_success_native (source next : InnerResponseV1.Message) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext)
    (observed : merge_response InnerResponseV1.sliceBuf source (1#u32) .Varint before ctx = .ok (.Ok (),next,after)) :
    ∃ native, LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after) ∧
      next = {source with id := some native} := by
  obtain ⟨decoded,middle,run,_,_⟩ := decode_full_reference before
  rw [actual_id_field_decoded source before middle ctx decoded run] at observed
  cases decoded with
  | Err error =>
    simp only [idFieldDecoded,InnerResponseV1.scalarResult64] at observed
    have success := stamped_field_success _ _ _ _ _ _ observed
    cases success.1
  | Ok native =>
    change Result.ok ((core.result.Result.Ok () : core.result.Result Unit prost.error.DecodeError),{source with id := some native},middle) = .ok ((core.result.Result.Ok () : core.result.Result Unit prost.error.DecodeError),next,after) at observed
    have same := Result.ok.inj observed
    have valueEq := congrArg (fun x => x.2.1) same
    have cursorEq : middle = after := congrArg (fun x => x.2.2) same
    refine ⟨native,?_,valueEq.symm⟩
    rw [←cursorEq]
    exact run

#print axioms actual_id_success_native

/-- Actual generated status success forces actual native varint success and exact source update/suffix. -/
theorem actual_status_success_native (source next : InnerResponseV1.Message) (before after : Slice U8)
    (ctx : prost.encoding.DecodeContext)
    (observed : merge_response InnerResponseV1.sliceBuf source (2#u32) .Varint before ctx = .ok (.Ok (),next,after)) :
    ∃ native, LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after) ∧
      next = {source with status := some (UScalar.cast .U32 native)} := by
  obtain ⟨decoded,middle,run,_,_⟩ := decode_full_reference before
  rw [actual_status_field_decoded source before middle ctx decoded run] at observed
  cases decoded with
  | Err error =>
    simp only [statusFieldDecoded,InnerResponseV1.scalarResult32] at observed
    have success := stamped_field_success _ _ _ _ _ _ observed
    cases success.1
  | Ok native =>
    change Result.ok ((core.result.Result.Ok () : core.result.Result Unit prost.error.DecodeError),{source with status := some (UScalar.cast .U32 native)},middle) = .ok ((core.result.Result.Ok () : core.result.Result Unit prost.error.DecodeError),next,after) at observed
    have same := Result.ok.inj observed
    have valueEq := congrArg (fun x => x.2.1) same
    have cursorEq : middle = after := congrArg (fun x => x.2.2) same
    refine ⟨native,?_,valueEq.symm⟩
    rw [←cursorEq]
    exact run

#print axioms actual_status_success_native

end ChatResponseReference.StreamingV1
