import ChatResponseReferenceWork.StreamingV1.SourceCache
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

theorem actual_scalar_cache_resumes (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (budget remaining : Nat) (isStatus : Bool)
    (ready : ChildReady state before budget remaining) (cache : CacheAgrees outer source state)
    (fits : before.length-remaining ≤ after.length) (modes : state.modes = lane 1)
    (known : state.scalarKnown = 255) (tag : state.tag = if isStatus then 2 else 1)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    (if isStatus then ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (2#u32) .Varint before ctx
      else ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (1#u32) .Varint before ctx) =
      .ok (.Ok (),if isStatus then {source with status := some (UScalar.cast .U32 native)} else {source with id := some native},after) ∧
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      CacheAgrees outer (if isStatus then {source with status := some (UScalar.cast .U32 native)} else {source with id := some native}) (feed state consumed) ∧
      ChildAtKey (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) := by
  obtain ⟨sourceResult,consumed,span,data,boundary⟩ := actual_scalar_resumes source state before after native ctx budget remaining isStatus ready fits modes known tag sourceSuccess
  refine ⟨sourceResult,consumed,span,?_,boundary⟩
  unfold CacheAgrees at cache ⊢
  rw [data,cache]
  cases isStatus with
  | false => exact (source_cache_id outer source native).symm
  | true => exact (source_cache_status outer source native).symm

#print axioms actual_scalar_cache_resumes
end ChatResponseReference.StreamingV1
