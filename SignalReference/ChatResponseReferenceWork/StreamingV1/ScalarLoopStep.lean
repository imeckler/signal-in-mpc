import ChatResponseReferenceWork.StreamingV1.ResponseStep
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

theorem actual_scalar_loop_step (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8)
    (native : U64) (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (isStatus : Bool) (limit : Usize)
    (limitExact : limit.val = before.length-remaining)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (fits : before.length-remaining ≤ after.length)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before =
      .ok (.Ok ((if isStatus then (2#u32) else (1#u32)),.Varint),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    SubmessageV1.body ctx limit (source,before,()) =
      .ok (.cont ((if isStatus then {source with status := some (UScalar.cast .U32 native)} else {source with id := some native}),after,())) ∧
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      CacheAgrees outer (if isStatus then {source with status := some (UScalar.cast .U32 native)} else {source with id := some native}) (feed state consumed) ∧
      ChildAtKey (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) := by
  obtain ⟨called,consumed,span,cacheAfter,boundaryAfter⟩ := actual_scalar_iteration outer source state before middle after native ctx budget remaining isStatus
    boundary cache positive fits keyRun valueRun
  exact ⟨actual_response_step_next source _ before after ctx limit (by rw [limitExact]; have := boundary.physical; omega) called,
    consumed,span,cacheAfter,boundaryAfter⟩

#print axioms actual_scalar_loop_step
end ChatResponseReference.StreamingV1
