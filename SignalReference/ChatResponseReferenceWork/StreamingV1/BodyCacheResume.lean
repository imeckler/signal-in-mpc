import ChatResponseReferenceWork.StreamingV1.ScalarCacheResume
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

theorem actual_body_cache_resumes (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (ready : ChildReady state before budget remaining) (cache : CacheAgrees outer source state)
    (physical : native.val ≤ after.length) (fits : native.val + (before.length-after.length) ≤ remaining)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,255,0,0])
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (4#u32) .LengthDelimited before ctx =
      .ok (.Ok (),{source with body := some ⟨ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val⟩},
        LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
      CacheAgrees outer {source with body := some ⟨ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val⟩} (feed state consumed) ∧
      ChildAtKey (feed state consumed) (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val)
        (budget-consumed.length) (remaining-consumed.length) ∧
      ∃ header,
        consumed = header ++ contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val) ∧
        bodyTrace (feed state header) (contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val)) =
          (contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val)).map (fun byte => (255,0,0,byte)) := by
  obtain ⟨sourceResult,consumed,span,data,boundary,header,headerEq,events⟩ := actual_body_resumes source state before after native ctx budget remaining ready physical fits modes kinds sourceSuccess
  refine ⟨sourceResult,consumed,span,?_,boundary,header,headerEq,events⟩
  unfold CacheAgrees at cache ⊢
  rw [data,cache]
  exact (source_cache_body outer source after native physical).symm

#print axioms actual_body_cache_resumes
end ChatResponseReference.StreamingV1
