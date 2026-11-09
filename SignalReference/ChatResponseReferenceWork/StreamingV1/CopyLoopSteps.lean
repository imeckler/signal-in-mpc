import ChatResponseReferenceWork.StreamingV1.MessageIteration
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

theorem actual_body_loop_step (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle afterLength : Slice U8)
    (native : U64) (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (limit : Usize)
    (limitExact : limit.val = before.length-remaining)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (physical : native.val ≤ afterLength.length)
    (fits : before.length-remaining ≤ (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val).length)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok ((4#u32),.LengthDelimited),middle))
    (lengthRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,afterLength)) :
    SubmessageV1.body ctx limit (source,before,()) =
      .ok (.cont ({source with body := some ⟨ActualResponseBytesV1.ContentModel.take afterLength (UScalar.cast .Usize native).val⟩},LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val,())) ∧
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val) ∧
      CacheAgrees outer {source with body := some ⟨ActualResponseBytesV1.ContentModel.take afterLength (UScalar.cast .Usize native).val⟩} (feed state consumed) ∧
      ChildAtKey (feed state consumed) (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val)
        (budget-consumed.length) (remaining-consumed.length) ∧
      ∃ header,
        consumed = header ++ contents (ActualResponseBytesV1.ContentModel.take afterLength (UScalar.cast .Usize native).val) ∧
        bodyTrace (feed state header) (contents (ActualResponseBytesV1.ContentModel.take afterLength (UScalar.cast .Usize native).val)) =
          (contents (ActualResponseBytesV1.ContentModel.take afterLength (UScalar.cast .Usize native).val)).map (fun byte => (255,0,0,byte)) := by
  obtain ⟨called,consumed,span,cacheAfter,boundaryAfter,header,headerEq,events⟩ := actual_body_iteration outer source state before middle afterLength native ctx budget remaining
    boundary cache positive physical fits keyRun lengthRun
  exact ⟨actual_response_step_next source _ before _ ctx limit (by rw [limitExact]; have := boundary.physical; omega) called,
    consumed,span,cacheAfter,boundaryAfter,header,headerEq,events⟩

#print axioms actual_body_loop_step

theorem actual_message_loop_step (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle afterLength : Slice U8)
    (native : U64) (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (limit : Usize)
    (limitExact : limit.val = before.length-remaining)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (physical : native.val ≤ afterLength.length)
    (fits : before.length-remaining ≤ (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val).length)
    (accepted : Utf8.accepts ((copiedString afterLength native).val.map (fun byte => byte.bv)) = true)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok ((3#u32),.LengthDelimited),middle))
    (lengthRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,afterLength)) :
    SubmessageV1.body ctx limit (source,before,()) =
      .ok (.cont ({source with message := some (copiedString afterLength native)},LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val,())) ∧
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val) ∧
      CacheAgrees outer {source with message := some (copiedString afterLength native)} (feed state consumed) ∧
      ChildAtKey (feed state consumed) (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val)
        (budget-consumed.length) (remaining-consumed.length) := by
  obtain ⟨called,consumed,span,cacheAfter,boundaryAfter⟩ := actual_message_iteration outer source state before middle afterLength native ctx budget remaining
    boundary cache positive physical fits accepted keyRun lengthRun
  exact ⟨actual_response_step_next source _ before _ ctx limit (by rw [limitExact]; have := boundary.physical; omega) called,
    consumed,span,cacheAfter,boundaryAfter⟩

#print axioms actual_message_loop_step

end ChatResponseReference.StreamingV1
