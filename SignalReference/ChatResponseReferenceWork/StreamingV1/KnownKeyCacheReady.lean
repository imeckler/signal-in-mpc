import ChatResponseReferenceWork.StreamingV1.BodyCacheResume
import ChatResponseReferenceWork.StreamingV1.MessageCacheResume
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipSlice

theorem actual_known_key_cache_ready (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : ActualInnerScanV1.prost.encoding.wire_type.WireType)
    (budget remaining : Nat) (boundary : ChildAtKey state before budget remaining)
    (cache : CacheAgrees outer source state) (positive : 0 < remaining) (fits : before.length-remaining < after.length)
    (known : (tag.val = 1 ∨ tag.val = 2) ∧ wire = .Varint ∨
      (tag.val = 3 ∨ tag.val = 4 ∨ tag.val = 5) ∧ wire = .LengthDelimited)
    (sourceSuccess : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,wire),after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      CacheAgrees outer source (feed state consumed) ∧
      ChildReady (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) ∧
      (feed state consumed).modes = lane (wireLane (wireNumber (ActualInnerResponseV1.toSkipWire wire))) ∧
      (feed state consumed).tag = BitVec.ofNat 64 tag.val ∧
      (feed state consumed).scalarKnown = (if tag.val = 1 ∨ tag.val = 2 then 255 else 0) ∧
      (feed state consumed).kinds = [0,if tag.val = 4 then 255 else 0,if tag.val = 3 then 255 else 0,if tag.val = 5 then 255 else 0] := by
  obtain ⟨consumed,span,data,ready,nextModes,nextTag,nextKnown,nextKinds⟩ := actual_known_key_ready state before after tag wire budget remaining boundary positive fits known sourceSuccess
  exact ⟨consumed,span,data.trans cache,ready,nextModes,nextTag,nextKnown,nextKinds⟩

#print axioms actual_known_key_cache_ready
end ChatResponseReference.StreamingV1
