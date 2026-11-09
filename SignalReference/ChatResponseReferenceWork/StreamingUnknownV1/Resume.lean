import ChatResponseReferenceWork.StreamingUnknownV1.Data
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Actual generated unknown-varint field resumes the full bounded inner scan,
with every source field unchanged and exact private counters/native suffix. -/
theorem unknown_varint_resumes (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (ready : ChildReady state before budget remaining) (cache : CacheAgrees outer source state)
    (fits : before.length-remaining ≤ after.length) (modes : state.modes = lane 1) (unknown : state.scalarKnown = 0)
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag .Varint before ctx =
      .ok (.Ok (),source,after) ∧
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      CacheAgrees outer source (feed state consumed) ∧
      ChildAtKey (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) := by
  have sourceResult := unknown_varint_from_decode source tag before after ctx unknownTag count (.Ok native) actual
  obtain ⟨consumed,span,data,nextModes,nextPositions,nextValue⟩ :=
    unknown_scalar_native_data state before after native remaining ready.remainingBound ready.physical fits
      modes ready.positions ready.inner ready.childCounter unknown actual
  obtain ⟨validConsumed,validSpan,nextValid⟩ := native_scalar_success_valid state before after native budget remaining
    ready.budgetBound ready.remainingBound ready.budgetEnough ready.physical fits modes ready.positions ready.valid
    ready.seen ready.finished ready.inner ready.depth ready.budgetCounter ready.childCounter actual
  have validUnique := consumed_prefix_unique _ _ _ _ validSpan span
  subst validConsumed
  obtain ⟨scopeConsumed,scopeSpan,nextRemaining,nextInner,nextDepth⟩ := native_scalar_scope state before after native remaining
    ready.remainingBound ready.physical fits modes ready.positions ready.inner ready.childCounter actual
  have scopeUnique := consumed_prefix_unique _ _ _ _ scopeSpan span
  subst scopeConsumed
  have inputLength : consumed.length+after.length = before.length := by
    have result := consumed_prefix_length _ _ _ span
    simpa only [contents,List.length_map] using result
  refine ⟨sourceResult,consumed,span,?_,?_⟩
  · exact data.trans cache
  · exact child_boundary_after state before after budget remaining ready consumed span (by have := ready.physical; omega)
      nextPositions nextValue nextValid nextModes nextDepth nextRemaining nextInner

#print axioms unknown_varint_resumes
end ChatResponseReference.StreamingUnknownV1
