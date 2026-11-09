import ChatResponseReferenceWork.StreamingUnknownV1.FixedKeyReady
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Complete actual fixed32/fixed64 unknown-field callback. The real key derives
its own guarded opaque entry, exact private byte count and source suffix. -/
theorem actual_unknown_fixed_iteration (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (wide : Bool)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (fixedFits : (if wide then 8 else 4) + (before.length-middle.length) ≤ remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before =
      .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Ok (),(),source,drop middle (if wide then 8 else 4)) ∧
    ∃ consumed,
      contents before = consumed ++ contents (drop middle (if wide then 8 else 4)) ∧
      CacheAgrees outer source (feed state consumed) ∧
      ChildAtKey (feed state consumed) (drop middle (if wide then 8 else 4))
        (budget-consumed.length) (remaining-consumed.length) := by
  obtain ⟨keyConsumed,keySpan,keyCache,keyReady,keyModes,keyKinds,keySkip,countFits⟩ :=
    actual_unknown_fixed_key_ready outer source state before middle tag budget remaining wide boundary cache positive unknownTag fixedFits keyRun
  obtain ⟨fieldRun,fieldConsumed,fieldBytes,fieldSpan,fieldCache,fieldBoundary⟩ := actual_unknown_fixed_resumes outer source tag
    (feed state keyConsumed) middle ctx (budget-keyConsumed.length) (remaining-keyConsumed.length) wide unknownTag count
    keyReady keyCache countFits keyModes keyKinds keySkip
  refine ⟨actual_response_callback source source before middle _ tag _ ctx (.Ok ()) keyRun fieldRun,
    keyConsumed++fieldConsumed,?_,?_,?_⟩
  · rw [keySpan,fieldSpan,List.append_assoc]
  · simpa only [feed,List.foldl_append] using fieldCache
  · have length : fieldConsumed.length = (if wide then 8 else 4) := by
      rw [fieldBytes,List.length_take]
      have inputLength : (contents middle).length = middle.length := by simp only [contents,List.length_map]
      rw [inputLength,Nat.min_eq_left (by have := keyReady.physical; omega)]
    simpa only [feed,List.foldl_append,List.length_append,Nat.sub_sub,length] using fieldBoundary

theorem actual_unknown_fixed_loop_step (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (wide : Bool)
    (limit : Usize) (limitExact : limit.val = before.length-remaining)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (fixedFits : (if wide then 8 else 4) + (before.length-middle.length) ≤ remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before =
      .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    SubmessageV1.body ctx limit (source,before,()) = .ok (.cont (source,drop middle (if wide then 8 else 4),())) ∧
    ∃ consumed,
      contents before = consumed ++ contents (drop middle (if wide then 8 else 4)) ∧
      CacheAgrees outer source (feed state consumed) ∧
      ChildAtKey (feed state consumed) (drop middle (if wide then 8 else 4))
        (budget-consumed.length) (remaining-consumed.length) := by
  obtain ⟨called,consumed,span,cacheAfter,boundaryAfter⟩ := actual_unknown_fixed_iteration outer source tag state before middle ctx budget remaining wide
    unknownTag count boundary cache positive fixedFits keyRun
  exact ⟨actual_response_step_next source source before _ ctx limit (by rw [limitExact]; have := boundary.physical; omega) called,
    consumed,span,cacheAfter,boundaryAfter⟩

#print axioms actual_unknown_fixed_iteration
#print axioms actual_unknown_fixed_loop_step
end ChatResponseReference.StreamingUnknownV1
