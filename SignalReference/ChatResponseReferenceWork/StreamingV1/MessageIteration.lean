import ChatResponseReferenceWork.StreamingV1.BodyIteration
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Complete actual accepted message String callback derives key/field entry
and preserves the source/cache/next-key invariant with exact copied content. -/
theorem actual_message_iteration (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle afterLength : Slice U8)
    (native : U64) (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (physical : native.val ≤ afterLength.length)
    (fits : before.length-remaining ≤ (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val).length)
    (accepted : Utf8.accepts ((copiedString afterLength native).val.map (fun byte => byte.bv)) = true)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok ((3#u32),.LengthDelimited),middle))
    (lengthRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,afterLength)) :
    SubmessageV1.callback.call_mut () (source,before,ctx) =
      .ok (.Ok (),(),{source with message := some (copiedString afterLength native)},
        LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val) ∧
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val) ∧
      CacheAgrees outer {source with message := some (copiedString afterLength native)} (feed state consumed) ∧
      ChildAtKey (feed state consumed) (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val)
        (budget-consumed.length) (remaining-consumed.length) := by
  obtain ⟨leading,byte,tail,span,suffix,_,_,_,_,_⟩ := native_success_span middle afterLength native lengthRun
  have lengthStrict : afterLength.length < middle.length := by
    have inputLength := congrArg List.length span
    have tailLength := congrArg List.length suffix
    simp only [contents,List.length_map,List.length_append,List.length_cons] at inputLength tailLength
    change middle.length = leading.length+(tail.length+1) at inputLength
    change afterLength.length = tail.length at tailLength
    omega
  have droppedLength : (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val).length = afterLength.length-native.val := by
    change (afterLength.val.drop native.val).length = _
    rw [List.length_drop]
  obtain ⟨keyConsumed,keySpan,keyCache,keyReady,keyModes,keyTag,keyKnown,keyKinds⟩ :=
    actual_known_key_cache_ready outer source state before middle (3#u32) .LengthDelimited budget remaining boundary cache positive
      (by rw [droppedLength] at fits; omega) (.inr ⟨.inl rfl,rfl⟩) keyRun
  have keyLength : before.length = keyConsumed.length+middle.length := by
    have result := congrArg List.length keySpan
    simpa only [contents,List.length_map,List.length_append] using result
  have modes : (feed state keyConsumed).modes = lane 2 := keyModes
  have kinds : (feed state keyConsumed).kinds = [0,0,255,0] := keyKinds
  obtain ⟨fieldResult,fieldConsumed,fieldSpan,fieldCache,fieldBoundary⟩ :=
    actual_message_cache_resumes outer source (feed state keyConsumed) middle afterLength native ctx (budget-keyConsumed.length) (remaining-keyConsumed.length)
      keyReady keyCache physical (by rw [droppedLength] at fits; have := keyReady.positive; omega) modes kinds accepted lengthRun
  refine ⟨actual_response_callback source _ before middle _ (3#u32) .LengthDelimited ctx (.Ok ()) keyRun fieldResult,
    keyConsumed++fieldConsumed,?_,?_,?_⟩
  · rw [keySpan,fieldSpan,List.append_assoc]
  · simpa only [feed,List.foldl_append] using fieldCache
  · simpa only [feed,List.foldl_append,List.length_append,Nat.sub_sub] using fieldBoundary
#print axioms actual_message_iteration
end ChatResponseReference.StreamingV1
