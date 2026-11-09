import ChatResponseReferenceWork.StreamingV1.ResponseCallback
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- One complete actual source callback (key plus ID/status payload) agrees with
the streaming loop/cache invariant. Field entry and key-private bounds derive
from native calls and final field fit, rather than a post-key assumption. -/
theorem actual_scalar_iteration (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8)
    (native : U64) (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (isStatus : Bool)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (fits : before.length-remaining ≤ after.length)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before =
      .ok (.Ok ((if isStatus then (2#u32) else (1#u32)),.Varint),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    SubmessageV1.callback.call_mut () (source,before,ctx) =
      .ok (.Ok (),(),if isStatus then {source with status := some (UScalar.cast .U32 native)} else {source with id := some native},after) ∧
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      CacheAgrees outer (if isStatus then {source with status := some (UScalar.cast .U32 native)} else {source with id := some native}) (feed state consumed) ∧
      ChildAtKey (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) := by
  let sourceTag : U32 := if isStatus then (2#u32) else (1#u32)
  obtain ⟨leading,byte,tail,span,suffix,_,_,_,_,_⟩ := native_success_span middle after native valueRun
  have valueStrict : after.length < middle.length := by
    have inputLength := congrArg List.length span
    have tailLength := congrArg List.length suffix
    simp only [contents,List.length_map,List.length_append,List.length_cons] at inputLength tailLength
    change middle.length = leading.length + (tail.length+1) at inputLength
    change after.length = tail.length at tailLength
    omega
  have supported : (sourceTag.val = 1 ∨ sourceTag.val = 2) ∧
      (ActualInnerScanV1.prost.encoding.wire_type.WireType.Varint) = .Varint ∨
      (sourceTag.val = 3 ∨ sourceTag.val = 4 ∨ sourceTag.val = 5) ∧
        (ActualInnerScanV1.prost.encoding.wire_type.WireType.Varint) = .LengthDelimited := by
    apply Or.inl
    refine ⟨?_,rfl⟩
    cases isStatus <;> first | exact .inl rfl | exact .inr rfl
  obtain ⟨keyConsumed,keySpan,keyCache,keyReady,keyModes,keyTag,keyKnown,keyKinds⟩ :=
    actual_known_key_cache_ready outer source state before middle sourceTag .Varint budget remaining boundary cache positive (by omega) supported keyRun
  have keyLength : before.length = keyConsumed.length+middle.length := by
    have result := congrArg List.length keySpan
    simpa only [contents,List.length_map,List.length_append] using result
  have modes : (feed state keyConsumed).modes = lane 1 := keyModes
  have known : (feed state keyConsumed).scalarKnown = 255 := by
    rw [keyKnown]
    cases isStatus <;> rfl
  have tag : (feed state keyConsumed).tag = if isStatus then 2 else 1 := by
    rw [keyTag]
    cases isStatus <;> rfl
  obtain ⟨fieldResult,fieldConsumed,fieldSpan,fieldCache,fieldBoundary⟩ :=
    actual_scalar_cache_resumes outer source (feed state keyConsumed) middle after native ctx (budget-keyConsumed.length) (remaining-keyConsumed.length)
      isStatus keyReady keyCache (by have := keyReady.positive; omega) modes known tag valueRun
  have fieldRun : ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source sourceTag .Varint middle ctx =
      .ok (.Ok (),if isStatus then {source with status := some (UScalar.cast .U32 native)} else {source with id := some native},after) := by
    cases isStatus <;> exact fieldResult
  refine ⟨actual_response_callback source _ before middle after sourceTag .Varint ctx (.Ok ()) keyRun fieldRun,keyConsumed++fieldConsumed,?_,?_,?_⟩
  · rw [keySpan,fieldSpan,List.append_assoc]
  · simpa only [feed,List.foldl_append] using fieldCache
  · simpa only [feed,List.foldl_append,List.length_append,Nat.sub_sub] using fieldBoundary

#print axioms actual_scalar_iteration
end ChatResponseReference.StreamingV1
