import ChatResponseReferenceWork.StreamingV1.InvalidMessageError
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open ActualInnerResponseV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual invalid-UTF8 key+String callback returns its exact cleared record,
error kind/diagnostic stack/suffix; actual streaming parser rejects full input. -/
theorem actual_message_invalid_iteration (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle afterLength : Slice U8)
    (native : U64) (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (physical : native.val ≤ afterLength.length)
    (fits : before.length-remaining ≤ (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val).length)
    (accepted : Utf8.accepts ((copiedString afterLength native).val.map (fun byte => byte.bv)) = false)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok ((3#u32),.LengthDelimited),middle))
    (lengthRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,afterLength)) :
    ∃ error,
      SubmessageV1.callback.call_mut () (source,before,ctx) =
        .ok (.Err error,(),{source with message := some (alloc.vec.Vec.new U8)},LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val) ∧
      error.inner.description = invalidMessageError.inner.description ∧ error.inner.stack.val = [diagnosticFrame2] ∧
      (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
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
  obtain ⟨fieldResult,fieldConsumed,fieldSpan,fieldValid⟩ := actual_message_field_agreement source ctx (feed state keyConsumed) middle afterLength native
    (budget-keyConsumed.length) (remaining-keyConsumed.length) keyReady.budgetBound keyReady.remainingBound keyReady.budgetEnough keyReady.physical
    physical (by rw [droppedLength] at fits; have := keyReady.positive; omega) modes keyReady.positions keyReady.shape.utf keyReady.value kinds
    keyReady.valid keyReady.seen keyReady.finished keyReady.inner keyReady.depth keyReady.budgetCounter keyReady.childCounter lengthRun
  simp only [messageFieldOutcome,accepted,Bool.false_eq_true,if_false] at fieldResult
  change ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (3#u32) .LengthDelimited middle ctx =
    (do let observed ← InnerResponseV1.stamp diagnosticFrame2 (.Err invalidMessageError)
        .ok (observed,{source with message := some (alloc.vec.Vec.new U8)},LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val)) at fieldResult
  obtain ⟨error,stampRun,errorKind,errorStack⟩ := invalid_message_stamp
  rw [stampRun] at fieldResult
  simp only [bind_tc_ok] at fieldResult
  rw [accepted] at fieldValid
  have fullSpan : contents before = (keyConsumed++fieldConsumed) ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val) := by
    rw [keySpan,fieldSpan,List.append_assoc]
  have invalid : (feed state (keyConsumed++fieldConsumed)).valid = 0 := by
    simpa only [feed,List.foldl_append,Bool.false_eq_true,if_false] using fieldValid
  refine ⟨error,actual_response_callback source _ before middle _ (3#u32) .LengthDelimited ctx (.Err error) keyRun fieldResult,errorKind,errorStack,?_⟩
  rw [fullSpan]
  apply finish_invalid_sticky
  simpa only [feed,List.foldl_append] using feed_invalid_sticky (feed state (keyConsumed++fieldConsumed))
    (contents (LibSignalReference.Candidate.ProstBytesBuf.drop afterLength native.val)) invalid

#print axioms actual_message_invalid_iteration
end ChatResponseReference.StreamingV1
