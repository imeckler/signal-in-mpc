import ChatResponseReferenceWork.StreamingUnknownV1.KeyReady
import ChatResponseReferenceWork.StreamingV1.MessageErrorLoop
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- A complete actual unknown-varint callback derives its own key/field entry,
exact consumed prefix, untouched source/cache and full next bounded loop state. -/
theorem actual_unknown_varint_iteration (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8) (native : U64)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (fits : before.length-remaining ≤ after.length)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.Varint),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Ok (),(),source,after) ∧
    ∃ consumed,
      contents before = consumed ++ contents after ∧ CacheAgrees outer source (feed state consumed) ∧
      ChildAtKey (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) := by
  obtain ⟨leading,byte,tail,span,suffix,_,_,_,_,_⟩ := native_success_span middle after native valueRun
  have valueStrict : after.length < middle.length := by
    have inputLength := congrArg List.length span
    have tailLength := congrArg List.length suffix
    simp only [contents,List.length_map,List.length_append,List.length_cons] at inputLength tailLength
    change middle.length = leading.length+(tail.length+1) at inputLength
    change after.length = tail.length at tailLength
    omega
  obtain ⟨keyConsumed,keySpan,keyCache,keyReady,keyModes,keyUnknown,keyKinds⟩ :=
    actual_unknown_varint_key_ready outer source state before middle tag budget remaining boundary cache positive (by omega) unknownTag keyRun
  have keyLength : before.length = keyConsumed.length+middle.length := by
    have result := congrArg List.length keySpan
    simpa only [contents,List.length_map,List.length_append] using result
  obtain ⟨fieldRun,fieldConsumed,fieldSpan,fieldCache,fieldBoundary⟩ := unknown_varint_resumes outer source tag
    (feed state keyConsumed) middle after native ctx (budget-keyConsumed.length) (remaining-keyConsumed.length)
    unknownTag count keyReady keyCache (by have := keyReady.positive; omega) keyModes keyUnknown valueRun
  refine ⟨actual_response_callback source source before middle after tag .Varint ctx (.Ok ()) keyRun fieldRun,
    keyConsumed++fieldConsumed,?_,?_,?_⟩
  · rw [keySpan,fieldSpan,List.append_assoc]
  · simpa only [feed,List.foldl_append] using fieldCache
  · simpa only [feed,List.foldl_append,List.length_append,Nat.sub_sub] using fieldBoundary

theorem actual_unknown_varint_loop_step (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8) (native : U64)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat) (limit : Usize)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (limitExact : limit.val = before.length-remaining)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (fits : before.length-remaining ≤ after.length)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.Varint),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    SubmessageV1.body ctx limit (source,before,()) = .ok (.cont (source,after,())) ∧
    ∃ consumed,
      contents before = consumed ++ contents after ∧ CacheAgrees outer source (feed state consumed) ∧
      ChildAtKey (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) := by
  obtain ⟨called,consumed,span,cacheAfter,boundaryAfter⟩ := actual_unknown_varint_iteration outer source tag state before middle after native ctx budget remaining
    unknownTag count boundary cache positive fits keyRun valueRun
  exact ⟨actual_response_step_next source source before after ctx limit (by rw [limitExact]; have := boundary.physical; omega) called,
    consumed,span,cacheAfter,boundaryAfter⟩

#print axioms actual_unknown_varint_iteration
#print axioms actual_unknown_varint_loop_step
end ChatResponseReference.StreamingUnknownV1
