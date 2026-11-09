import ChatResponseReferenceWork.StreamingUnknownV1.LengthResume
import ChatResponseReferenceWork.StreamingUnknownV1.LengthKeyReady
import ChatResponseReferenceWork.StreamingUnknownV1.FixedErrors
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual unknown length-delimited key/length/payload callback, including empty
payloads. Real decoders derive numeric key and length entry; arbitrary payload
bytes are ignored while exact private counters/cache resume at the next key. -/
theorem actual_unknown_length_iteration (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8) (native : U64)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (unknown : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (fits : native.val + (before.length-after.length) ≤ remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (lengthRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    SubmessageV1.callback.call_mut () (source,before,ctx) = .ok (.Ok (),(),source,drop after native.val) ∧
    ∃ consumed,
      contents before = consumed ++ contents (drop after native.val) ∧
      CacheAgrees outer source (feed state consumed) ∧
      ChildAtKey (feed state consumed) (drop after native.val) (budget-consumed.length) (remaining-consumed.length) := by
  have keyDecrease := actual_key_success_decreases before middle tag .LengthDelimited keyRun
  obtain ⟨leading,byte,tail,lengthSpan,lengthSuffix,_,_,_,_,_⟩ := native_success_span middle after native lengthRun
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length lengthSuffix
    simpa only [contents,List.length_map] using result.symm
  have middleLength : middle.length = leading.length+1+after.length := by
    have result := congrArg List.length lengthSpan
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  have keyFits : before.length-remaining < middle.length := by omega
  obtain ⟨keyConsumed,keySpan,keyCache,keyReady,keyModes,keyKnown,keyKinds⟩ :=
    actual_unknown_length_key_ready outer source state before middle tag budget remaining boundary cache positive keyFits unknown keyRun
  have keyLength : before.length = keyConsumed.length+middle.length := by
    have result := congrArg List.length keySpan
    simpa only [contents,List.length_map,List.length_append] using result
  have fieldFits : native.val + (middle.length-after.length) ≤ remaining-keyConsumed.length := by omega
  obtain ⟨fieldRun,fieldConsumed,fieldSpan,fieldCache,fieldBoundary⟩ :=
    actual_unknown_length_resumes outer source tag ctx (feed state keyConsumed) middle after native
      (budget-keyConsumed.length) (remaining-keyConsumed.length) keyReady keyCache unknown count fieldFits keyModes keyKinds lengthRun
  refine ⟨actual_response_callback source source before middle _ tag .LengthDelimited ctx (.Ok ()) keyRun fieldRun,
    keyConsumed++fieldConsumed,?_,?_,?_⟩
  · rw [keySpan,fieldSpan,List.append_assoc]
  · simpa only [feed,List.foldl_append] using fieldCache
  · simpa only [feed,List.foldl_append,List.length_append,Nat.sub_sub] using fieldBoundary

theorem actual_unknown_length_loop_step (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8) (native : U64)
    (ctx : ActualSubmessageV1.prost.encoding.DecodeContext) (budget remaining : Nat)
    (limit : Usize) (limitExact : limit.val = before.length-remaining)
    (unknown : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (boundary : ChildAtKey state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < remaining) (fits : native.val + (before.length-after.length) ≤ remaining)
    (keyRun : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (lengthRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    SubmessageV1.body ctx limit (source,before,()) = .ok (.cont (source,drop after native.val,())) ∧
    ∃ consumed,
      contents before = consumed ++ contents (drop after native.val) ∧
      CacheAgrees outer source (feed state consumed) ∧
      ChildAtKey (feed state consumed) (drop after native.val) (budget-consumed.length) (remaining-consumed.length) := by
  obtain ⟨called,consumed,span,cacheAfter,boundaryAfter⟩ := actual_unknown_length_iteration outer source tag state before middle after native ctx budget remaining
    unknown count boundary cache positive fits keyRun lengthRun
  exact ⟨actual_response_step_next source source before _ ctx limit (by rw [limitExact]; have := boundary.physical; omega) called,
    consumed,span,cacheAfter,boundaryAfter⟩

#print axioms actual_unknown_length_iteration
#print axioms actual_unknown_length_loop_step
end ChatResponseReference.StreamingUnknownV1
