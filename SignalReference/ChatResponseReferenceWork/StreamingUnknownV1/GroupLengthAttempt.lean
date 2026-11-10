import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthIteration
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthError
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthUnderflow
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthNotStrict
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Exhaustive actual inner-group length child attempt. Native header termination/
result, physical and private fit are derived; exact actual error/loop exit or
source continuation/native suffix is retained with full numeric continuation or
rejection, including empty fields ending at the real child boundary. -/
theorem actual_group_length_attempt_all (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (parent tag count : U32) (parents : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining parents count)
    (cache : CacheAgrees outer source state) (depthBound : parents.length ≤ 98)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle)) :
    ∃ decoded after,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (decoded,after) ∧
      PrefixPost middle decoded after ∧ ErrorPost middle decoded after ∧
      LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before =
        .ok (groupChild (groupLengthNativeResult decoded after).1 (groupLengthNativeResult decoded after).2) ∧
      match decoded with
      | .Err error =>
        LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok (.Err error,after) ∧
        (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
      | .Ok native =>
        if native.val ≤ after.length then
          if native.val+(before.length-after.length) < remaining then
            ∃ consumed,
              contents before = consumed ++ contents (drop after native.val) ∧ CacheAgrees outer source (feed state consumed) ∧
              GroupLoopReady (feed state consumed) (drop after native.val) (budget-consumed.length) (remaining-consumed.length) parents count
          else (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
        else
          LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok (.Err (decodeError .BufferUnderflow),after) ∧
          (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨decoded,after,actual,prefixPost,errorPost⟩ := decode_full_reference middle
  refine ⟨decoded,after,actual,prefixPost,errorPost,actual_group_length_source_from_decode state before middle after parent tag count parents budget remaining decoded ready depthBound keyRun actual,?_⟩
  cases decoded with
  | Err error => exact (actual_group_length_error outer source state before middle after parent tag count error parents budget remaining ready cache depthBound keyRun actual).2
  | Ok native =>
    dsimp only
    by_cases physical : native.val ≤ after.length
    · rw [if_pos physical]
      by_cases fits : native.val+(before.length-after.length) < remaining
      · rw [if_pos fits]
        exact (actual_group_length_loop_step outer source state before middle after parent tag count native parents budget remaining ready cache depthBound fits keyRun actual).2
      · rw [if_neg fits]
        exact (actual_group_length_not_strict outer source state before middle after parent tag count native parents budget remaining ready cache depthBound physical fits keyRun actual).2
    · rw [if_neg physical]
      exact (actual_group_length_underflow state before middle after parent tag count native parents budget remaining ready depthBound (by omega) keyRun actual).2

#print axioms actual_group_length_attempt_all
end ChatResponseReference.StreamingUnknownV1
