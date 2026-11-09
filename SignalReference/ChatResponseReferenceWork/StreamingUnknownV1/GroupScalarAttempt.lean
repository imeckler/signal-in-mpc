import ChatResponseReferenceWork.StreamingUnknownV1.GroupScalarIteration
import ChatResponseReferenceWork.StreamingUnknownV1.GroupScalarOverrun
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Exhaustive actual group varint child attempt after its real key. Primitive
termination/outcome and private field fit are derived. Native errors preserve
exact error/suffix and source group-loop exit; physical source continuation at
or beyond the private boundary is retained separately from Core rejection. -/
theorem actual_group_varint_attempt_all (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (parent tag count : U32) (parents : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining parents count)
    (cache : CacheAgrees outer source state) (depthBound : parents.length ≤ 98)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,.Varint),middle)) :
    ∃ decoded after,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (decoded,after) ∧
      PrefixPost middle decoded after ∧ ErrorPost middle decoded after ∧
      match decoded with
      | .Err error =>
        LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.done (.Err error,after)) ∧
        LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok (.Err error,after) ∧
        (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
      | .Ok _ =>
        LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.cont after) ∧
        if before.length-after.length < remaining then
          ∃ consumed,
            contents before = consumed ++ contents after ∧ CacheAgrees outer source (feed state consumed) ∧
            GroupLoopReady (feed state consumed) after (budget-consumed.length) (remaining-consumed.length) parents count
        else
          (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨decoded,after,actual,prefixPost,errorPost⟩ := decode_full_reference middle
  refine ⟨decoded,after,actual,prefixPost,errorPost,?_⟩
  cases decoded with
  | Err error => exact actual_group_varint_error outer source state before middle after parent tag count error parents budget remaining ready cache depthBound keyRun actual
  | Ok native =>
    by_cases fits : before.length-after.length < remaining
    · obtain ⟨step,complete⟩ := actual_group_varint_loop_step outer source state before middle after parent tag count native parents budget remaining ready cache depthBound fits keyRun actual
      exact ⟨step,by simpa only [if_pos fits] using complete⟩
    · obtain ⟨step,rejected⟩ := actual_group_varint_not_fit outer source state before middle after parent tag count native parents budget remaining ready cache depthBound
        (by have := ready.common.physical; have := ready.common.positive; omega) keyRun actual
      exact ⟨step,by simpa only [if_neg fits] using rejected⟩

#print axioms actual_group_varint_attempt_all
end ChatResponseReference.StreamingUnknownV1
