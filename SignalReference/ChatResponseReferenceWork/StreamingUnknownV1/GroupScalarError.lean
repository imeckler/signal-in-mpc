import ChatResponseReferenceWork.StreamingUnknownV1.GroupPendingKey
import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyEntry
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual group-loop malformed scalar child preserves exact native error/suffix
and derives full Core rejection, including keys exhausting/crossing the child. -/
theorem actual_group_varint_error (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8)
    (parent tag count : U32) (error : LoopSupportSkip.error.DecodeError) (parents : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining parents count)
    (cache : CacheAgrees outer source state) (depthBound : parents.length ≤ 98)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,.Varint),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Err error,after)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.done (.Err error,after)) ∧
    LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok (.Err error,after) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have countPositive : 1 < count.val := by have := ready.context; omega
  let child := U32.ofNatCore (count.val-1) (by have h := count.hmax; scalar_tac)
  have decremented : count.val = child.val+1 := by change count.val = (count.val-1)+1; omega
  have childPositive : child ≠ 0#u32 := by
    intro zero
    have numeric := congrArg UScalar.val zero
    change child.val = 0 at numeric
    omega
  have childRun := skip_varint_error middle after error tag child childPositive valueRun
  have step : LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.done (.Err error,after)) :=
    group_child_after before middle after parent tag ⟨count⟩ ⟨child⟩ .Varint (.Err error)
      (by intro same; cases same) keyRun (enter_recursion_value count child decremented) childRun
  refine ⟨step,group_loop_done _ _ _ _ step,?_⟩
  by_cases inside : before.length-remaining < middle.length
  · obtain ⟨keyConsumed,keySpan,keyData,keyValid,keyModes,keyPositions,keyValue,keyTag,keyKnown,keyKinds,keyInner,keyDepth,keyStack,keyBudget,keyRemaining,keySeen,keyFinished,keyUtf⟩ :=
      nested_native_nonfixed_key_entry state before middle tag .Varint parents.length budget remaining ready.common.budgetBound ready.common.remainingBound
        ready.common.budgetEnough ready.common.physical inside ready.modes ready.common.positions ready.common.shape.kinds ready.common.shape.utf
        ready.common.value ready.common.valid ready.common.seen ready.common.finished ready.common.inner ready.depth ready.common.budgetCounter ready.common.childCounter
        ready.positive depthBound (.inl rfl) keyRun
    have rejected := any_native_varint_error_reject (feed state keyConsumed) middle after error 1 (by decide)
      keyModes keyPositions keyValue (.inl (by decide)) valueRun
    rw [keySpan]
    simpa only [feed,List.foldl_append] using rejected
  · exact group_pending_key_not_inside_reject state before middle tag .Varint budget remaining parents count ready (.inl rfl) (by omega) keyRun

#print axioms actual_group_varint_error
end ChatResponseReference.StreamingUnknownV1
