import ChatResponseReferenceWork.StreamingUnknownV1.GroupScalarError
import ChatResponseReferenceWork.StreamingUnknownV1.GroupScalarBoundary
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual source group body may continue after a scalar exhausting or crossing
the private child. Core already rejects because the group has no in-child end.
The source continuation/suffix is retained, not replaced by an invented error. -/
theorem actual_group_varint_not_fit (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8)
    (parent tag count : U32) (native : U64) (parents : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining parents count)
    (cache : CacheAgrees outer source state) (depthBound : parents.length ≤ 98)
    (notFit : after.length ≤ before.length-remaining)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,.Varint),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.cont after) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have countPositive : 1 < count.val := by have := ready.context; omega
  let child := U32.ofNatCore (count.val-1) (by have h := count.hmax; scalar_tac)
  have decremented : count.val = child.val+1 := by change count.val = (count.val-1)+1; omega
  have childPositive : child ≠ 0#u32 := by
    intro zero
    have numeric := congrArg UScalar.val zero
    change child.val = 0 at numeric
    omega
  have childRun := skip_varint_after middle after native tag child childPositive valueRun
  have step : LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.cont after) :=
    group_child_after before middle after parent tag ⟨count⟩ ⟨child⟩ .Varint (.Ok ())
      (by intro same; cases same) keyRun (enter_recursion_value count child decremented) childRun
  refine ⟨step,?_⟩
  by_cases inside : before.length-remaining < middle.length
  · obtain ⟨keyConsumed,keySpan,keyData,keyValid,keyModes,keyPositions,keyValue,keyTag,keyKnown,keyKinds,keyInner,keyDepth,keyStack,keyBudget,keyRemaining,keySeen,keyFinished,keyUtf⟩ :=
      nested_native_nonfixed_key_entry state before middle tag .Varint parents.length budget remaining ready.common.budgetBound ready.common.remainingBound
        ready.common.budgetEnough ready.common.physical inside ready.modes ready.common.positions ready.common.shape.kinds ready.common.shape.utf
        ready.common.value ready.common.valid ready.common.seen ready.common.finished ready.common.inner ready.depth ready.common.budgetCounter ready.common.childCounter
        ready.positive depthBound (.inl rfl) keyRun
    have keyLength : before.length = keyConsumed.length+middle.length := by
      have result := congrArg List.length keySpan
      simpa only [contents,List.length_map,List.length_append] using result
    have rejected : (TlsChatResponse.finish Word64.concrete ByteAuth.concrete
        (feed (feed state keyConsumed) (contents middle))).valid = 0 := by
      by_cases past : after.length < before.length-remaining
      · exact native_varint_child_overrun_reject (feed state keyConsumed) middle after native (remaining-keyConsumed.length) 1 (by decide)
          (by have := ready.common.remainingBound; omega) (by have := ready.common.physical; omega)
          (by have := ready.common.physical; omega) (by have := ready.common.physical; omega) keyModes keyInner keyRemaining valueRun
      · simp only [wireNumber,if_neg (by decide : ¬(0:Nat) = 3)] at keyDepth
        have notTop := nested_depth_not_top (feed state keyConsumed) parents.length ready.positive (by omega) (keyDepth.trans ready.depth)
        exact native_group_scalar_at_child_end_reject (feed state keyConsumed) middle after native (remaining-keyConsumed.length)
          (by have := ready.common.remainingBound; omega) (by have := ready.common.physical; omega)
          keyModes keyPositions keyInner keyRemaining notTop valueRun
    rw [keySpan]
    simpa only [feed,List.foldl_append] using rejected
  · exact group_pending_key_not_inside_reject state before middle tag .Varint budget remaining parents count ready (.inl rfl) (by omega) keyRun

#print axioms actual_group_varint_not_fit
end ChatResponseReference.StreamingUnknownV1
