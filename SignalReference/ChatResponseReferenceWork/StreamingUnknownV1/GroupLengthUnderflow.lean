import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthSource
import ChatResponseReferenceWork.StreamingUnknownV1.GroupPendingKey
import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyEntry
import ChatResponseReferenceWork.StreamingUnknownV1.LengthTransition
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual length payload underflow exits the group at its unadvanced post-header
suffix. Numeric rejection is derived independently of real group depth; source
cursor is not equated to any later processed physical bytes. -/
theorem actual_group_length_underflow (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before middle after : Slice U8) (parent tag count : U32) (native : U64) (parents : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining parents count) (depthBound : parents.length ≤ 98)
    (underflow : after.length < native.val)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.done (.Err (decodeError .BufferUnderflow),after)) ∧
    LoopSupportSkip.encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok (.Err (decodeError .BufferUnderflow),after) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have step := actual_group_length_source_from_decode state before middle after parent tag count parents budget remaining (.Ok native) ready depthBound keyRun valueRun
  simp only [groupLengthNativeResult,fixedResult,if_pos underflow,groupChild] at step
  refine ⟨step,group_loop_done _ _ _ _ step,?_⟩
  by_cases inside : before.length-remaining < middle.length
  · obtain ⟨keyConsumed,keySpan,keyData,keyValid,keyModes,keyPositions,keyValue,keyTag,keyKnown,keyKinds,keyInner,keyDepth,keyStack,keyBudget,keyRemaining,keySeen,keyFinished,keyUtf⟩ :=
      nested_native_nonfixed_key_entry state before middle tag .LengthDelimited parents.length budget remaining ready.common.budgetBound ready.common.remainingBound
        ready.common.budgetEnough ready.common.physical inside ready.modes ready.common.positions ready.common.shape.kinds ready.common.shape.utf
        ready.common.value ready.common.valid ready.common.seen ready.common.finished ready.common.inner ready.depth ready.common.budgetCounter ready.common.childCounter
        ready.positive depthBound (.inr (.inl rfl)) keyRun
    have rejected := native_unknown_length_underflow_reject (feed state keyConsumed) middle after native keyModes keyPositions keyValue keyKinds underflow valueRun
    rw [keySpan]
    simpa only [feed,List.foldl_append] using rejected
  · exact group_pending_key_not_inside_reject state before middle tag .LengthDelimited budget remaining parents count ready (.inr (.inr (.inl rfl))) (by omega) keyRun

#print axioms actual_group_length_underflow
end ChatResponseReference.StreamingUnknownV1
