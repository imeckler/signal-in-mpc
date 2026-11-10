import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthSource
import ChatResponseReferenceWork.StreamingUnknownV1.GroupPendingKey
import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyEntry
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthHeaderRoom
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthBoundary
import ChatResponseReferenceWork.StreamingUnknownV1.GroupOpaqueBoundary
import ChatResponseReferenceWork.StreamingV1.ChildLengthOverrun
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual length skip succeeds physically at/past the private child. Its real
source continuation/drop is preserved while Core rejects header overrun, empty
header exact-end, or the final payload byte leaving its group unclosed. -/
theorem actual_group_length_not_strict (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle after : Slice U8)
    (parent tag count : U32) (native : U64) (parents : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining parents count) (cache : CacheAgrees outer source state)
    (depthBound : parents.length ≤ 98) (physical : native.val ≤ after.length)
    (notStrict : ¬native.val+(before.length-after.length) < remaining)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,.LengthDelimited),middle))
    (valueRun : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok native,after)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.cont (drop after native.val)) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have step := actual_group_length_source_from_decode state before middle after parent tag count parents budget remaining (.Ok native) ready depthBound keyRun valueRun
  simp only [groupLengthNativeResult,fixedResult,if_neg (by omega : ¬after.length < native.val),groupChild] at step
  refine ⟨step,?_⟩
  by_cases inside : before.length-remaining < middle.length
  · obtain ⟨keyConsumed,keySpan,keyData,keyValid,keyModes,keyPositions,keyValue,keyTag,keyKnown,keyKinds,keyInner,keyDepth,keyStack,keyBudget,keyRemaining,keySeen,keyFinished,keyUtf⟩ :=
      nested_native_nonfixed_key_entry state before middle tag .LengthDelimited parents.length budget remaining ready.common.budgetBound ready.common.remainingBound
        ready.common.budgetEnough ready.common.physical inside ready.modes ready.common.positions ready.common.shape.kinds ready.common.shape.utf
        ready.common.value ready.common.valid ready.common.seen ready.common.finished ready.common.inner ready.depth ready.common.budgetCounter ready.common.childCounter
        ready.positive depthBound (.inr (.inl rfl)) keyRun
    have keyLength : before.length = keyConsumed.length+middle.length := by
      have result := congrArg List.length keySpan
      simpa only [contents,List.length_map,List.length_append] using result
    obtain ⟨leading,byte,tail,valueSpan,valueSuffix,_,_,_,_,_⟩ := native_success_span middle after native valueRun
    have tailLength : tail.length = after.length := by
      have result := congrArg List.length valueSuffix
      simpa only [contents,List.length_map] using result.symm
    have middleLength : middle.length = leading.length+1+after.length := by
      have result := congrArg List.length valueSpan
      simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
    have dropped : (drop after native.val).length = after.length-native.val := by change (after.val.drop native.val).length = _; rw [List.length_drop]
    simp only [wireNumber,if_neg (by decide : ¬(2:Nat) = 3)] at keyDepth keyStack
    have notTop := nested_depth_not_top (feed state keyConsumed) parents.length ready.positive (by omega) (keyDepth.trans ready.depth)
    have rejected : (TlsChatResponse.finish Word64.concrete ByteAuth.concrete
        (feed (feed state keyConsumed) (contents middle))).valid = 0 := by
      by_cases tooLarge : remaining < native.val+(before.length-after.length)
      · exact native_length_child_overrun_reject (feed state keyConsumed) middle after native (remaining-keyConsumed.length)
          (by have := ready.common.remainingBound; omega) (by have := ready.common.physical; omega) (by have := ready.common.physical; omega)
          physical (by change (drop after native.val).length < _; rw [dropped]; have := ready.common.physical; omega)
          keyModes keyPositions keyValue keyInner keyRemaining valueRun
      · have exactEnd : native.val+(before.length-after.length) = remaining := by omega
        by_cases empty : native.val = 0
        · exact native_group_length_at_child_end_reject (feed state keyConsumed) middle after native (remaining-keyConsumed.length)
            (by have := ready.common.remainingBound; omega) (by have := ready.common.physical; omega)
            keyModes keyPositions keyInner keyRemaining notTop valueRun
        · have keyShape := feed_shape state keyConsumed
            (show StateShape state from ⟨ready.common.shape.modes,ready.common.shape.positions,ready.common.shape.kinds,ready.common.shape.stack,ready.common.shape.utf⟩)
          have erasedShape : StateShape (eraseGroupDepth (feed state keyConsumed)) := ⟨keyShape.modes,keyShape.positions,keyShape.kinds,keyShape.stack,keyShape.utf⟩
          have fieldReady : ChildReady (eraseGroupDepth (feed state keyConsumed)) middle (budget-keyConsumed.length) (remaining-keyConsumed.length) :=
            ⟨⟨by have := ready.common.budgetBound; omega,by have := ready.common.remainingBound; omega,
              by have := ready.common.physical; omega,by have := ready.common.budgetEnough; omega,
              erasedShape,keyPositions,keyValue,keyValid,keySeen,keyFinished,rfl,keyBudget,keyRemaining⟩,
              by have := ready.common.physical; omega,keyInner⟩
          obtain ⟨header,headerSpan,headerCache,headerKinds,headerSkip,headerReady,headerMode,headerDepth,headerStack⟩ :=
            group_length_header_with_room outer source (feed state keyConsumed) middle after native (budget-keyConsumed.length) (remaining-keyConsumed.length)
              fieldReady (keyData.trans cache) (by omega) (by omega) keyModes keyKinds valueRun
          rw [if_neg empty] at headerMode
          have headerLength : middle.length = header.length+after.length := by
            have result := congrArg List.length headerSpan
            simpa only [contents,List.length_map,List.length_append] using result
          have headerCounter : (feed (feed state keyConsumed) header).responseRemaining = BitVec.ofNat 64 native.val := by
            have rawCounter : (feed (feed state keyConsumed) header).responseRemaining = BitVec.ofNat 64 (remaining-keyConsumed.length-header.length) := headerReady.childCounter
            rw [rawCounter]
            congr 1
            omega
          have nativeBound : native.val < 2^64 := native.bv.isLt
          have nativeBits : native.bv = BitVec.ofNat 64 native.val := by
            apply BitVec.eq_of_toNat_eq
            simp only [UScalar.bv_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt nativeBound]
          have headerNotTop : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (feed (feed state keyConsumed) header).depth 0 = 0 := by rw [headerDepth]; exact notTop
          have lastReject := group_opaque_at_child_end_reject (feed (feed state keyConsumed) header) after native.val
            (by have := ready.common.remainingBound; omega) (by omega) physical headerMode headerReady.inner headerCounter
            (headerSkip.trans nativeBits) headerNotTop
          rw [headerSpan]
          simpa only [feed,List.foldl_append] using lastReject
    rw [keySpan]
    simpa only [feed,List.foldl_append] using rejected
  · exact group_pending_key_not_inside_reject state before middle tag .LengthDelimited budget remaining parents count ready (.inr (.inr (.inl rfl))) (by omega) keyRun

#print axioms actual_group_length_not_strict
end ChatResponseReference.StreamingUnknownV1
