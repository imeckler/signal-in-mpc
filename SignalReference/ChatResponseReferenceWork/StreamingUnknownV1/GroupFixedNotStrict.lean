import ChatResponseReferenceWork.StreamingUnknownV1.GroupFixedSource
import ChatResponseReferenceWork.StreamingUnknownV1.GroupFixedNoFit
import ChatResponseReferenceWork.StreamingUnknownV1.GroupFixedKeyEntry
import ChatResponseReferenceWork.StreamingUnknownV1.GroupOpaqueBoundary
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Actual fixed source skip can succeed at/past the private child. Source body
continuation and native drop are retained while Core rejects either its actual
fixed-length guard or the final payload byte leaving its group unclosed. -/
theorem actual_group_fixed_not_strict (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before middle : Slice U8) (parent tag count : U32) (parents : List U32) (budget remaining : Nat) (wide : Bool)
    (ready : GroupLoopReady state before budget remaining parents count) (depthBound : parents.length ≤ 98)
    (physical : (if wide then 8 else 4) ≤ middle.length)
    (notStrict : ¬(if wide then 8 else 4) + (before.length-middle.length) < remaining)
    (keyRun : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    LoopSupportSkip.encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.cont (drop middle (if wide then 8 else 4))) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have step := actual_group_fixed_source_all state before middle parent tag count parents budget remaining wide ready depthBound keyRun
  simp only [fixedResult,if_neg (by omega : ¬middle.length < (if wide then 8 else 4)),groupChild] at step
  refine ⟨step,?_⟩
  by_cases tooLarge : ¬(if wide then 8 else 4) + (before.length-middle.length) ≤ remaining
  · exact group_fixed_key_not_fit_reject state before middle tag budget remaining wide parents count ready tooLarge keyRun
  · have widthPositive : 0 < (if wide then 8 else 4) := by cases wide <;> decide
    have exactEnd : (if wide then 8 else 4) + (before.length-middle.length) = remaining := by omega
    have keyFits : before.length-remaining < middle.length := by have := ready.common.physical; omega
    obtain ⟨keyConsumed,keySpan,keyData,keyValid,keyModes,keyPositions,keyValue,keyTag,keyKnown,keyKinds,keyInner,keyDepth,keyStack,keyBudget,keyRemaining,keySeen,keyFinished,keyUtf,keySkip⟩ :=
      nested_native_fixed_key_entry state before middle tag (if wide then .SixtyFourBit else .ThirtyTwoBit) parents.length budget remaining
        ready.common.budgetBound ready.common.remainingBound ready.common.budgetEnough ready.common.physical keyFits ready.modes ready.common.positions
        ready.common.shape.kinds ready.common.shape.utf ready.common.value ready.common.valid ready.common.seen ready.common.finished ready.common.inner ready.depth
        ready.common.budgetCounter ready.common.childCounter ready.positive depthBound wide rfl (by omega) keyRun
    have keyMode : (feed state keyConsumed).modes = lane 3 := by cases wide <;> exact keyModes
    have keyLength : before.length = keyConsumed.length+middle.length := by
      have result := congrArg List.length keySpan
      simpa only [contents,List.length_map,List.length_append] using result
    have fieldCounter : (feed state keyConsumed).responseRemaining = BitVec.ofNat 64 (if wide then 8 else 4) := by
      rw [keyRemaining]
      congr 1
      omega
    have notTop := nested_depth_not_top (feed state keyConsumed) parents.length ready.positive (by omega) (keyDepth.trans ready.depth)
    have rejected := group_opaque_at_child_end_reject (feed state keyConsumed) middle (if wide then 8 else 4)
      (by have := ready.common.remainingBound; omega) widthPositive physical keyMode keyInner fieldCounter keySkip notTop
    rw [keySpan]
    simpa only [feed,List.foldl_append] using rejected

#print axioms actual_group_fixed_not_strict
end ChatResponseReference.StreamingUnknownV1
