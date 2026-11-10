import ChatResponseReferenceWork.StreamingUnknownV1.GroupScalarInduction
import ChatResponseReferenceWork.StreamingUnknownV1.GroupFixedInduction
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthInduction
import ChatResponseReferenceWork.StreamingUnknownV1.GroupStartInduction
import ChatResponseReferenceWork.StreamingUnknownV1.GroupOutcomeClose
import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyError
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLimitRejection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkip
open LoopSupportSkip
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Complete actual inner-group scan, all source outcomes, by strict physical
slice-length induction. Active tags, actual source recursion context, private
child boundary, complete numeric cache/frame and exact native suffix coexist;
compatible native success cannot be replaced by arbitrary numeric rejection. -/
theorem actual_inner_group_refinement (outer : ResponseData) (source : InnerResponseV1.Message)
    (before : Slice U8) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (parent count : U32) (older : List U32) (budget remaining : Nat)
    (ready : GroupLoopReady state before budget remaining (older++[parent]) count)
    (cache : CacheAgrees outer source state) :
    ∃ result, encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok result ∧
      GroupOutcome outer source state before budget remaining older count result := by
  have bounded : ∀ size : Nat, ∀ view : Slice U8, view.length = size →
      ∀ (next : TlsChatResponse.State (BitVec 8) (BitVec 64)) (nextParent nextCount : U32) (nextOlder : List U32) (nextBudget nextRemaining : Nat),
      GroupLoopReady next view nextBudget nextRemaining (nextOlder++[nextParent]) nextCount → CacheAgrees outer source next →
      ∃ result, encoding.skip_field_loop sliceBuf nextParent view ⟨nextCount⟩ = .ok result ∧
        GroupOutcome outer source next view nextBudget nextRemaining nextOlder nextCount result := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro view sizeEq next nextParent nextCount nextOlder nextBudget nextRemaining nextReady nextCache
      have recursive : ∀ after : Slice U8, after.length < view.length →
          ∀ (current : TlsChatResponse.State (BitVec 8) (BitVec 64)) (currentParent currentCount : U32) (currentOlder : List U32) (currentBudget currentRemaining : Nat),
          GroupLoopReady current after currentBudget currentRemaining (currentOlder++[currentParent]) currentCount → CacheAgrees outer source current →
          ∃ result, encoding.skip_field_loop sliceBuf currentParent after ⟨currentCount⟩ = .ok result ∧
            GroupOutcome outer source current after currentBudget currentRemaining currentOlder currentCount result := by
        intro after strict
        exact ih after.length (by omega) after rfl
      obtain ⟨decoded,middle,keyRun,keyBound,keyStrict⟩ := FullParserV3.key_total view
      cases decoded with
      | Err error =>
        obtain ⟨body,run,rejected⟩ := actual_group_key_error next view middle nextParent nextCount (nextOlder++[nextParent]) nextBudget nextRemaining error nextReady keyRun
        exact ⟨(.Err error,middle),run,rejected⟩
      | Ok pair =>
        rcases pair with ⟨tag,wire⟩
        classical
        by_cases isEnd : wire = .EndGroup
        · subst wire
          exact ⟨groupClose nextParent tag middle,
            (actual_group_close_attempt_all outer source next view middle nextParent tag nextCount nextOlder nextBudget nextRemaining nextReady nextCache keyRun).2.1,
            group_close_outcome outer source next view middle nextParent tag nextCount nextOlder nextBudget nextRemaining nextReady nextCache keyRun⟩
        · by_cases atLimit : (nextOlder++[nextParent]).length = 99
          · obtain ⟨body,run,rejected⟩ := actual_group_limit_error next view middle nextParent tag nextCount wire (nextOlder++[nextParent]) nextBudget nextRemaining nextReady atLimit isEnd keyRun
            exact ⟨(.Err (decodeError .RecursionLimitReached),middle),run,rejected⟩
          · have depthBound : (nextOlder++[nextParent]).length ≤ 98 := by have := nextReady.bounded; omega
            cases wire with
            | Varint =>
              exact group_varint_induction_step outer source next view middle nextParent tag nextCount nextOlder nextBudget nextRemaining nextReady nextCache depthBound keyRun
                (fun after strict current currentBudget currentRemaining currentReady currentCache => recursive after strict current nextParent nextCount nextOlder currentBudget currentRemaining currentReady currentCache)
            | SixtyFourBit =>
              exact group_fixed_induction_step outer source next view middle nextParent tag nextCount nextOlder nextBudget nextRemaining true nextReady nextCache depthBound keyRun
                (fun after strict current currentBudget currentRemaining currentReady currentCache => recursive after strict current nextParent nextCount nextOlder currentBudget currentRemaining currentReady currentCache)
            | LengthDelimited =>
              exact group_length_induction_step outer source next view middle nextParent tag nextCount nextOlder nextBudget nextRemaining nextReady nextCache depthBound keyRun
                (fun after strict current currentBudget currentRemaining currentReady currentCache => recursive after strict current nextParent nextCount nextOlder currentBudget currentRemaining currentReady currentCache)
            | StartGroup =>
              exact group_start_induction_step outer source next view middle nextParent tag nextCount nextOlder nextBudget nextRemaining nextReady nextCache depthBound keyRun recursive
            | EndGroup => exact False.elim (isEnd rfl)
            | ThirtyTwoBit =>
              exact group_fixed_induction_step outer source next view middle nextParent tag nextCount nextOlder nextBudget nextRemaining false nextReady nextCache depthBound keyRun
                (fun after strict current currentBudget currentRemaining currentReady currentCache => recursive after strict current nextParent nextCount nextOlder currentBudget currentRemaining currentReady currentCache)
  exact bounded before.length before rfl state parent count older budget remaining ready cache

#print axioms actual_inner_group_refinement
end ChatResponseReference.StreamingUnknownV1
