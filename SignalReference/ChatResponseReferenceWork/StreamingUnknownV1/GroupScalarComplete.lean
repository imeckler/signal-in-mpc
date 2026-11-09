import ChatResponseReferenceWork.StreamingUnknownV1.GroupScalarValidity
import ChatResponseReferenceWork.StreamingUnknownV1.GroupScalarStack
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Complete numeric scalar skip at arbitrary real group depth: exact actual
native suffix, cache/control/validity/private counters and unchanged depth/stack.
Strict fit preserves space for the active group's required closing tag. -/
theorem group_scalar_value_complete (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (budget remaining : Nat) (ready : ChildReady (eraseGroupDepth state) before budget remaining)
    (cache : CacheAgrees outer source state) (strictFit : before.length-after.length < remaining)
    (modes : state.modes = lane 1) (unknown : state.scalarKnown = 0)
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧ CacheAgrees outer source (feed state consumed) ∧
      (feed state consumed).modes = lane 0 ∧ (feed state consumed).positions = oneHot 0 ∧
      (feed state consumed).value = 0 ∧ (feed state consumed).valid = 255 ∧
      (feed state consumed).depth = state.depth ∧ (feed state consumed).stack = state.stack ∧
      (feed state consumed).responseRemaining = BitVec.ofNat 64 (remaining-consumed.length) ∧
      (feed state consumed).inner = 255 := by
  obtain ⟨consumed,span,data,nextModes,nextPositions,nextValue⟩ := unknown_scalar_native_data state before after native remaining
    ready.remainingBound ready.physical (by omega) modes ready.positions ready.inner ready.childCounter unknown actual
  obtain ⟨validConsumed,validSpan,nextValid⟩ := group_native_scalar_valid state before after native budget remaining
    ready.budgetBound ready.remainingBound ready.budgetEnough ready.physical strictFit modes ready.positions ready.shape.kinds ready.valid
    ready.seen ready.finished ready.inner ready.budgetCounter ready.childCounter actual
  have validSame : validConsumed = consumed := consumed_prefix_unique _ _ _ _ validSpan span
  subst validConsumed
  obtain ⟨scopeConsumed,scopeSpan,nextRemaining,nextInner,nextDepth⟩ := native_scalar_scope state before after native remaining
    ready.remainingBound ready.physical (by omega) modes ready.positions ready.inner ready.childCounter actual
  have scopeSame : scopeConsumed = consumed := consumed_prefix_unique _ _ _ _ scopeSpan span
  subst scopeConsumed
  obtain ⟨stackConsumed,stackSpan,nextStack⟩ := native_scalar_stack state before after native modes ready.positions actual
  have stackSame : stackConsumed = consumed := consumed_prefix_unique _ _ _ _ stackSpan span
  subst stackConsumed
  have inputLength : before.length = consumed.length+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append] using result
  have consumedFit : consumed.length < remaining := by omega
  rw [if_neg (by omega : consumed.length ≠ remaining)] at nextInner
  exact ⟨consumed,span,data.trans cache,nextModes,nextPositions,nextValue,nextValid,nextDepth,nextStack,nextRemaining,nextInner⟩

#print axioms group_scalar_value_complete
end ChatResponseReference.StreamingUnknownV1
