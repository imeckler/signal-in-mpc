import ChatResponseReferenceWork.StreamingUnknownV1.GroupVarintProjection
import ChatResponseReferenceWork.StreamingUnknownV1.GroupLengthStack
import ChatResponseReferenceWork.StreamingUnknownV1.LengthHeaderReady
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Full unknown length-header continuation at retained group depth, including
empty payloads. Whole-field fit and strict header room derive every private guard and leave a
live child, including when the payload itself reaches the child end, preserving actual depth/full stack. -/
theorem group_length_header_with_room (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (budget remaining : Nat) (ready : ChildReady (eraseGroupDepth state) before budget remaining)
    (cache : CacheAgrees outer source state) (payloadFit : native.val+(before.length-after.length) ≤ remaining)
    (headerInside : before.length-after.length < remaining)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,0,0,0])
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ header,
      contents before = header ++ contents after ∧ CacheAgrees outer source (feed state header) ∧
      (feed state header).kinds = [0,0,0,0] ∧ (feed state header).skip = native.bv ∧
      ChildReady (eraseGroupDepth (feed state header)) after (budget-header.length) (remaining-header.length) ∧
      (feed state header).modes = (if native.val = 0 then lane 0 else lane 3) ∧
      (feed state header).depth = state.depth ∧ (feed state header).stack = state.stack := by
  obtain ⟨flatHeader,flatSpan,flatCache,flatKinds,flatSkip,flatReady⟩ :=
    actual_unknown_length_header_ready outer source (eraseGroupDepth state) before after native budget remaining ready cache payloadFit modes kinds actual
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native actual
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result.symm
  have inputLength : before.length = leading.length+1+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  let header := leading++[byte]
  have headerSpan : contents before = header++contents after := by
    calc
      contents before = leading++byte::contents after := by rw [span,←suffix]
      _ = header++contents after := by simp only [header,List.append_assoc,List.singleton_append]
  have same : flatHeader = header := consumed_prefix_unique _ _ _ _ flatSpan headerSpan
  subst flatHeader
  have headerLength : header.length = leading.length+1 := by simp only [header,List.length_append,List.length_cons,List.length_nil]
  have projection : feed (eraseGroupDepth state) header = eraseGroupDepth (feed state header) :=
    group_varint_depth_projection state leading byte 2 remaining (.inr rfl) modes ready.shape.kinds ready.inner ready.remainingBound (by omega) ready.childCounter continues
  rw [projection] at flatCache flatKinds flatSkip flatReady
  obtain ⟨scopeHeader,scopeSpan,nextRemaining,nextInner,nextDepth⟩ := native_unknown_length_header_scope state before after native remaining
    ready.remainingBound ready.physical (by omega) modes ready.positions kinds ready.inner ready.childCounter actual
  have scopeSame : scopeHeader = header := consumed_prefix_unique _ _ _ _ scopeSpan headerSpan
  subst scopeHeader
  obtain ⟨stackHeader,stackSpan,nextStack⟩ := native_length_header_stack state before after native modes ready.positions actual
  have stackSame : stackHeader = header := consumed_prefix_unique _ _ _ _ stackSpan headerSpan
  subst stackHeader
  have positive : 0 < remaining-header.length := by omega
  have complete : ChildReady (eraseGroupDepth (feed state header)) after (budget-header.length) (remaining-header.length) ∧
      (feed state header).modes = (if native.val = 0 then lane 0 else lane 3) := by
    by_cases empty : native.val = 0
    · rw [if_pos empty] at flatReady ⊢
      exact ⟨ready_of_key _ _ _ _ flatReady positive,flatReady.modes⟩
    · rw [if_neg empty] at flatReady ⊢
      exact flatReady
  exact ⟨header,headerSpan,flatCache,flatKinds,flatSkip,complete.1,complete.2,nextDepth,nextStack⟩

#print axioms group_length_header_with_room
end ChatResponseReference.StreamingUnknownV1
