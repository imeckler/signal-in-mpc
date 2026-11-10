import ChatResponseReferenceWork.StreamingUnknownV1.GroupPendingKey
import ChatResponseReferenceWork.StreamingUnknownV1.FixedReject
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem group_fixed_key_not_fit_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before middle : Slice U8) (tag : U32) (budget remaining : Nat) (wide : Bool)
    (parents : List U32) (count : U32)
    (ready : GroupLoopReady state before budget remaining parents count)
    (notFit : ¬ (if wide then 8 else 4) + (before.length-middle.length) ≤ remaining)
    (actual : LoopSupportSkip.encoding.decode_key sliceBuf before =
      .ok (.Ok (tag,if wide then .SixtyFourBit else .ThirtyTwoBit),middle)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  by_cases inside : before.length-remaining < middle.length
  · obtain ⟨native,run,accepted⟩ := native_key_success_varint before middle tag _ actual
    obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before middle native run
    have tailLength : tail.length = middle.length := by
      have result := congrArg List.length suffix
      simpa only [contents,List.length_map] using result.symm
    have inputLength : before.length = leading.length+1+middle.length := by
      have result := congrArg List.length span
      simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
    have invariant := core_prefix_invariant state leading 0 0 (by decide) (by omega) ready.modes ready.common.positions continues
    have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
    have context := bounded_varint_prefix_context state leading remaining ready.common.remainingBound (by omega) ready.common.inner ready.common.childCounter continues
    have initialValue : state.value = 0 := ready.common.value
    have currentValue : (feed state leading).value = accumulated leading 0 0 := by simpa only [initialValue] using invariant.2.2
    have decoded : coreDecoded (feed state leading) byte = native.bv := by
      unfold coreDecoded
      rw [currentPositions,currentValue,contribution_one_hot leading.length (by omega) byte]
      exact nativeValue.symm
    have nativeKind := native_key_kind native tag _ accepted
    have kindFixed : Word64.concrete.band (coreDecoded (feed state leading) byte) (Word64.concrete.const 7) =
        Word64.concrete.const (if wide then 1 else 5) := by
      rw [decoded]
      change native.bv &&& 7 = _
      rw [nativeKind]
      cases wide <;> rfl
    have fixedOn : actualFixedOn (feed state leading) byte = 255 := by
      unfold actualFixedOn
      rw [kindFixed]
      cases wide <;> rfl
    have fixedLength : Word64.concrete.select
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete
          (Word64.concrete.band (coreDecoded (feed state leading) byte) (Word64.concrete.const 7)) 1)
        (Word64.concrete.const 8) (Word64.concrete.const 4) = BitVec.ofNat 64 (if wide then 8 else 4) := by
      rw [kindFixed]
      cases wide <;> rfl
    have available : availableLength (feed state leading) = BitVec.ofNat 64 (remaining-(leading.length+1)) := by
      unfold availableLength
      rw [context.2.2.2.1,Word64.select_accept,context.2.2.2.2]
      change BitVec.ofNat 64 (remaining-leading.length) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (remaining-leading.length) 1 (by decide) (by omega)]
      congr 1 <;> omega
    have bad : actualFixedGood (feed state leading) byte = 0 := by
      unfold actualFixedGood
      dsimp only
      rw [fixedLength,available,Word64.ule_value]
      have widthSmall : (if wide then 8 else 4) < 2^64 := by cases wide <;> decide
      have availableSmall : remaining-(leading.length+1) < 2^64 := by have := ready.common.remainingBound; omega
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt widthSmall,Nat.mod_eq_of_lt availableSmall]
      exact if_neg (by omega)
    have rejected := core_fixed_key_reject (feed state leading) byte invariant.1 terminal fixedOn bad
    rw [span]
    apply finish_invalid_sticky
    simp only [feed,List.foldl_append,List.foldl_cons]
    exact feed_invalid_sticky _ tail rejected
  · apply group_pending_key_not_inside_reject state before middle tag _ budget remaining parents count ready _ (by omega) actual
    cases wide <;> first | exact .inr (.inl rfl) | exact .inr (.inr (.inr rfl))

#print axioms group_fixed_key_not_fit_reject
end ChatResponseReference.StreamingUnknownV1
