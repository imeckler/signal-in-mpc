import ChatResponseReferenceWork.StreamingV1.NativeKnownKeyEntry
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

theorem actual_driver_key_native (before after : Slice U8) (tag : U32)
    (wire : ActualInnerScanV1.prost.encoding.wire_type.WireType)
    (sourceSuccess : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,wire),after)) :
    LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,ActualInnerResponseV1.toSkipWire wire),after) := by
  obtain ⟨result,middle,nativeRun,actualRun,_,_⟩ := InnerScanV1.key_total before
  cases result with
  | Err error =>
    rw [sourceSuccess] at actualRun
    simp at actualRun
  | Ok pair =>
    rcases pair with ⟨nativeTag,nativeWire⟩
    rw [sourceSuccess] at actualRun
    have eqPair := congrArg Prod.fst (Result.ok.inj actualRun)
    have eqSuffix := congrArg Prod.snd (Result.ok.inj actualRun)
    simp only [core.result.Result.Ok.injEq,Prod.mk.injEq] at eqPair
    obtain ⟨tagEq,wireEq⟩ := eqPair
    have inverse : nativeWire = ActualInnerResponseV1.toSkipWire wire := by
      have inverseRaw (raw : WireType) : ActualInnerResponseV1.toSkipWire (ActualResponseBytesV1.fromSkipWire raw) = raw := by
        cases raw <;> rfl
      rw [wireEq]
      exact (inverseRaw nativeWire).symm
    change after = middle at eqSuffix
    rw [←tagEq,←eqSuffix,inverse] at nativeRun
    exact nativeRun

theorem actual_driver_known_key_entry (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : ActualInnerScanV1.prost.encoding.wire_type.WireType) (budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : before.length ≤ budget) (physical : remaining ≤ before.length)
    (childFits : before.length-remaining < after.length)
    (modes : state.modes = lane 0) (positions : state.positions = oneHot 0)
    (kindsShape : state.kinds.length = 4) (utfShape : state.utf.length = 8)
    (value : state.value = 0) (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget)
    (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (known : (tag.val = 1 ∨ tag.val = 2) ∧ wire = .Varint ∨
      (tag.val = 3 ∨ tag.val = 4 ∨ tag.val = 5) ∧ wire = .LengthDelimited)
    (sourceSuccess : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,wire),after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      responseData (feed state consumed) = responseData state ∧
      (feed state consumed).valid = 255 ∧
      (feed state consumed).modes = lane (wireLane (wireNumber (ActualInnerResponseV1.toSkipWire wire))) ∧
      (feed state consumed).positions = oneHot 0 ∧ (feed state consumed).value = 0 ∧
      (feed state consumed).tag = BitVec.ofNat 64 tag.val ∧
      (feed state consumed).scalarKnown = (if tag.val = 1 ∨ tag.val = 2 then 255 else 0) ∧
      (feed state consumed).kinds = [0,if tag.val = 4 then 255 else 0,if tag.val = 3 then 255 else 0,if tag.val = 5 then 255 else 0] ∧
      (feed state consumed).inner = 255 ∧ (feed state consumed).depth = 0 ∧
      (feed state consumed).budget = BitVec.ofNat 64 (budget-consumed.length) ∧
      (feed state consumed).responseRemaining = BitVec.ofNat 64 (remaining-consumed.length) ∧
      (feed state consumed).seen = 255 ∧ (feed state consumed).finished = 0 ∧
      (feed state consumed).utf.length = 8 := by
  have knownNative : (tag.val = 1 ∨ tag.val = 2) ∧ ActualInnerResponseV1.toSkipWire wire = .Varint ∨
      (tag.val = 3 ∨ tag.val = 4 ∨ tag.val = 5) ∧ ActualInnerResponseV1.toSkipWire wire = .LengthDelimited := by
    rcases known with ⟨tags,wireEq⟩ | ⟨tags,wireEq⟩
    · rw [wireEq]; exact .inl ⟨tags,rfl⟩
    · rw [wireEq]; exact .inr ⟨tags,rfl⟩
  exact native_known_key_entry state before after tag (ActualInnerResponseV1.toSkipWire wire) budget remaining
    budgetBound remainingBound budgetEnough physical childFits modes positions kindsShape utfShape value valid seen finished inner depth
    budgetCounter childCounter knownNative (actual_driver_key_native before after tag wire sourceSuccess)

#print axioms actual_driver_key_native
#print axioms actual_driver_known_key_entry
end ChatResponseReference.StreamingV1
