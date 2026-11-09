import ChatResponseReferenceWork.StreamingV1.AnyKeyError
import ChatResponseReferenceWork.StreamingV1.ListChoice
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
set_option maxRecDepth 100000
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkipKey

theorem rejected_row_key_error (before : Slice U8)
    (numeric : (ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (contents before) 0).ok = 0) :
    ∃ error after, LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Err error,after) := by
  obtain ⟨error,after,run,_,_⟩ := native_prefix_rejection before numeric
  exact ⟨error,after,key_from_varint before after (.Err error) run⟩

/-- Every actual successful key supplies the Core's complete next lexer control
state, input span and exact returned tail. No prefix/table premise is supplied. -/
theorem any_native_key_success_transition (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : WireType)
    (modes : state.modes = lane 0) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (sourceSuccess : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    ∃ leading byte tail,
      contents before = leading ++ byte::tail ∧ contents after = tail ∧
      leading.length+1 ≤ before.length ∧
      let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (feed state leading) byte).state
      next.tag = BitVec.ofNat 64 tag.val ∧ next.modes = lane (wireLane (wireNumber wire)) ∧
      next.value = 0 ∧ next.positions = oneHot 0 := by
  cases lexer_shape (contents before) with
  | terminal leading tail byte span bound continues ended tenth =>
    obtain ⟨native,suffix,keyRun,_,nativeValue,suffixTail,lengthBound⟩ :=
      core_terminal_key state before leading tail byte bound modes positions value span continues ended tenth
    rw [sourceSuccess] at keyRun
    have accepted : keyResult native = .Ok (tag,wire) := (congrArg Prod.fst (Result.ok.inj keyRun)).symm
    have suffixEq : after = suffix := congrArg Prod.snd (Result.ok.inj keyRun)
    have invariant := core_prefix_invariant state leading 0 0 (by decide) (by omega) modes positions continues
    refine ⟨leading,byte,tail,span,?_,lengthBound,?_,?_,?_,?_⟩
    · rw [suffixEq]; exact suffixTail
    · exact native_tag_transition _ byte native tag wire invariant.1 ended nativeValue accepted
    · exact native_key_modes _ byte native tag wire invariant.1 ended nativeValue accepted
    · exact terminal_value_reset _ byte 0 (by decide) invariant.1 ended
    · apply terminal_position_reset _ byte 0 leading.length (by decide) invariant.1
      · simpa only [Nat.zero_add] using invariant.2.1
      · exact ended
  | malformed leading tail byte span length continues invalid =>
    have numeric := rejected_tenth_row leading tail byte length continues invalid
    rw [←span] at numeric
    obtain ⟨error,suffix,errorRun⟩ := rejected_row_key_error before numeric
    rw [sourceSuccess] at errorRun
    simp at errorRun
  | truncated leading span bound continues =>
    have numeric := truncated_row leading (by omega) continues
    rw [←span] at numeric
    obtain ⟨error,suffix,errorRun⟩ := rejected_row_key_error before numeric
    rw [sourceSuccess] at errorRun
    simp at errorRun

/-- Successful-key transition at the actual generated schema driver's ABI. -/
theorem actual_driver_key_success_transition (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : ActualInnerScanV1.prost.encoding.wire_type.WireType)
    (modes : state.modes = lane 0) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (sourceSuccess : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,wire),after)) :
    ∃ leading byte tail,
      contents before = leading ++ byte::tail ∧ contents after = tail ∧
      leading.length+1 ≤ before.length ∧
      let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (feed state leading) byte).state
      next.tag = BitVec.ofNat 64 tag.val ∧ next.modes = lane (wireLane (wireNumber (ActualInnerResponseV1.toSkipWire wire))) ∧
      next.value = 0 ∧ next.positions = oneHot 0 := by
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
    exact any_native_key_success_transition state before after tag (ActualInnerResponseV1.toSkipWire wire)
      modes positions value nativeRun

#print axioms rejected_row_key_error
#print axioms any_native_key_success_transition
#print axioms actual_driver_key_success_transition
end ChatResponseReference.StreamingV1
