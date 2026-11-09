import ChatResponseReferenceWork.StreamingUnknownV1.LengthTransition
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

def UnknownLengthStartSpan (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) : Prop :=
  ∃ leading byte tail,
    contents before = leading ++ byte::tail ∧ contents after = tail ∧
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
    next.skip = native.bv ∧ next.modes = if native.bv = BitVec.ofNat 64 0 then lane 0 else lane 3

/-- Exhaustive actual unknown length-delimited merger with numeric malformed
length/physical-underflow rejection. Success preserves the source record, exact
payload drop and native terminal controls; private-child fit and full payload
continuation are intentionally separate from physical source success. -/
theorem actual_unknown_length_refinement (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext)
    (unknown : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0)
    (value : state.value = 0) (kinds : state.kinds = [0,0,0,0]) :
    ∃ decoded after,
      PrefixPost before decoded after ∧ ErrorPost before decoded after ∧
      ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag .LengthDelimited before ctx =
        .ok (unknownLengthResult source decoded after) ∧
      match decoded with
      | .Err _ => (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0
      | .Ok native => UnknownLengthStartSpan state before after native ∧
          if native.val ≤ after.length then
            unknownLengthResult source decoded after =
              (.Ok (),source,LibSignalReference.Candidate.ProstSkipBuf.drop after native.val)
          else (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨decoded,after,run,prefixPost,errorPost⟩ := decode_full_reference before
  refine ⟨decoded,after,prefixPost,errorPost,unknown_length_from_decode source tag before after ctx unknown count decoded run,?_⟩
  cases decoded with
  | Err error => exact any_native_varint_error_reject state before after error 2 (by decide) modes positions value (.inl (by decide)) run
  | Ok native =>
    refine ⟨native_unknown_length_transition state before after native modes positions value kinds run,?_⟩
    by_cases fits : native.val ≤ after.length
    · rw [if_pos fits]
      simp only [unknownLengthResult,unchangedSkipResult,LibSignalReference.Candidate.ProstSkip.fixedResult,if_neg (by omega : ¬after.length < native.val)]
      rfl
    · rw [if_neg fits]
      exact native_unknown_length_underflow_reject state before after native modes positions value kinds (by omega) run

#print axioms actual_unknown_length_refinement
end ChatResponseReference.StreamingUnknownV1
