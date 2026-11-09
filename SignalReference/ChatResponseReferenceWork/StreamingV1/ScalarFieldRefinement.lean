import ChatResponseReferenceWork.StreamingV1.IdPresence
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

def UpdateSpan (field : TlsChatResponse.State (BitVec 8) (BitVec 64) → BitVec 64)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (expected : BitVec 64) : Prop :=
  ∃ leading byte tail,
    contents before = leading ++ byte::tail ∧ contents after = tail ∧
    field (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state = expected

/-- Actual generated ID dispatcher→Core ID field component on every input and
native outcome. Exact error/default/duplicate effects remain on the source side;
child-success cursor bounds are explicit and must be derived by the full scan. -/
theorem actual_id_field_refinement (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (remaining : Nat)
    (capacity : remaining ≤ 4096) (physical : remaining ≤ before.length)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (known : state.scalarKnown = 255) (tag : state.tag = 1) :
    ∃ decoded after,
      PrefixPost before decoded after ∧ ErrorPost before decoded after ∧
      ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (1#u32) .Varint before ctx =
        idFieldDecoded source decoded after ∧
      match decoded with
      | .Ok native => idFieldDecoded source decoded after =
          .ok (.Ok (),{source with id := some native},after) ∧
          (before.length-remaining ≤ after.length → IdUpdateSpan state before after native.bv)
      | .Err _ => (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨decoded,after,run,prefixPost,errorPost⟩ := decode_full_reference before
  refine ⟨decoded,after,prefixPost,errorPost,actual_id_field_decoded source before after ctx decoded run,?_⟩
  cases decoded with
  | Ok native =>
    refine ⟨rfl,?_⟩
    intro fits
    exact bounded_scalar_id_full_update state before after native remaining capacity physical fits modes positions value inner counter known tag run
  | Err error =>
    exact any_native_varint_error_reject state before after error 1 (by decide) modes positions value (.inl (by decide)) run

/-- Actual generated status dispatcher→Core low32 status component, retaining
all input/outcome source effects and explicit bounded-child success condition. -/
theorem actual_status_field_refinement (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (remaining : Nat)
    (capacity : remaining ≤ 4096) (physical : remaining ≤ before.length)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (known : state.scalarKnown = 255) (tag : state.tag = 2) :
    ∃ decoded after,
      PrefixPost before decoded after ∧ ErrorPost before decoded after ∧
      ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (2#u32) .Varint before ctx =
        statusFieldDecoded source decoded after ∧
      match decoded with
      | .Ok native => statusFieldDecoded source decoded after =
          .ok (.Ok (),{source with status := some (UScalar.cast .U32 native)},after) ∧
          (before.length-remaining ≤ after.length →
            UpdateSpan (·.status) state before after (statusWord (UScalar.cast .U32 native)))
      | .Err _ => (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨decoded,after,run,prefixPost,errorPost⟩ := decode_full_reference before
  refine ⟨decoded,after,prefixPost,errorPost,actual_status_field_decoded source before after ctx decoded run,?_⟩
  cases decoded with
  | Ok native =>
    refine ⟨rfl,?_⟩
    intro fits
    exact bounded_scalar_status_update state before after native remaining capacity physical fits modes positions value inner counter known tag run
  | Err error =>
    exact any_native_varint_error_reject state before after error 1 (by decide) modes positions value (.inl (by decide)) run

#print axioms actual_id_field_refinement
#print axioms actual_status_field_refinement
end ChatResponseReference.StreamingV1
