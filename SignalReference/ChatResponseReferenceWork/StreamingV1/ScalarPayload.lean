import ChatResponseReferenceWork.StreamingV1.AnyVarint
import ChatResponseReferenceWork.StreamingV1.ScalarProjection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Payload lexer correspondence, independent of validity of the surrounding
field/message. The complete schema invariant must supply field/recursion bounds. -/
def PayloadSpan (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) : Prop :=
  ∃ leading byte tail,
    contents before = leading ++ byte::tail ∧ contents after = tail ∧
    leading.length+1 ≤ before.length ∧ coreDecoded (feed state leading) byte = native.bv ∧
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (feed state leading) byte).state
    next.value = 0 ∧ next.positions = oneHot 0

/-- Actual pinned uint64/uint32 mergers and actual Core payload lexer on every
input/outcome. Source scalar values, exact error/suffix and mutation are retained;
errors force Core rejection. No source merge result or decoder premise is assumed. -/
theorem actual_scalar_payload (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (oldId : U64) (oldStatus : U32) (before : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0) (value : state.value = 0) :
    ∃ decoded after,
      PrefixPost before decoded after ∧ ErrorPost before decoded after ∧
      ActualInnerResponseV1.prost.encoding.uint32.merge InnerResponseV1.sliceBuf .Varint oldStatus before ctx =
        .ok (InnerResponseV1.scalarResult32 oldStatus decoded after) ∧
      ActualInnerResponseV1.prost.encoding.uint64.merge InnerResponseV1.sliceBuf .Varint oldId before ctx =
        .ok (InnerResponseV1.scalarResult64 oldId decoded after) ∧
      match decoded with
      | .Ok native => PayloadSpan state before after native ∧
          statusWord (UScalar.cast .U32 native) = native.bv &&& 4294967295
      | .Err _ => (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨decoded,after,run,prefixPost,errorPost⟩ := decode_full_reference before
  refine ⟨decoded,after,prefixPost,errorPost,InnerResponseV1.uint32_from_decode oldStatus before after ctx decoded run,
    InnerResponseV1.uint64_from_decode oldId before after ctx decoded run,?_⟩
  cases decoded with
  | Ok native =>
    exact ⟨any_native_varint_success state before after native 1 (by decide) modes positions value run,
      status_cast_projection native⟩
  | Err error =>
    exact any_native_varint_error_reject state before after error 1 (by decide) modes positions value (.inl (by decide)) run

#print axioms actual_scalar_payload
end ChatResponseReference.StreamingV1
