import ChatResponseReferenceWork.StreamingV1.CallbackSuccessNative
import ProtoParseWork.FullParserV3Work.Skip.SkipLeaf
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Unknown response tags retain the actual generated default branch, including
source message identity, exact skip result/suffix, and fail/div behavior. -/
theorem unknown_dispatcher (source : InnerResponseV1.Message) (tag : U32)
    (wire : ActualInnerResponseV1.prost.encoding.wire_type.WireType) (before : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (unknown : 5 < tag.val) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag wire before ctx =
    (do let (result,after) ← ActualInnerResponseV1.prost.encoding.skip_field InnerResponseV1.sliceBuf wire tag before ctx
        .ok (result,source,after)) := by
  rw [InnerResponseV1.dispatcher_reference]
  unfold InnerResponseV1.fieldSpec
  split
  · exact False.elim ((by decide : ¬5 < (1#u32).val) unknown)
  · exact False.elim ((by decide : ¬5 < (2#u32).val) unknown)
  · exact False.elim ((by decide : ¬5 < (3#u32).val) unknown)
  · exact False.elim ((by decide : ¬5 < (4#u32).val) unknown)
  · exact False.elim ((by decide : ¬5 < (5#u32).val) unknown)
  · rfl

def unknownScalarResult (source : InnerResponseV1.Message)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :
    core.result.Result Unit ActualInnerResponseV1.prost.error.DecodeError × InnerResponseV1.Message × Slice U8 :=
  match decoded with
  | .Ok _ => (.Ok (),source,after)
  | .Err error => (.Err (ActualResponseBytesV1.fromSkipError error),source,after)

theorem unknown_varint_from_decode (source : InnerResponseV1.Message) (tag : U32)
    (before after : Slice U8) (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext)
    (unknown : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (decoded,after)) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag .Varint before ctx =
    .ok (unknownScalarResult source decoded after) := by
  rw [unknown_dispatcher source tag .Varint before ctx unknown]
  unfold ActualInnerResponseV1.prost.encoding.skip_field
  rw [InnerResponseV1.scalar_adapter]
  simp only [ActualInnerResponseV1.toSkipWire]
  cases decoded with
  | Ok native =>
    rw [LibSignalReference.Candidate.ProstSkip.skip_varint_after before after native tag ctx.recurse_count count actual]
    rfl
  | Err error =>
    rw [LibSignalReference.Candidate.ProstSkip.skip_varint_error before after error tag ctx.recurse_count count actual]
    rfl

/-- Exhaustive actual source unknown-varint outcome and Core scalar lexer relation.
No primitive correctness/termination or success premise is supplied. Child/budget
entry and successful field continuation are separate full-scan obligations. -/
theorem unknown_varint_all (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (unknown : 5 < tag.val)
    (count : ctx.recurse_count ≠ 0#u32) (modes : state.modes = lane 1)
    (positions : state.positions = oneHot 0) (value : state.value = 0) :
    ∃ decoded after,
      PrefixPost before decoded after ∧ ErrorPost before decoded after ∧
      ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag .Varint before ctx =
        .ok (unknownScalarResult source decoded after) ∧
      match decoded with
      | .Ok native => PayloadSpan state before after native
      | .Err _ => (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨decoded,after,actual,prefixPost,errorPost⟩ := decode_full_reference before
  refine ⟨decoded,after,prefixPost,errorPost,unknown_varint_from_decode source tag before after ctx unknown count decoded actual,?_⟩
  cases decoded with
  | Ok native => exact any_native_varint_success state before after native 1 (by decide) modes positions value actual
  | Err error => exact any_native_varint_error_reject state before after error 1 (by decide) modes positions value (.inl (by decide)) actual

#print axioms unknown_varint_from_decode
#print axioms unknown_varint_all
#print axioms unknown_dispatcher
end ChatResponseReference.StreamingUnknownV1
