import ChatResponseReferenceWork.StreamingUnknownV1.FixedSource
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Actual unknown length-delimited outcome: malformed length preserves the
native decoder suffix; a decoded length uses the real physical-fit skip result. -/
def unknownLengthResult (source : InnerResponseV1.Message)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :=
  unchangedSkipResult source (match decoded with
    | .Ok native => LibSignalReference.Candidate.ProstSkip.fixedResult after native.val
    | .Err error => (.Err error,after))

theorem unknown_length_from_decode (source : InnerResponseV1.Message) (tag : U32)
    (before after : Slice U8) (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext)
    (unknown : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (decoded,after)) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag .LengthDelimited before ctx =
    .ok (unknownLengthResult source decoded after) := by
  apply unknown_from_native_skip source tag _ before ctx unknown
  simp only [ActualInnerResponseV1.toSkipWire]
  cases decoded with
  | Ok native => exact LibSignalReference.Candidate.ProstSkip.length_delimited_after before after native tag ctx.recurse_count count actual
  | Err error => exact LibSignalReference.Candidate.ProstSkip.length_delimited_error before after error tag ctx.recurse_count count actual

/-- Native termination, length decoding and physical payload fit are derived,
including every malformed-length and physical-underflow outcome. Private child
bounds and Core continuation/rejection are subsequent composition obligations. -/
theorem unknown_length_source_all (source : InnerResponseV1.Message) (tag : U32)
    (before : Slice U8) (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext)
    (unknown : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32) :
    ∃ decoded after,
      PrefixPost before decoded after ∧ ErrorPost before decoded after ∧
      ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag .LengthDelimited before ctx =
        .ok (unknownLengthResult source decoded after) := by
  obtain ⟨decoded,after,actual,prefixPost,errorPost⟩ := decode_full_reference before
  exact ⟨decoded,after,prefixPost,errorPost,unknown_length_from_decode source tag before after ctx unknown count decoded actual⟩

/-- Actual default merger and length lexer on all inputs, preserving source
errors/suffix and deriving numeric EOF rejection for malformed length varints.
Successful decoding only identifies the terminal row; child-fit and payload
continuation are deliberately not inferred from decoder success. -/
theorem unknown_length_lexer_all (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (unknown : 5 < tag.val)
    (count : ctx.recurse_count ≠ 0#u32) (modes : state.modes = lane 2)
    (positions : state.positions = oneHot 0) (value : state.value = 0) :
    ∃ decoded after,
      PrefixPost before decoded after ∧ ErrorPost before decoded after ∧
      ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag .LengthDelimited before ctx =
        .ok (unknownLengthResult source decoded after) ∧
      match decoded with
      | .Ok native => PayloadSpan state before after native
      | .Err _ => (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨decoded,after,actual,prefixPost,errorPost⟩ := decode_full_reference before
  refine ⟨decoded,after,prefixPost,errorPost,unknown_length_from_decode source tag before after ctx unknown count decoded actual,?_⟩
  cases decoded with
  | Ok native => exact any_native_varint_success state before after native 2 (by decide) modes positions value actual
  | Err error => exact any_native_varint_error_reject state before after error 2 (by decide) modes positions value (.inl (by decide)) actual

#print axioms unknown_length_lexer_all
#print axioms unknown_length_from_decode
#print axioms unknown_length_source_all
end ChatResponseReference.StreamingUnknownV1
