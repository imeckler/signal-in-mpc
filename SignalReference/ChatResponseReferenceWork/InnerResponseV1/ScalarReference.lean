import ChatResponseReferenceWork.InnerResponseV1.ScalarSource
import ProtoParseWork.FullParserV3Work.Skip.Replayed.Consumption
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerResponseV1
open ActualInnerResponseV1
abbrev sliceBuf : bytes.buf.buf_impl.Buf (Slice U8) :=
  ⟨LibSignalReference.Candidate.ProstBytesBuf.remaining,
   LibSignalReference.Candidate.ProstBytesBuf.chunk,
   LibSignalReference.Candidate.ProstBytesBuf.advance⟩
theorem scalar_adapter : ActualResponseBytesV1.toSkipBuf (toBytesBuf sliceBuf) =
    LibSignalReference.Candidate.ProstSkipBuf.sliceBuf := rfl

def scalarResult32 (old : U32) (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :
    core.result.Result Unit prost.error.DecodeError × U32 × Slice U8 :=
  match decoded with
  | .Ok value => (.Ok (),UScalar.cast .U32 value,after)
  | .Err error => (.Err (ActualResponseBytesV1.fromSkipError error),old,after)
def scalarResult64 (old : U64) (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :
    core.result.Result Unit prost.error.DecodeError × U64 × Slice U8 :=
  match decoded with
  | .Ok value => (.Ok (),value,after)
  | .Err error => (.Err (ActualResponseBytesV1.fromSkipError error),old,after)

theorem uint32_from_decode (old : U32) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (run : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (decoded,after)) :
    prost.encoding.uint32.merge sliceBuf .Varint old before ctx = .ok (scalarResult32 old decoded after) := by
  unfold prost.encoding.uint32.merge
  have wire : prost.encoding.wire_type.check_wire_type .Varint .Varint = .ok (.Ok ()) := rfl
  rw [wire]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  unfold prost.encoding.varint.decode_varint ActualResponseBytesV1.prost.encoding.varint.decode_varint
  rw [scalar_adapter,run]
  cases decoded <;> rfl

theorem uint64_from_decode (old : U64) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (run : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (decoded,after)) :
    prost.encoding.uint64.merge sliceBuf .Varint old before ctx = .ok (scalarResult64 old decoded after) := by
  unfold prost.encoding.uint64.merge
  have wire : prost.encoding.wire_type.check_wire_type .Varint .Varint = .ok (.Ok ()) := rfl
  rw [wire]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  unfold prost.encoding.varint.decode_varint ActualResponseBytesV1.prost.encoding.varint.decode_varint
  rw [scalar_adapter,run]
  cases decoded <;> rfl

/-- Actual full-width ID and low32 status mergers share the exact accepted native
varint/error/suffix observation; no decoder/termination hypothesis remains. -/
theorem scalar_full_reference (id : U64) (status : U32) (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstSkipBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstSkipBuf.ErrorPost before decoded after ∧
      prost.encoding.uint32.merge sliceBuf .Varint status before ctx = .ok (scalarResult32 status decoded after) ∧
      prost.encoding.uint64.merge sliceBuf .Varint id before ctx = .ok (scalarResult64 id decoded after) := by
  obtain ⟨decoded,after,run,prefixPost,errorPost⟩ := LibSignalReference.Candidate.ProstSkipBuf.decode_full_reference before
  exact ⟨decoded,after,prefixPost,errorPost,uint32_from_decode status before after ctx decoded run,
    uint64_from_decode id before after ctx decoded run⟩
#print axioms scalar_adapter
#print axioms scalar_full_reference
end ChatResponseReference.InnerResponseV1
