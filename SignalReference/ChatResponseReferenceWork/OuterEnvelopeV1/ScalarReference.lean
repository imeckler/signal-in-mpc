import ChatResponseReferenceWork.OuterEnvelopeV1.Replayed.Funs
import ChatResponseReferenceWork.InnerScanV1.Consumption
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.OuterEnvelopeV1
open ActualOuterEnvelopeV1
abbrev sliceBuf := InnerResponseV1.sliceBuf

def scalarResult (old : I32) (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :
    core.result.Result Unit prost.error.DecodeError × I32 × Slice U8 :=
  match decoded with
  | .Ok value => (.Ok (),UScalar.hcast .I32 value,after)
  | .Err error => (.Err (ActualResponseBytesV1.fromSkipError error),old,after)

theorem int32_from_decode (old : I32) (before after : Slice U8) (ctx : prost.encoding.DecodeContext)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (run : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (decoded,after)) :
    prost.encoding.int32.merge sliceBuf .Varint old before ctx = .ok (scalarResult old decoded after) := by
  unfold prost.encoding.int32.merge
  have wire : prost.encoding.wire_type.check_wire_type .Varint .Varint = .ok (.Ok ()) := rfl
  rw [wire]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  unfold prost.encoding.varint.decode_varint ActualInnerResponseV1.prost.encoding.varint.decode_varint ActualResponseBytesV1.prost.encoding.varint.decode_varint
  rw [InnerResponseV1.scalar_adapter,run]
  cases decoded <;> rfl

/-- Actual signed enum scalar cast and all wire errors, preserving old values on
error and exact decoder suffix; no varint correctness/termination premise. -/
theorem int32_consumption (old : I32) (wire : prost.encoding.wire_type.WireType)
    (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    ∃ result value after,
      prost.encoding.int32.merge sliceBuf wire old before ctx = .ok (result,value,after) ∧
      after.length ≤ before.length := by
  have varint : ∃ result value after,
      prost.encoding.int32.merge sliceBuf .Varint old before ctx = .ok (result,value,after) ∧
      after.length ≤ before.length := by
    obtain ⟨decoded,after,run,bound,strict⟩ := FullParserV3.varint_total before
    have merged := int32_from_decode old before after ctx decoded run
    cases decoded <;> exact ⟨_,_,_,merged,bound⟩
  cases wire <;> first | exact varint | exact ⟨_,_,_,rfl,Nat.le_refl _⟩
#print axioms int32_from_decode
#print axioms int32_consumption
end ChatResponseReference.OuterEnvelopeV1
