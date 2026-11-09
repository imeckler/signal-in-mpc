import ChatResponseReferenceWork.InnerResponseV1.SkipBridge
import ChatResponseReferenceWork.InnerResponseV1.ScalarReference
import ProtoParseWork.FullParserV3Work.SkipTotality
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerResponseV1
open ActualInnerResponseV1

def skipResult (result : core.result.Result Unit LoopSupportSkip.error.DecodeError × Slice U8) :
    core.result.Result Unit prost.error.DecodeError × Slice U8 :=
  match result.1 with
  | .Ok unit => (.Ok unit,result.2)
  | .Err error => (.Err (ActualResponseBytesV1.fromSkipError error),result.2)

/-- All wire kinds, groups, malformed inputs and zero budget. The inherited
finite derivation proves termination; no finite-skip premise is supplied. -/
theorem skip_full_reference (wire : prost.encoding.wire_type.WireType) (tag : U32)
    (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    ∃ result,
      LibSignalReference.Candidate.ProstSkip.SkipSemantics (.field (toSkipWire wire)) tag ctx.recurse_count before result ∧
      prost.encoding.skip_field sliceBuf wire tag before ctx = .ok (skipResult result) ∧
      result.2.length ≤ before.length := by
  obtain ⟨result,semantics,run,bound⟩ := FullParserV3.skip_field_total (toSkipWire wire) tag ctx.recurse_count before
  refine ⟨result,semantics,?_,bound⟩
  unfold prost.encoding.skip_field
  rw [scalar_adapter,run]
  rcases result with ⟨r,after⟩
  cases r <;> rfl
#print axioms skip_full_reference
end ChatResponseReference.InnerResponseV1
