import ProtoParseWork.FullParserV3Work.SkipTotality
import ProtoParseWork.ParserErrorStateV2Work.Replayed.ContiguousReference
open Aeneas Aeneas.Std Result
open SignalMessageIntegration
namespace FullParserV3
set_option maxHeartbeats 1000000

theorem skip_slice_adapter : toSkipBuf DispatcherIntegration.sliceBuf =
    LibSignalReference.Candidate.ProstSkipBuf.sliceBuf := rfl

/-- The actual generated unknown-field dispatcher always terminates under the
accepted contiguous-buffer models, preserving fields on rejection and success. -/
theorem unknown_dispatch_total (m : proto.wire.SignalMessage) (tag : U32)
    (wire : prost.encoding.wire_type.WireType) (before : Slice U8)
    (ctx : prost.encoding.DecodeContext) (htag : 6 < tag.val) :
    ∃ status after,
      proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        DispatcherIntegration.sliceBuf m tag wire before ctx = ok (status,m,after) ∧
      after.length ≤ before.length := by
  obtain ⟨result,_,hskip,hle⟩ := skip_field_total (toSkipWire wire) tag ctx.recurse_count before
  rcases result with ⟨status,after⟩
  cases status with
  | Ok value =>
    refine ⟨.Ok value,after,?_,hle⟩
    rw [DispatcherIntegration.unknown_dispatch _ _ _ _ _ _ htag]
    unfold prost.encoding.skip_field
    rw [skip_slice_adapter,hskip]
    rfl
  | Err error =>
    refine ⟨.Err (skipError error),after,?_,hle⟩
    rw [DispatcherIntegration.unknown_dispatch _ _ _ _ _ _ htag]
    unfold prost.encoding.skip_field
    rw [skip_slice_adapter,hskip]
    rfl

#print axioms skip_slice_adapter
#print axioms unknown_dispatch_total
end FullParserV3
