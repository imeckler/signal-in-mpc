import ChatResponseReferenceWork.StreamingUnknownV1.OpaqueResume
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def unchangedSkipResult (source : InnerResponseV1.Message)
    (native : core.result.Result Unit LoopSupportSkip.error.DecodeError × Slice U8) :
    core.result.Result Unit ActualInnerResponseV1.prost.error.DecodeError × InnerResponseV1.Message × Slice U8 :=
  let result := InnerResponseV1.skipResult native
  (result.1,source,result.2)

theorem unknown_from_native_skip (source : InnerResponseV1.Message) (tag : U32)
    (wire : ActualInnerResponseV1.prost.encoding.wire_type.WireType) (before : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (unknown : 5 < tag.val)
    (native : core.result.Result Unit LoopSupportSkip.error.DecodeError × Slice U8)
    (actual : LoopSupportSkip.encoding.skip_field sliceBuf (ActualInnerResponseV1.toSkipWire wire) tag before ⟨ctx.recurse_count⟩ = .ok native) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag wire before ctx = .ok (unchangedSkipResult source native) := by
  rw [unknown_dispatcher source tag wire before ctx unknown]
  unfold ActualInnerResponseV1.prost.encoding.skip_field
  rw [InnerResponseV1.scalar_adapter,actual]
  rcases native with ⟨status,after⟩
  cases status <;> rfl

/-- All actual fixed32/fixed64 outcomes, including physical underflow returning
its original source buffer; no input-fit or primitive result premise is supplied. -/
theorem unknown_fixed_source_all (source : InnerResponseV1.Message) (tag : U32) (before : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (wide : Bool)
    (unknown : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag
      (if wide then .SixtyFourBit else .ThirtyTwoBit) before ctx =
    .ok (unchangedSkipResult source (LibSignalReference.Candidate.ProstSkip.fixedResult before (if wide then 8 else 4))) := by
  apply unknown_from_native_skip source tag _ before ctx unknown
  cases wide with
  | false => exact LibSignalReference.Candidate.ProstSkip.fixed32_reference before tag ctx.recurse_count count
  | true => exact LibSignalReference.Candidate.ProstSkip.fixed64_reference before tag ctx.recurse_count count

/-- Zero source recursion budget rejects before touching the buffer. Its numeric
max-depth correspondence is a separate group-entry obligation. -/
theorem unknown_zero_recursion_source (source : InnerResponseV1.Message) (tag : U32)
    (wire : ActualInnerResponseV1.prost.encoding.wire_type.WireType) (before : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (unknown : 5 < tag.val)
    (zero : ctx.recurse_count = 0#u32) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag wire before ctx =
      .ok (unchangedSkipResult source (.Err (LibSignalReference.Candidate.ProstSkip.decodeError .RecursionLimitReached),before)) := by
  apply unknown_from_native_skip source tag wire before ctx unknown
  rw [zero]
  exact LibSignalReference.Candidate.ProstSkip.recursion_limit_first sliceBuf (ActualInnerResponseV1.toSkipWire wire) tag before

#print axioms unknown_from_native_skip
#print axioms unknown_fixed_source_all
#print axioms unknown_zero_recursion_source
end ChatResponseReference.StreamingUnknownV1
