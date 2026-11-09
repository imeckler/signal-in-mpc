import ChatResponseReferenceWork.InnerResponseV1.BufferBridge
import ProtoParseWork.DispatcherIntegrationWork.SkipReplay.Funs
open Aeneas Aeneas.Std Result
namespace ActualInnerResponseV1
def toSkipWire : prost.encoding.wire_type.WireType → LoopSupportSkip.encoding.wire_type.WireType
  | .Varint => .Varint | .SixtyFourBit => .SixtyFourBit | .LengthDelimited => .LengthDelimited
  | .StartGroup => .StartGroup | .EndGroup => .EndGroup | .ThirtyTwoBit => .ThirtyTwoBit
noncomputable def prost.encoding.skip_field {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (wire : prost.encoding.wire_type.WireType) (tag : U32) (before : B) (ctx : prost.encoding.DecodeContext) :
    Result (core.result.Result Unit prost.error.DecodeError × B) := do
  let (r,after) ← LoopSupportSkip.encoding.skip_field (ActualResponseBytesV1.toSkipBuf (toBytesBuf inst))
    (toSkipWire wire) tag before ⟨ctx.recurse_count⟩
  match r with
  | .Ok unit => .ok (.Ok unit,after)
  | .Err error => .ok (.Err (ActualResponseBytesV1.fromSkipError error),after)
end ActualInnerResponseV1
