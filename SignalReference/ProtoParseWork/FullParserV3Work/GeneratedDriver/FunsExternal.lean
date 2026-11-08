import ProtoParseWork.FullParserV3Work.GeneratedDriver.Types
import ProtoParseWork.DispatcherIntegrationWork.Generated.FunsExternal
open Aeneas Aeneas.Std Result
open ActualMessageDriver
namespace ActualMessageDriver

def toSkipBuf {B : Type} (inst : bytes.buf.buf_impl.Buf B) : LoopSupportSkip.bytes.buf.buf_impl.Buf B :=
  let base : LoopSupportSkip.bytes.buf.buf_impl.Buf B :=
    ⟨inst.remaining,inst.chunk,inst.advance,fun _ => .fail .panic⟩
  { base with get_u8 := LoopSupportSkip.bytes.buf.buf_impl.Buf.get_u8.default base }
def wireFromSkip : LoopSupportSkip.encoding.wire_type.WireType → prost.encoding.wire_type.WireType
  | .Varint => .Varint
  | .SixtyFourBit => .SixtyFourBit
  | .LengthDelimited => .LengthDelimited
  | .StartGroup => .StartGroup
  | .EndGroup => .EndGroup
  | .ThirtyTwoBit => .ThirtyTwoBit

def bytes.buf.buf_impl.Buf.has_remaining.default {Self : Type}
    (inst : bytes.buf.buf_impl.Buf Self) (buf : Self) : Result Bool := do
  let n ← inst.remaining buf
  ok (n > 0#usize)

noncomputable def prost.encoding.decode_key {B : Type}
    (inst : bytes.buf.buf_impl.Buf B) (buf : B) :
    Result ((core.result.Result (U32 × prost.encoding.wire_type.WireType) prost.error.DecodeError) × B) := do
  let (r,after) ← LoopSupportSkip.encoding.decode_key (toSkipBuf inst) buf
  let r := match r with
    | .Ok (tag,wire) => .Ok (tag,wireFromSkip wire)
    | .Err error => .Err (SignalMessageIntegration.skipError error)
  ok (r,after)
end ActualMessageDriver
