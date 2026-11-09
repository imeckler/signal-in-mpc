import ChatResponseReferenceWork.InnerScanV1.Replayed.Types
import ProtoParseWork.DispatcherIntegrationWork.SkipReplay.Funs
open Aeneas Aeneas.Std Result
namespace ActualInnerScanV1
def toSkipBuf {B : Type} (inst : bytes.buf.buf_impl.Buf B) : LoopSupportSkip.bytes.buf.buf_impl.Buf B :=
  let base : LoopSupportSkip.bytes.buf.buf_impl.Buf B := ⟨inst.remaining,inst.chunk,inst.advance,fun _ => .fail .undef⟩
  {base with get_u8 := LoopSupportSkip.bytes.buf.buf_impl.Buf.get_u8.default base}
def bytes.buf.buf_impl.Buf.has_remaining.default {B : Type} (inst : bytes.buf.buf_impl.Buf B) (buf : B) : Result Bool := do
  let count ← inst.remaining buf
  .ok (count > 0#usize)
noncomputable def prost.encoding.decode_key {B : Type} (inst : bytes.buf.buf_impl.Buf B) (before : B) :
    Result (core.result.Result (U32 × prost.encoding.wire_type.WireType) prost.error.DecodeError × B) := do
  let (r,after) ← LoopSupportSkip.encoding.decode_key (toSkipBuf inst) before
  match r with
  | .Ok (tag,wire) => .ok (.Ok (tag,ActualResponseBytesV1.fromSkipWire wire),after)
  | .Err error => .ok (.Err (ActualResponseBytesV1.fromSkipError error),after)
def core.result.Result.map {T E U F : Type} (inst : core.ops.function.FnOnce F T U)
    (result : core.result.Result T E) (closure : F) : Result (core.result.Result U E) :=
  match result with
  | .Ok value => do let next ← inst.call_once closure value; .ok (.Ok next)
  | .Err error => .ok (.Err error)
end ActualInnerScanV1
