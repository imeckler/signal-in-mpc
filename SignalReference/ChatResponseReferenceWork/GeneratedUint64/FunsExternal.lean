import ChatResponseReferenceWork.GeneratedUint64.Types
import ProtoParseWork.FullParserV3Work.Skip.Replayed.WrapperReference

/- Concrete adapter to the already proved unchanged pinned varint decoder.
Only this dependency is selected opaque at extraction; no correctness axiom. -/
namespace ActualChatResponseUint64
open Aeneas Aeneas.Std

def fromSkipWire : LoopSupportSkip.encoding.wire_type.WireType → encoding.wire_type.WireType
  | .Varint => .Varint | .SixtyFourBit => .SixtyFourBit | .LengthDelimited => .LengthDelimited
  | .StartGroup => .StartGroup | .EndGroup => .EndGroup | .ThirtyTwoBit => .ThirtyTwoBit

def fromSkipKind : LoopSupportSkip.error.DecodeErrorKind → error.DecodeErrorKind
  | .LengthDelimiterTooLarge => .LengthDelimiterTooLarge
  | .InvalidVarint => .InvalidVarint
  | .RecursionLimitReached => .RecursionLimitReached
  | .InvalidWireType n => .InvalidWireType n
  | .InvalidKey n => .InvalidKey n
  | .InvalidTag => .InvalidTag
  | .UnexpectedWireType a b => .UnexpectedWireType (fromSkipWire a) (fromSkipWire b)
  | .BufferUnderflow => .BufferUnderflow
  | .DelimitedLengthExceeded => .DelimitedLengthExceeded
  | .UnexpectedEndGroupTag => .UnexpectedEndGroupTag
  | .InvalidString => .InvalidString
  | .UnexpectedTypeUrl a b => .UnexpectedTypeUrl a b
  | .Other (.Borrowed s) => .Other (.Borrowed s)
  | .Other (.Owned s) => .Other (.Owned s)

def fromSkipError (e : LoopSupportSkip.error.DecodeError) : error.DecodeError :=
  ⟨⟨fromSkipKind e.inner.description,e.inner.stack⟩⟩

def toSkipBuf {B : Type} (inst : bytes.buf.buf_impl.Buf B) : LoopSupportSkip.bytes.buf.buf_impl.Buf B :=
  let base : LoopSupportSkip.bytes.buf.buf_impl.Buf B := ⟨inst.remaining,inst.chunk,inst.advance,fun _ => .fail .panic⟩
  {base with get_u8 := LoopSupportSkip.bytes.buf.buf_impl.Buf.get_u8.default base}

noncomputable def encoding.varint.decode_varint {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (before : B) : Result ((core.result.Result U64 error.DecodeError) × B) := do
  let (r,after) ← LoopSupportSkip.encoding.varint.decode_varint (toSkipBuf inst) before
  match r with
  | .Ok n => .ok (.Ok n,after)
  | .Err error => .ok (.Err (fromSkipError error),after)
end ActualChatResponseUint64
