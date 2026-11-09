import ChatResponseReferenceWork.InnerResponseV1.Replayed.Types
import ChatResponseReferenceWork.StringContentV3.Generated.Funs
import ChatResponseReferenceWork.RepeatedStringV1.Replayed.Funs
open Aeneas Aeneas.Std Result
namespace ActualInnerResponseV1

def toStringWire : prost.encoding.wire_type.WireType → ActualStringContentV3.encoding.wire_type.WireType
  | .Varint => .Varint | .SixtyFourBit => .SixtyFourBit | .LengthDelimited => .LengthDelimited
  | .StartGroup => .StartGroup | .EndGroup => .EndGroup | .ThirtyTwoBit => .ThirtyTwoBit

def fromStringKind : ActualStringContentV3.error.DecodeErrorKind → prost.error.DecodeErrorKind
  | .LengthDelimiterTooLarge => .LengthDelimiterTooLarge | .InvalidVarint => .InvalidVarint
  | .RecursionLimitReached => .RecursionLimitReached | .InvalidWireType n => .InvalidWireType n
  | .InvalidKey n => .InvalidKey n | .InvalidTag => .InvalidTag
  | .UnexpectedWireType a b => .UnexpectedWireType (fromStringWire a) (fromStringWire b)
  | .BufferUnderflow => .BufferUnderflow | .DelimitedLengthExceeded => .DelimitedLengthExceeded
  | .UnexpectedEndGroupTag => .UnexpectedEndGroupTag | .InvalidString => .InvalidString
  | .UnexpectedTypeUrl a b => .UnexpectedTypeUrl a b
  | .Other (.Borrowed s) => .Other (.Borrowed s) | .Other (.Owned s) => .Other (.Owned s)
where fromStringWire : ActualStringContentV3.encoding.wire_type.WireType → prost.encoding.wire_type.WireType
  | .Varint => .Varint | .SixtyFourBit => .SixtyFourBit | .LengthDelimited => .LengthDelimited
  | .StartGroup => .StartGroup | .EndGroup => .EndGroup | .ThirtyTwoBit => .ThirtyTwoBit

def fromStringError (error : ActualStringContentV3.error.DecodeError) : prost.error.DecodeError :=
  ⟨⟨fromStringKind error.inner.description,error.inner.stack⟩⟩
def stringBuf {B : Type} (inst : bytes.buf.buf_impl.Buf B) : ActualStringContentV3.bytes.buf.buf_impl.Buf B :=
  ⟨inst.remaining,inst.chunk,inst.advance,fun s n => .ok ⟨s,n⟩⟩
def repeatedBuf {B : Type} (inst : bytes.buf.buf_impl.Buf B) : ActualRepeatedStringV1.bytes.buf.buf_impl.Buf B :=
  ⟨inst.remaining,inst.chunk,inst.advance⟩
def stringCtx (ctx : prost.encoding.DecodeContext) : ActualStringContentV3.encoding.DecodeContext := ⟨ctx.recurse_count⟩

/-- Execute the actual separately proved U8 DropGuard clear on every error,
including wrong wire, before returning to the generated field callback. -/
noncomputable def prost.encoding.string.merge {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (wire : prost.encoding.wire_type.WireType) (old : String) (before : B) (ctx : prost.encoding.DecodeContext) :
    Result (core.result.Result Unit prost.error.DecodeError × String × B) := do
  let (r,value,after) ← ActualStringContentV3.encoding.string.merge (stringBuf inst) (toStringWire wire) old before (stringCtx ctx)
  match r with
  | .Ok unit => .ok (.Ok unit,value,after)
  | .Err error =>
    let (cleared,_) ← ActualStringContentV3.reference_Impl_0.drop value
    .ok (.Err (fromStringError error),cleared,after)

noncomputable def prost.encoding.string.merge_repeated {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (wire : prost.encoding.wire_type.WireType) (old : alloc.vec.Vec String) (before : B) (ctx : prost.encoding.DecodeContext) :
    Result (core.result.Result Unit prost.error.DecodeError × alloc.vec.Vec String × B) := do
  let (r,value,after) ← ActualRepeatedStringV1.encoding.string.merge_repeated (repeatedBuf inst) (toStringWire wire) old before (stringCtx ctx)
  match r with
  | .Ok unit => .ok (.Ok unit,value,after)
  | .Err error => .ok (.Err (fromStringError error),value,after)
end ActualInnerResponseV1
