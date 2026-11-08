import ChatResponseReferenceWork.StringContentV3.Generated.Types
import ChatResponseReferenceWork.StringContentV3.ContiguousPut.GeneratedReference
import ChatResponseReferenceWork.Utf8Spec
import ProtoParseWork.FullParserV3Work.Skip.Replayed.WrapperReference
open Aeneas Aeneas.Std Result
namespace ActualStringContentV3
open ChatResponseReference.TypedLoanProjection
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

/-- Byte-content interpretation of owned Rust String. Error-time invalid bytes
are retained internally; owned Err observation must erase them explicitly. -/
abbrev String := alloc.vec.Vec U8
def alloc.string.String.as_mut_vec (value : String) : Result ((alloc.vec.Vec U8) × (alloc.vec.Vec U8 → String)) :=
  .ok (value,id)
/-- Executable UTF8 grammar boundary; no claim about std's unsafe pointer body. -/
def core.str.converts.from_utf8 (value : Slice U8) : Result (core.result.Result Str Unit) :=
  .ok (if ChatResponseReference.Utf8.accepts (value.val.map (fun b => b.bv)) then .Ok value else .Err ())
def alloc.vec.Vec.reserve {T : Type} (A : Type) :=
  ProstAdapterCandidate.alloc.vec.Vec.reserve (T:=T) A
def alloc.vec.Vec.clear {T : Type} (_ : Type) (_ : alloc.vec.Vec T) : Result (alloc.vec.Vec T) :=
  .ok (alloc.vec.Vec.new T)
def bytes.buf.buf_impl.Buf.partial_TraitDecl_28.Blanket.remaining {B : Type}
    (inst : bytes.buf.buf_impl.Buf B) := inst.remaining
def bytes.buf.buf_impl.Buf.partial_TraitDecl_28.Blanket.chunk {B : Type}
    (inst : bytes.buf.buf_impl.Buf B) := inst.chunk
def bytes.buf.buf_impl.Buf.partial_TraitDecl_28.Blanket.advance {B : Type}
    (inst : bytes.buf.buf_impl.Buf B) : LoanOp B Usize := actualAdvance ⟨inst.remaining,inst.chunk,inst.advance⟩
def takeAdvanceRaw {B : Type} (inst : bytes.buf.buf_impl.Buf.partial_TraitDecl_28 B)
    (s : bytes.buf.take.Take.partial_Type_37 B) (n : Usize) :
    Result ((bytes.buf.take.Take.partial_Type_37 B) × (bytes.buf.take.Take.partial_Type_37 B → bytes.buf.take.Take.partial_Type_37 B)) := do
  massert (n ≤ s.limit)
  let inner ← inst.advance s.inner n
  let limit ← UScalar.sub s.limit n
  let next : bytes.buf.take.Take.partial_Type_37 B := ⟨inner,limit⟩
  .ok (next,fun final => {next with inner := final.inner})
def bytes.buf.buf_impl.Buf.partial_TraitDecl_29.Blanket.advance {B : Type}
    (inst : bytes.buf.buf_impl.Buf.partial_TraitDecl_28 B) :
    LoanOp (bytes.buf.take.Take.partial_Type_37 B) Usize where
  raw := takeAdvanceRaw inst
  observed := fun s n => do let (next,restore) ← takeAdvanceRaw inst s n; .ok (restore next)
  correspondence := fun _ _ => rfl
def bytes.buf.buf_impl.Buf.partial_TraitDecl_29.Blanket.chunk {B : Type}
    (inst : bytes.buf.buf_impl.Buf.partial_TraitDecl_28 B) (s : bytes.buf.take.Take.partial_Type_37 B) : Result (Slice U8) := do
  let chunk ← inst.chunk s.inner
  .ok (ProstBytesCandidate.ContentModel.take chunk s.limit.val)
def bytes.buf.buf_impl.Buf.partial_TraitDecl_29.Blanket.remaining {B : Type}
    (inst : bytes.buf.buf_impl.Buf.partial_TraitDecl_28 B) (s : bytes.buf.take.Take.partial_Type_37 B) : Result Usize := do
  let n ← inst.remaining s.inner
  .ok (core.cmp.impls.OrdUsize.min n s.limit)
/-- Precisely scoped contiguous copier. Other receiver types fail closed. Final
reference statements fix the canonical slice dictionary, not arbitrary Buf. -/
noncomputable def alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put {B : Type}
    (_ : bytes.buf.buf_impl.Buf.partial_TraitDecl_29 B) (value : alloc.vec.Vec U8)
    (src : bytes.buf.take.Take.partial_Type_37 B) : Result ((alloc.vec.Vec U8) × (bytes.buf.take.Take.partial_Type_37 B)) := by
  classical
  exact if h : B = Slice U8 then by
    subst B
    exact do
      let (value1,after) ← ContiguousPutOneStep.put_contiguous_one_step value src.inner src.limit
      .ok (value1,{src with inner := after})
    else .fail .panic
end ActualStringContentV3
