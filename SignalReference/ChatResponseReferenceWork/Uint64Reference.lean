import ChatResponseReferenceWork.GeneratedUint64.Funs
import ProtoParseWork.FullParserV3Work.Skip.Replayed.Consumption
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference
open ActualChatResponseUint64
set_option maxHeartbeats 2000000

/-- Actual uint64 primitive's contiguous Buf instantiation; the mutable/default
get_u8 forwarding is definitionally the accepted contiguous decoder adapter. -/
def sliceBuf : bytes.buf.buf_impl.Buf (Slice U8) :=
  ⟨LibSignalReference.Candidate.ProstSkipBuf.remaining,LibSignalReference.Candidate.ProstSkipBuf.chunk,
   LibSignalReference.Candidate.ProstSkipBuf.advance⟩
theorem slice_adapter : toSkipBuf sliceBuf = LibSignalReference.Candidate.ProstSkipBuf.sliceBuf := rfl

def decodeError (kind : error.DecodeErrorKind) : error.DecodeError := ⟨⟨kind,alloc.vec.Vec.new (Str×Str)⟩⟩

def mergeResult (old : U64) (r : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :
    core.result.Result Unit error.DecodeError × U64 × Slice U8 :=
  match r with
  | .Ok value => (.Ok (),value,after)
  | .Err e => (.Err (fromSkipError e),old,after)

/-- Actual source rejects a wrong wire before any decoder/buffer operation,
retaining both the old scalar and the exact original suffix. -/
theorem uint64_wire_error {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (wire : encoding.wire_type.WireType) (old : U64) (before : B) (ctx : encoding.DecodeContext)
    (hw : wire ≠ .Varint) : encoding.uint64.merge inst wire old before ctx =
    .ok (.Err (decodeError (.UnexpectedWireType wire .Varint)),old,before) := by
  cases wire <;> first | exact False.elim (hw rfl) | rfl

/-- Exact actual generated uint64 continuation after the already proved actual
varint call: no uint32 truncation, and no replacement on decoder error. -/
theorem uint64_after (before after : Slice U8) (old : U64) (ctx : encoding.DecodeContext)
    (r : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (hd : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (r,after)) :
    encoding.uint64.merge sliceBuf .Varint old before ctx = .ok (mergeResult old r after) := by
  unfold encoding.uint64.merge
  have hw : encoding.wire_type.check_wire_type .Varint .Varint = .ok (.Ok ()) := rfl
  rw [hw]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  unfold encoding.varint.decode_varint
  rw [slice_adapter,hd]
  cases r <;> rfl

/-- Complete actual uint64 merger reference, including full-width values,
malformed/overflow rejection, exact fast/slow failure suffix and old-value
retention. No caller primitive correctness or termination premise. -/
theorem uint64_full_reference (before : Slice U8) (old : U64) (ctx : encoding.DecodeContext) :
    ∃ result after,
      LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (result,after) ∧
      LibSignalReference.Candidate.ProstSkipBuf.PrefixPost before result after ∧
      LibSignalReference.Candidate.ProstSkipBuf.ErrorPost before result after ∧
      encoding.uint64.merge sliceBuf .Varint old before ctx = .ok (mergeResult old result after) := by
  obtain ⟨result,after,hd,hp,he⟩ := LibSignalReference.Candidate.ProstSkipBuf.decode_full_reference before
  exact ⟨result,after,hd,hp,he,uint64_after before after old ctx result hd⟩

#print axioms slice_adapter
#print axioms uint64_wire_error
#print axioms uint64_after
#print axioms uint64_full_reference
end ChatResponseReference
