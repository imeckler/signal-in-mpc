import ChatResponseReferenceWork.RepeatedStringV1.Replayed.Funs
import ChatResponseReferenceWork.StringContentV3.FullStringReference
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.RepeatedStringV1
open ActualRepeatedStringV1
abbrev Value := ActualStringContentV3.String
abbrev sliceBuf : bytes.buf.buf_impl.Buf (Slice U8) :=
  ⟨LibSignalReference.Candidate.ProstBytesBuf.remaining,
   LibSignalReference.Candidate.ProstBytesBuf.chunk,
   LibSignalReference.Candidate.ProstBytesBuf.advance⟩
theorem adapter_exact : toStringBuf sliceBuf = ChatResponseReference.StringContentV3.sliceBuf := rfl

def appendResult (old : alloc.vec.Vec Value)
    (result : core.result.Result Unit error.DecodeError × Value × Slice U8) :
    Result (core.result.Result Unit error.DecodeError × alloc.vec.Vec Value × Slice U8) :=
  match result.1 with
  | .Err error => .ok (.Err error,old,result.2.2)
  | .Ok _ => do
    let next ← alloc.vec.Vec.push old result.2.1
    .ok (.Ok (),next,result.2.2)

theorem repeated_wire_error (wire : encoding.wire_type.WireType) (old : alloc.vec.Vec Value)
    (before : Slice U8) (ctx : encoding.DecodeContext) (hw : wire ≠ .LengthDelimited) :
    encoding.string.merge_repeated sliceBuf wire old before ctx =
      .ok (.Err (ChatResponseReference.StringContentV3.decodeError (.UnexpectedWireType wire .LengthDelimited)),old,before) := by
  cases wire <;> first | exact False.elim (hw rfl) | rfl

/-- Exact source continuation. Failed String merge never appends; successful
merge executes Vec.push, preserving its allocation/failure/divergence effects. -/
theorem repeated_after_string (before : Slice U8) (old : alloc.vec.Vec Value)
    (ctx : encoding.DecodeContext)
    (result : core.result.Result Unit error.DecodeError × Value × Slice U8)
    (run : ActualStringContentV3.encoding.string.merge ChatResponseReference.StringContentV3.sliceBuf
      .LengthDelimited (alloc.vec.Vec.new U8) before ctx = .ok result) :
    encoding.string.merge_repeated sliceBuf .LengthDelimited old before ctx = appendResult old result := by
  unfold encoding.string.merge_repeated
  have wire : encoding.wire_type.check_wire_type .LengthDelimited .LengthDelimited = .ok (.Ok ()) := rfl
  rw [wire]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    alloc.string.String.Insts.CoreDefaultDefault.default]
  unfold encoding.string.merge
  rw [adapter_exact,run]
  rcases result with ⟨r,value,suffix⟩
  cases r <;> rfl

/-- Total all-outcomes contiguous repeated-header primitive, reusing the actual
String/varint/copier composition. No primitive correctness/termination premise.
The append's allocation effect remains before any owned-error observation. -/
theorem repeated_full_reference (before : Slice U8) (old : alloc.vec.Vec Value) (ctx : encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstSkipBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstSkipBuf.ErrorPost before decoded after ∧
      encoding.string.merge_repeated sliceBuf .LengthDelimited old before ctx =
        appendResult old (ChatResponseReference.StringContentV3.stringResult
          (ChatResponseReference.StringContentV3.bytesResult (alloc.vec.Vec.new U8) decoded after)) := by
  obtain ⟨decoded,after,prefixPost,errorPost,run⟩ := ChatResponseReference.StringContentV3.string_full_reference before (alloc.vec.Vec.new U8) ctx
  exact ⟨decoded,after,prefixPost,errorPost,repeated_after_string before old ctx _ run⟩

/-- Old header order is retained and the new successful header is appended. -/
theorem success_order (old : alloc.vec.Vec Value) (value : Value) (suffix : Slice U8)
    (bound : old.val.length < Usize.max) :
    ∃ next, appendResult old (.Ok (),value,suffix) = .ok (.Ok (),next,suffix) ∧
      next.val = old.val ++ [value] := by
  obtain ⟨next,run,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec old value bound)
  exact ⟨next,by simp only [appendResult,run,bind_tc_ok],contents⟩
#print axioms adapter_exact
#print axioms repeated_wire_error
#print axioms repeated_after_string
#print axioms repeated_full_reference
#print axioms success_order
end ChatResponseReference.RepeatedStringV1
