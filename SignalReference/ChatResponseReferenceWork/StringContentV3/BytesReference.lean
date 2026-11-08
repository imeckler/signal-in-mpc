import ChatResponseReferenceWork.StringContentV3.CopierReference
import ProtoParseWork.FullParserV3Work.Skip.Replayed.Consumption
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.StringContentV3
open ActualStringContentV3
open ChatResponseReference.ContiguousPut

def decodeError (kind : error.DecodeErrorKind) : error.DecodeError :=
  ⟨⟨kind,alloc.vec.Vec.new (Str×Str)⟩⟩
theorem slice_adapter : toSkipBuf sliceBuf = LibSignalReference.Candidate.ProstSkipBuf.sliceBuf := rfl

theorem bytes_wire_error (wire : encoding.wire_type.WireType)
    (old : alloc.vec.Vec U8) (before : Slice U8) (ctx : encoding.DecodeContext)
    (hw : wire ≠ .LengthDelimited) :
    encoding.bytes.merge_one_copy.partial_Fun_293 sliceBuf wire old before ctx =
      .ok (.Err (decodeError (.UnexpectedWireType wire .LengthDelimited)),old,before) := by
  cases wire <;> first | exact False.elim (hw rfl) | rfl

theorem bytes_decode_error (before after : Slice U8) (old : alloc.vec.Vec U8)
    (error : LoopSupportSkip.error.DecodeError) (ctx : encoding.DecodeContext)
    (hd : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (.Err error,after)) :
    encoding.bytes.merge_one_copy.partial_Fun_293 sliceBuf .LengthDelimited old before ctx =
      .ok (.Err (fromSkipError error),old,after) := by
  unfold encoding.bytes.merge_one_copy.partial_Fun_293
  have hw : encoding.wire_type.check_wire_type .LengthDelimited .LengthDelimited = .ok (.Ok ()) := rfl
  rw [hw]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  unfold encoding.varint.decode_varint
  rw [slice_adapter,hd]
  rfl

private theorem remaining_u64 (view : Slice U8) :
    (UScalar.cast .U64 view.len).val = view.length := by
  rw [UScalar.cast_val_mod_pow_greater_numBits_eq .U64 view.len (by
    simp only [UScalarTy.Usize_numBits_eq,UScalarTy.U64_numBits_eq]
    cases System.Platform.numBits_eq <;> omega)]
  exact Slice.len_val view

theorem bytes_underflow (before after : Slice U8) (old : alloc.vec.Vec U8)
    (value : U64) (ctx : encoding.DecodeContext)
    (hd : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (.Ok value,after))
    (hn : after.length < value.val) :
    encoding.bytes.merge_one_copy.partial_Fun_293 sliceBuf .LengthDelimited old before ctx =
      .ok (.Err (decodeError .BufferUnderflow),old,after) := by
  unfold encoding.bytes.merge_one_copy.partial_Fun_293
  have hw : encoding.wire_type.check_wire_type .LengthDelimited .LengthDelimited = .ok (.Ok ()) := rfl
  rw [hw]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  unfold encoding.varint.decode_varint
  rw [slice_adapter,hd]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  change (do let i1 ← lift (UScalar.cast .U64 after.len)
             if value > i1 then _ else _) = _
  have hl := remaining_u64 after
  have hc : value > UScalar.cast .U64 after.len := by scalar_tac
  simp only [lift,bind_tc_ok,if_pos hc]
  rfl
theorem bytes_success (before after : Slice U8) (old : alloc.vec.Vec U8)
    (value : U64) (ctx : encoding.DecodeContext)
    (hd : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (.Ok value,after))
    (hn : value.val ≤ after.length) :
    encoding.bytes.merge_one_copy.partial_Fun_293 sliceBuf .LengthDelimited old before ctx =
      .ok (.Ok (),LibSignalReference.Candidate.ProstVecAdapter.fromSlice (view ⟨after,UScalar.cast .Usize value⟩),
        LibSignalReference.Candidate.ProstBytesBuf.drop after (view ⟨after,UScalar.cast .Usize value⟩).length) := by
  unfold encoding.bytes.merge_one_copy.partial_Fun_293
  have hw : encoding.wire_type.check_wire_type .LengthDelimited .LengthDelimited = .ok (.Ok ()) := rfl
  rw [hw]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  unfold encoding.varint.decode_varint
  rw [slice_adapter,hd]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  change (do let i1 ← lift (UScalar.cast .U64 after.len)
             if value > i1 then _ else _) = _
  have hl := remaining_u64 after
  have hc : ¬value > UScalar.cast .U64 after.len := by scalar_tac
  simp only [lift,bind_tc_ok,if_neg hc]
  unfold bytes.buf.buf_impl.Buf.take.partial_Fun_292.default bytes.buf.take.new.partial_Fun_296
  simp only [bind_tc_ok]
  dsimp! only
  simp only [bind_tc_ok]
  dsimp! only
  rw [replace_slice_reference]
  simp only [bind_tc_ok]
  dsimp! only

theorem payload_length (after : Slice U8) (value : U64) (hn : value.val ≤ after.length) :
    (view ⟨after,UScalar.cast .Usize value⟩).length = value.val := by
  have hbound := after.len.hBounds
  rw [Slice.len_val] at hbound
  have hv : (UScalar.cast .Usize value).val = value.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq .Usize value (by omega)
  rw [view_length,hv,Nat.min_eq_left hn]

def bytesResult (old : alloc.vec.Vec U8)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :
    core.result.Result Unit error.DecodeError × alloc.vec.Vec U8 × Slice U8 :=
  match decoded with
  | .Err error => (.Err (fromSkipError error),old,after)
  | .Ok value => if value.val ≤ after.length then
      (.Ok (),LibSignalReference.Candidate.ProstVecAdapter.fromSlice (view ⟨after,UScalar.cast .Usize value⟩),
        LibSignalReference.Candidate.ProstBytesBuf.drop after value.val)
    else (.Err (decodeError .BufferUnderflow),old,after)

theorem bytes_from_decode (before after : Slice U8) (old : alloc.vec.Vec U8)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (ctx : encoding.DecodeContext)
    (hd : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (decoded,after)) :
    encoding.bytes.merge_one_copy.partial_Fun_293 sliceBuf .LengthDelimited old before ctx =
      .ok (bytesResult old decoded after) := by
  cases decoded with
  | Err error => exact bytes_decode_error before after old error ctx hd
  | Ok value =>
    by_cases hn : value.val ≤ after.length
    · simpa only [bytesResult,if_pos hn,payload_length after value hn] using bytes_success before after old value ctx hd hn
    · simpa only [bytesResult,if_neg hn] using bytes_underflow before after old value ctx hd (by omega)

/-- Total contiguous source composition, no varint/termination/put correctness
premise. Exact decoder error, prefix and suffix observations are retained. -/
theorem bytes_full_reference (before : Slice U8) (old : alloc.vec.Vec U8) (ctx : encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstSkipBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstSkipBuf.ErrorPost before decoded after ∧
      encoding.bytes.merge_one_copy.partial_Fun_293 sliceBuf .LengthDelimited old before ctx =
        .ok (bytesResult old decoded after) := by
  obtain ⟨decoded,after,hd,hp,he⟩ := LibSignalReference.Candidate.ProstSkipBuf.decode_full_reference before
  exact ⟨decoded,after,hp,he,bytes_from_decode before after old decoded ctx hd⟩
#print axioms bytes_wire_error
#print axioms bytes_decode_error
#print axioms bytes_underflow
#print axioms bytes_success
#print axioms payload_length
#print axioms bytes_full_reference
end ChatResponseReference.StringContentV3
