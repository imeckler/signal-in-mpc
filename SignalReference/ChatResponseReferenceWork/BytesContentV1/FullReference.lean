import ChatResponseReferenceWork.BytesContentV1.Reference
import ProtoParseWork.FullParserV3Work.Skip.Replayed.Consumption
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.BytesContentV1
open ActualResponseBytesV1


noncomputable abbrev mergeField := prost.encoding.bytes.merge bytes.bytes.Bytes.Insts.ProstEncodingBytesAdapter sliceBuf

def decodeError (kind : prost.error.DecodeErrorKind) : prost.error.DecodeError :=
  ⟨⟨kind,alloc.vec.Vec.new (Str×Str)⟩⟩
theorem slice_adapter : toSkipBuf sliceBuf = LibSignalReference.Candidate.ProstSkipBuf.sliceBuf := rfl

theorem bytes_wire_error (wire : prost.encoding.wire_type.WireType)
    (old : bytes.bytes.Bytes) (before : Slice U8) (ctx : prost.encoding.DecodeContext)
    (hw : wire ≠ .LengthDelimited) :
    mergeField wire old before ctx =
      .ok (.Err (decodeError (.UnexpectedWireType wire .LengthDelimited)),old,before) := by
  cases wire <;> first | exact False.elim (hw rfl) | rfl

theorem bytes_decode_error (before after : Slice U8) (old : bytes.bytes.Bytes)
    (error : LoopSupportSkip.error.DecodeError) (ctx : prost.encoding.DecodeContext)
    (hd : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (.Err error,after)) :
    mergeField .LengthDelimited old before ctx =
      .ok (.Err (fromSkipError error),old,after) := by
  unfold mergeField prost.encoding.bytes.merge
  have hw : prost.encoding.wire_type.check_wire_type .LengthDelimited .LengthDelimited = .ok (.Ok ()) := rfl
  rw [hw]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  unfold prost.encoding.varint.decode_varint
  rw [slice_adapter,hd]
  rfl

private theorem remaining_u64 (view : Slice U8) :
    (UScalar.cast .U64 view.len).val = view.length := by
  rw [UScalar.cast_val_mod_pow_greater_numBits_eq .U64 view.len (by
    simp only [UScalarTy.Usize_numBits_eq,UScalarTy.U64_numBits_eq]
    cases System.Platform.numBits_eq <;> omega)]
  exact Slice.len_val view

theorem bytes_underflow (before after : Slice U8) (old : bytes.bytes.Bytes)
    (value : U64) (ctx : prost.encoding.DecodeContext)
    (hd : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (.Ok value,after))
    (hn : after.length < value.val) :
    mergeField .LengthDelimited old before ctx =
      .ok (.Err (decodeError .BufferUnderflow),old,after) := by
  unfold mergeField prost.encoding.bytes.merge
  have hw : prost.encoding.wire_type.check_wire_type .LengthDelimited .LengthDelimited = .ok (.Ok ()) := rfl
  rw [hw]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  unfold prost.encoding.varint.decode_varint
  rw [slice_adapter,hd]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  change (do let i1 ← lift (UScalar.cast .U64 after.len)
             if value > i1 then _ else _) = _
  have hl := remaining_u64 after
  have hc : value > UScalar.cast .U64 after.len := by scalar_tac
  simp only [lift,bind_tc_ok,if_pos hc]
  rfl
theorem bytes_success (before after : Slice U8) (old : bytes.bytes.Bytes)
    (value : U64) (ctx : prost.encoding.DecodeContext)
    (hd : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (.Ok value,after))
    (hn : value.val ≤ after.length) :
    mergeField .LengthDelimited old before ctx =
      .ok (.Ok (),⟨ContentModel.take after (UScalar.cast .Usize value).val⟩,
        LibSignalReference.Candidate.ProstBytesBuf.drop after (UScalar.cast .Usize value).val) := by
  unfold mergeField prost.encoding.bytes.merge
  have hw : prost.encoding.wire_type.check_wire_type .LengthDelimited .LengthDelimited = .ok (.Ok ()) := rfl
  rw [hw]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  unfold prost.encoding.varint.decode_varint
  rw [slice_adapter,hd]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  change (do let i1 ← lift (UScalar.cast .U64 after.len)
             if value > i1 then _ else _) = _
  have hl := remaining_u64 after
  have hc : ¬value > UScalar.cast .U64 after.len := by scalar_tac
  simp only [lift,bind_tc_ok,if_neg hc]
  have hbound := after.len.hBounds
  rw [Slice.len_val] at hbound
  have hv : (UScalar.cast .Usize value).val = value.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq .Usize value (by omega)
  have hcopy := slice_copy after (UScalar.cast .Usize value) (by rw [hv]; exact hn)
  change (do let (b,buf2) ← sliceBuf.copy_to_bytes after (UScalar.cast .Usize value)
             let value1 ← bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with nativeBuf old b
             .ok ((core.result.Result.Ok () : core.result.Result Unit prost.error.DecodeError),value1,buf2)) = _
  rw [hcopy]
  simp only [bind_tc_ok]
  try dsimp! only
  rw [replace_bytes]
  rfl

theorem payload_length (after : Slice U8) (value : U64) (hn : value.val ≤ after.length) :
    (UScalar.cast .Usize value).val = value.val := by
  have hbound := after.len.hBounds
  rw [Slice.len_val] at hbound
  exact UScalar.cast_val_mod_pow_of_inBounds_eq .Usize value (by omega)

def bytesResult (old : bytes.bytes.Bytes)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (after : Slice U8) :
    core.result.Result Unit prost.error.DecodeError × bytes.bytes.Bytes × Slice U8 :=
  match decoded with
  | .Err error => (.Err (fromSkipError error),old,after)
  | .Ok value => if value.val ≤ after.length then
      (.Ok (),⟨ContentModel.take after (UScalar.cast .Usize value).val⟩,
        LibSignalReference.Candidate.ProstBytesBuf.drop after value.val)
    else (.Err (decodeError .BufferUnderflow),old,after)

theorem bytes_from_decode (before after : Slice U8) (old : bytes.bytes.Bytes)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError) (ctx : prost.encoding.DecodeContext)
    (hd : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (decoded,after)) :
    mergeField .LengthDelimited old before ctx =
      .ok (bytesResult old decoded after) := by
  cases decoded with
  | Err error => exact bytes_decode_error before after old error ctx hd
  | Ok value =>
    by_cases hn : value.val ≤ after.length
    · simpa only [bytesResult,if_pos hn,payload_length after value hn] using bytes_success before after old value ctx hd hn
    · simpa only [bytesResult,if_neg hn] using bytes_underflow before after old value ctx hd (by omega)

/-- Total contiguous source composition, no varint/termination/put correctness
premise. Exact decoder error, prefix and suffix observations are retained. -/
theorem bytes_full_reference (before : Slice U8) (old : bytes.bytes.Bytes) (ctx : prost.encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstSkipBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstSkipBuf.ErrorPost before decoded after ∧
      mergeField .LengthDelimited old before ctx =
        .ok (bytesResult old decoded after) := by
  obtain ⟨decoded,after,hd,hp,he⟩ := LibSignalReference.Candidate.ProstSkipBuf.decode_full_reference before
  exact ⟨decoded,after,hp,he,bytes_from_decode before after old decoded ctx hd⟩
#print axioms bytes_wire_error
#print axioms bytes_decode_error
#print axioms bytes_underflow
#print axioms bytes_success
#print axioms payload_length
#print axioms bytes_full_reference
end ChatResponseReference.BytesContentV1
