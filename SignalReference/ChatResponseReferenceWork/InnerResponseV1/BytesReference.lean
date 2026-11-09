import ChatResponseReferenceWork.InnerResponseV1.Replayed.Funs
import ChatResponseReferenceWork.BytesContentV1.FullReference
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerResponseV1
open ActualInnerResponseV1
abbrev byteSlice : bytes.buf.buf_impl.Buf (Slice U8) :=
  ⟨LibSignalReference.Candidate.ProstBytesBuf.remaining,
   LibSignalReference.Candidate.ProstBytesBuf.chunk,
   LibSignalReference.Candidate.ProstBytesBuf.advance⟩
theorem byte_buffer_exact : toBytesBuf byteSlice = ChatResponseReference.BytesContentV1.sliceBuf := rfl

abbrev expandedNative := toBytesBuf (fromBytesBuf ChatResponseReference.BytesContentV1.nativeBuf)
theorem copy_native_all (value : bytes.bytes.Bytes) :
    expandedNative.copy_to_bytes value value.contents.len =
      .ok (⟨ActualResponseBytesV1.ContentModel.take value.contents value.contents.len.val⟩,
        ⟨ActualResponseBytesV1.ContentModel.drop value.contents value.contents.len.val⟩) := by
  change (do
    let remaining ← Result.ok value.contents.len
    if value.contents.len > remaining then .fail .panic else do
      let chunk ← Result.ok value.contents
      let (copied,_) ← ActualResponseBytesV1.ContentModel.copySlice chunk value.contents.len
      let next ← ActualResponseBytesV1.bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf.advance value value.contents.len
      .ok (copied,next)) = _
  have hn : value.contents.len.val ≤ value.contents.length := by simpa only [Slice.len_val] using Nat.le_refl value.contents.length
  have hnot : ¬value.contents.len > value.contents.len := by scalar_tac
  simp only [bind_tc_ok,if_neg hnot,ActualResponseBytesV1.ContentModel.copySlice,if_pos hn,
    ActualResponseBytesV1.bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf.advance]

/-- The schema adapter receives a contiguous native Bytes value. Rebuilding its
three-method interface cannot change the exact copied content. -/
theorem replacement_exact (old value : bytes.bytes.Bytes) :
    (bytesAdapter bytes.bytes.Bytes.Insts.ProstEncodingBytesAdapter).sealedBytesAdapterInst.replace_with
      ChatResponseReference.BytesContentV1.nativeBuf old value = .ok value := by
  change ActualResponseBytesV1.bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with
    expandedNative old value = _
  unfold ActualResponseBytesV1.bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with
  change (do let i ← Result.ok value.contents.len
             let (copied,_) ← expandedNative.copy_to_bytes value i
             .ok copied) = _
  simp only [bind_tc_ok]
  rw [copy_native_all]
  simp only [bind_tc_ok]
  try dsimp! only
  congr 1
  cases value
  congr 1
  apply Subtype.ext
  simp only [ActualResponseBytesV1.ContentModel.take,Slice.len_val,List.take_length]
theorem bytes_adapter_ext (first second : ActualResponseBytesV1.prost.encoding.BytesAdapter bytes.bytes.Bytes)
    (equal : first.sealedBytesAdapterInst.replace_with ChatResponseReference.BytesContentV1.nativeBuf =
      second.sealedBytesAdapterInst.replace_with ChatResponseReference.BytesContentV1.nativeBuf)
    {B : Type} (inst : ActualResponseBytesV1.bytes.buf.buf_impl.Buf B)
    (wire : prost.encoding.wire_type.WireType) (old : bytes.bytes.Bytes) (before : B) (ctx : prost.encoding.DecodeContext) :
    ActualResponseBytesV1.prost.encoding.bytes.merge first inst wire old before ctx =
      ActualResponseBytesV1.prost.encoding.bytes.merge second inst wire old before ctx := by
  unfold ActualResponseBytesV1.prost.encoding.bytes.merge
  simp only [equal]

theorem bytes_source_exact (wire : prost.encoding.wire_type.WireType) (old : bytes.bytes.Bytes)
    (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    prost.encoding.bytes.merge bytes.bytes.Bytes.Insts.ProstEncodingBytesAdapter byteSlice wire old before ctx =
      ChatResponseReference.BytesContentV1.mergeField wire old before ctx := by
  unfold prost.encoding.bytes.merge
  rw [byte_buffer_exact]
  apply bytes_adapter_ext
  funext old value
  rw [replacement_exact]
  change Result.ok value = ActualResponseBytesV1.bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with
    ChatResponseReference.BytesContentV1.nativeBuf old value
  exact (ChatResponseReference.BytesContentV1.replace_bytes old value).symm

/-- The dispatcher Byte adapter reaches the already proved actual field merger,
including exact native decoder errors/suffixes and old/replacement contents. -/
theorem bytes_full_reference (old : bytes.bytes.Bytes) (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    ∃ decoded after,
      LibSignalReference.Candidate.ProstSkipBuf.PrefixPost before decoded after ∧
      LibSignalReference.Candidate.ProstSkipBuf.ErrorPost before decoded after ∧
      prost.encoding.bytes.merge bytes.bytes.Bytes.Insts.ProstEncodingBytesAdapter byteSlice .LengthDelimited old before ctx =
        .ok (ChatResponseReference.BytesContentV1.bytesResult old decoded after) := by
  rw [bytes_source_exact]
  exact ChatResponseReference.BytesContentV1.bytes_full_reference before old ctx
#print axioms byte_buffer_exact
#print axioms copy_native_all
#print axioms replacement_exact
#print axioms bytes_source_exact
#print axioms bytes_full_reference
end ChatResponseReference.InnerResponseV1
