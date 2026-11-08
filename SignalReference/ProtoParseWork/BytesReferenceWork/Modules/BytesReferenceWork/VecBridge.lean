import BytesReferenceWork.BytesReference
import BytesReferenceWork.VecReference

namespace LibSignalReference.Candidate.ProstBytes
open Aeneas Aeneas.Std ProstBytesCandidate
open LibSignalReference.Candidate.ProstBytesBuf LibSignalReference.Candidate.ProstVecAdapter
set_option maxHeartbeats 500000

/-- Same remaining/chunk/advance methods projected between two extraction-local
Buf dictionary types; has_remaining is the actual default (Bytes does not override it). -/
def adaptBuf {B : Type} (inst : bytes.buf.buf_impl.Buf B) :
    ProstAdapterCandidate.bytes.buf.buf_impl.Buf B where
  remaining := inst.remaining
  chunk := inst.chunk
  advance := inst.advance
  has_remaining := fun buf => do
    let n ← inst.remaining buf
    Result.ok (n > 0#usize)

/-- Preserve all unobserved dictionary fields as parameters; no dummy append
implementation or axiom is introduced. Only replace_with is fixed to the actual
extracted Vec<u8> function. Every parsing theorem is independent of the rest. -/
def actualReplace {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (old : alloc.vec.Vec U8) (buf : B) : Result (alloc.vec.Vec U8) :=
  ProstAdapterCandidate.alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.replace_with
    (adaptBuf inst) old buf

def withActualReplace (unused : encoding.sealed.BytesAdapter (alloc.vec.Vec U8)) :
    encoding.BytesAdapter (alloc.vec.Vec U8) :=
  ⟨{ unused with replace_with := actualReplace }⟩

private def emptySlice : Slice U8 := ⟨[],by simp⟩

private theorem content_drop_all (view : Slice U8) :
    ContentModel.drop view view.length = emptySlice := by
  apply Subtype.ext
  exact List.drop_length

theorem actual_replace_snapshot (old : alloc.vec.Vec U8) (view : Slice U8) :
    ProstAdapterCandidate.alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.replace_with
      (adaptBuf bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf) old ⟨view⟩ =
      Result.ok (fromSlice view) := by
  by_cases he : view.length = 0
  · have hv : view = emptySlice := by
      apply Subtype.ext
      exact List.eq_nil_iff_length_eq_zero.mpr he
    subst view
    exact replace_empty_buffer _ _ _ rfl rfl
  · apply replace_one_chunk (adaptBuf bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf) old ⟨view⟩ ⟨emptySlice⟩ view
    · rfl
    · change Result.ok (decide (view.len > 0#usize)) = Result.ok true
      have hp : view.len > 0#usize := by scalar_tac
      simp [hp]
    · rfl
    · change (if view.len.val ≤ view.length then
          Result.ok (⟨ContentModel.drop view view.len.val⟩ : bytes.bytes.Bytes) else Result.fail .panic) = Result.ok (⟨emptySlice⟩ : bytes.bytes.Bytes)
      simp only [Slice.len_val,le_refl,if_true,content_drop_all]
    · rfl

theorem bytes_after_actual_vec (unused : encoding.sealed.BytesAdapter (alloc.vec.Vec U8))
    (before after : Slice U8) (old : alloc.vec.Vec U8) (value : U64) (ctx : encoding.DecodeContext)
    (hd : encoding.varint.decode_varint sliceBuf before = Result.ok (.Ok value,after))
    (hn : value.val ≤ after.length) :
    encoding.bytes.merge (withActualReplace unused) sliceBuf .LengthDelimited old before ctx =
      Result.ok (.Ok (),fromSlice (ContentModel.take after value.val),drop after value.val) := by
  apply bytes_after_replace _ _ _ _ _ _ _ hd hn
  exact actual_replace_snapshot old (ContentModel.take after value.val)

/-- Content result for the actual contiguous Vec field merger. On a malformed
length prefix or a length exceeding the remaining slice, the old field survives. -/
def bytesResult (old : alloc.vec.Vec U8)
    (decoded : core.result.Result U64 error.DecodeError) (after : Slice U8) :
    core.result.Result Unit error.DecodeError × alloc.vec.Vec U8 × Slice U8 :=
  match decoded with
  | .Err error => (.Err error,old,after)
  | .Ok value => if value.val ≤ after.length then
      (.Ok (),fromSlice (ContentModel.take after value.val),drop after value.val)
    else (.Err (decodeError .BufferUnderflow),old,after)

theorem bytes_from_decode (unused : encoding.sealed.BytesAdapter (alloc.vec.Vec U8))
    (before after : Slice U8) (old : alloc.vec.Vec U8)
    (decoded : core.result.Result U64 error.DecodeError) (ctx : encoding.DecodeContext)
    (hd : encoding.varint.decode_varint sliceBuf before = Result.ok (decoded,after)) :
    encoding.bytes.merge (withActualReplace unused) sliceBuf .LengthDelimited old before ctx =
      Result.ok (bytesResult old decoded after) := by
  cases decoded with
  | Err error => exact bytes_decode_error _ _ _ _ _ _ hd
  | Ok value =>
      by_cases hn : value.val ≤ after.length
      · simpa only [bytesResult,if_pos hn] using bytes_after_actual_vec unused before after old value ctx hd hn
      · simpa only [bytesResult,if_neg hn] using bytes_underflow (withActualReplace unused) before after old value ctx hd (by omega)

/-- Total content reference for every contiguous input slice. All unobserved
adapter methods are universally quantified; there is no replacement or decoder
premise. The clear/reserve/copy models' normal-allocation boundary is explicit. -/
theorem bytes_full_reference (unused : encoding.sealed.BytesAdapter (alloc.vec.Vec U8))
    (before : Slice U8) (old : alloc.vec.Vec U8) (ctx : encoding.DecodeContext) :
    ∃ decoded after, PrefixPost before decoded after ∧ ErrorPost before decoded after ∧
      encoding.bytes.merge (withActualReplace unused) sliceBuf .LengthDelimited old before ctx =
        Result.ok (bytesResult old decoded after) := by
  obtain ⟨decoded,after,hd,hp,he⟩ := decode_full_reference before
  exact ⟨decoded,after,hp,he,bytes_from_decode unused before after old decoded ctx hd⟩

/-- Last successful duplicate wins, replacing rather than appending bytes. -/
theorem bytes_last_value (unused : encoding.sealed.BytesAdapter (alloc.vec.Vec U8))
    (before firstBody middle lastBody : Slice U8) (old : alloc.vec.Vec U8)
    (first last : U64) (ctx : encoding.DecodeContext)
    (hf : encoding.varint.decode_varint sliceBuf before = Result.ok (.Ok first,firstBody))
    (hfb : first.val ≤ firstBody.length) (hm : drop firstBody first.val = middle)
    (hl : encoding.varint.decode_varint sliceBuf middle = Result.ok (.Ok last,lastBody))
    (hlb : last.val ≤ lastBody.length) :
    (do
      let (_,next,rest) ← encoding.bytes.merge (withActualReplace unused) sliceBuf .LengthDelimited old before ctx
      encoding.bytes.merge (withActualReplace unused) sliceBuf .LengthDelimited next rest ctx) =
      Result.ok (.Ok (),fromSlice (ContentModel.take lastBody last.val),drop lastBody last.val) := by
  rw [bytes_after_actual_vec unused before firstBody old first ctx hf hfb]
  simp only [bind_tc_ok,hm]
  exact bytes_after_actual_vec unused middle lastBody _ last ctx hl hlb

#print axioms bytes_from_decode
#print axioms bytes_full_reference
#print axioms bytes_last_value
#print axioms adaptBuf
#print axioms actual_replace_snapshot
#print axioms bytes_after_actual_vec
end LibSignalReference.Candidate.ProstBytes
