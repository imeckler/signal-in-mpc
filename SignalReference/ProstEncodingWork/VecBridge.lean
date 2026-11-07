import ProstEncodingWork.Generated.VecPutSlice.Funs
import ProstEncodingWork.NatBridge

namespace LibSignalReference.Candidate.ProstEncoding

open Aeneas Aeneas.Std
open _root_.ProstEncoding
open TlsMpc

set_option maxHeartbeats 2000000

theorem clone_bytes (source : Slice U8) :
    Slice.clone core.clone.CloneU8.clone source = .ok source := by
  obtain ⟨after, ha, he⟩ := WP.spec_imp_exists
    (Slice.clone_spec (s := source) (clone := core.clone.CloneU8.clone) (by intros; rfl))
  simpa only [← he] using ha

/-- The actual selected Vec override, through the official Aeneas Vec model. -/
theorem put_slice_success (buf : Aeneas.Std.alloc.vec.Vec U8) (source : Slice U8)
    (hsize : buf.length + source.length ≤ Usize.max) :
    ∃ after, _root_.ProstEncoding.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_slice buf source = .ok after ∧
      after.val = buf.val ++ source.val := by
  refine ⟨⟨buf.val ++ source.val, by simpa using hsize⟩, ?_, rfl⟩
  have hclone : Slice.clone (liftFun1 core.clone.impls.CloneU8.clone) source = .ok source :=
    clone_bytes source
  simp only [_root_.ProstEncoding.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_slice,
    Aeneas.Std.alloc.vec.Vec.extend_from_slice, dif_pos hsize]
  split
  · rename_i copied hcopy
    have he : copied = source := Result.ok.inj (hcopy.symm.trans hclone)
    subst copied
    rfl
  · rename_i error hcopy
    cases hcopy.symm.trans hclone
  · rename_i hcopy
    cases hcopy.symm.trans hclone

theorem put_slice_overflow (buf : Aeneas.Std.alloc.vec.Vec U8) (source : Slice U8)
    (hsize : ¬ buf.length + source.length ≤ Usize.max) :
    _root_.ProstEncoding.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_slice buf source = .fail .panic := by
  simp [_root_.ProstEncoding.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_slice,
    Aeneas.Std.alloc.vec.Vec.extend_from_slice, hsize]

def oneByte (byte : U8) : Slice U8 := Array.to_slice (Array.make 1#usize [byte])

theorem oneByte_val (byte : U8) : (oneByte byte).val = [byte] := by rfl

def appendOne (buf : Aeneas.Std.alloc.vec.Vec U8) (byte : U8) :
    Result (Aeneas.Std.alloc.vec.Vec U8) :=
  _root_.ProstEncoding.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_slice buf (oneByte byte)

/-- The selected dictionary projections are assembled from the actual Vec
override and actual one-byte default, with no assumed append implementation. -/
def vecDictionary : bytes.buf.buf_mut.BufMut (Aeneas.Std.alloc.vec.Vec U8) where
  put_slice := _root_.ProstEncoding.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_slice
  put_u8 := appendOne

theorem vec_put_u8_default (buf : Aeneas.Std.alloc.vec.Vec U8) (byte : U8) :
    vecDictionary.put_u8 buf byte = bytes.buf.buf_mut.BufMut.put_u8.default vecDictionary buf byte := by
  rfl

theorem appendOne_success (buf : Aeneas.Std.alloc.vec.Vec U8) (byte : U8)
    (hsize : buf.length < Usize.max) :
    ∃ after, appendOne buf byte = .ok after ∧ after.val = buf.val ++ [byte] := by
  exact put_slice_success buf (oneByte byte) (by change buf.length + 1 ≤ Usize.max; omega)

def vecContents (buf : Aeneas.Std.alloc.vec.Vec U8) : List (BitVec 8) :=
  buf.val.map UScalar.bv

theorem vec_appends_within : AppendsWithin vecDictionary.put_u8 vecContents Usize.max := by
  intro buf byte hsize
  obtain ⟨after, ha, hv⟩ := appendOne_success buf byte (by simpa [vecContents] using hsize)
  refine ⟨after, ha, ?_⟩
  simp [vecContents, hv]

/-- Actual prost encoding using the selected actual Vec buffer methods agrees
with the Lean public-length encoder for every uint64, within the model's size
bound. The original generic loop's errors remain covered by encode_eq_run. -/
theorem vec_encode_appends (value : U64) (buf : Aeneas.Std.alloc.vec.Vec U8)
    (hsize : buf.length + 10 ≤ Usize.max) :
    ∃ after, encoding.varint.encode_varint vecDictionary value buf = .ok after ∧
      vecContents after = vecContents buf ++ Signal.Varint.publicNat ByteAuth.concrete value.val := by
  exact encode_appends_within vecDictionary vecContents Usize.max vec_appends_within
    value buf (by simpa [vecContents] using hsize)

end LibSignalReference.Candidate.ProstEncoding
