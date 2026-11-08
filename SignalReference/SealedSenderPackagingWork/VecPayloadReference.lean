import BytesReferenceWork.VecReference
import BytesReferenceWork.Replayed.BufModel
import SealedSenderPackagingWork.Generated.PayloadAppendSelected.Funs

namespace LibSignalReference.Candidate.SealedSenderPayload
open Aeneas Aeneas.Std
open LibSignalReference.Candidate.ProstVecAdapter
open LibSignalReference.Candidate.ProstBytesBuf
set_option maxHeartbeats 1000000

def contiguous : ProstAdapterCandidate.bytes.buf.buf_impl.Buf (Slice U8) where
  remaining := remaining
  chunk := chunk
  advance := advance
  has_remaining := fun view => do
    let n ← remaining view
    .ok (n>0#usize)


/-- Official Aeneas Vec clone/append content semantics; allocation resource
and concrete heap address/Drop behavior remain the existing model boundary. -/
theorem extend_bytes (target : alloc.vec.Vec U8) (view : Slice U8)
    (fits : target.length+view.length≤Usize.max) :
    ∃ after, alloc.vec.Vec.extend_from_slice core.clone.CloneU8 target view = .ok after ∧
      after.val=target.val++view.val := by
  refine ⟨⟨target.val++view.val,by simpa using fits⟩,?_,rfl⟩
  have hc : Slice.clone (liftFun1 core.clone.impls.CloneU8.clone) view = .ok view :=
    clone_u8 view
  simp only [alloc.vec.Vec.extend_from_slice,dif_pos fits]
  split
  · rename_i copied he
    have eq : copied=view := Result.ok.inj (he.symm.trans hc)
    subst copied;rfl
  · rename_i error he;cases he.symm.trans hc
  · rename_i he;cases he.symm.trans hc

theorem put_loop_one_chunk_any {B : Type} (inst : ProstAdapterCandidate.bytes.buf.buf_impl.Buf B)
    (target : alloc.vec.Vec U8) (buf empty : B) (view : Slice U8)
    (fits : target.length+view.length≤Usize.max)
    (hh : inst.has_remaining buf=.ok true) (hc : inst.chunk buf=.ok view)
    (ha : inst.advance buf view.len=.ok empty) (hz : inst.has_remaining empty=.ok false) :
    ∃ after, ProstAdapterCandidate.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop inst target buf=.ok after ∧
      after.val=target.val++view.val := by
  obtain ⟨after,he,hval⟩ := extend_bytes target view fits
  refine ⟨after,?_,hval⟩
  rw [ProstAdapterCandidate.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop,loop.eq_1]
  simp only [ProstAdapterCandidate.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop.body,
    hh,bind_tc_ok,if_true,hc,he,ha]
  exact put_loop_done inst after empty hz

def emptySlice : Slice U8 := ⟨[],by simp⟩

theorem drop_all (view : Slice U8) : drop view view.length=emptySlice := by
  apply Subtype.ext
  exact List.drop_length

/-- Actual unchanged bytes Vec<u8>::put loop, using the already scoped
contiguous Slice Buf/content model. No payload-append contract is assumed. -/
theorem actual_put_slice_appends (target : alloc.vec.Vec U8) (view : Slice U8)
    (fits : target.length+view.length≤Usize.max) :
    ∃ after, ProstAdapterCandidate.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put
        contiguous target view=.ok after ∧ after.val=target.val++view.val := by
  unfold ProstAdapterCandidate.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put
  have hr : contiguous.remaining view=.ok view.len := rfl
  rw [hr]
  simp only [bind_tc_ok,ProstAdapterCandidate.alloc.vec.Vec.reserve]
  rw [if_pos (by simpa only [Slice.len_val] using fits)]
  simp only [bind_tc_ok]
  by_cases empty : view.length=0
  · have eq : view=emptySlice := by apply Subtype.ext;exact List.eq_nil_iff_length_eq_zero.mpr empty
    subst view
    refine ⟨target,put_loop_done _ target emptySlice rfl,?_⟩
    simp [emptySlice]
  · apply put_loop_one_chunk_any _ target view emptySlice view fits
    · change Result.ok (decide (view.len>0#usize))=Result.ok true
      have h : view.len>0#usize := by scalar_tac
      simp [h]
    · rfl
    · change (if view.length<view.len.val then Result.fail .panic else Result.ok (drop view view.len.val))=Result.ok emptySlice
      rw [Slice.len_val,if_neg (by omega),drop_all]
    · rfl

theorem actual_put_slice_overflow (target : alloc.vec.Vec U8) (view : Slice U8)
    (overflow : Usize.max<target.length+view.length) :
    ProstAdapterCandidate.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put
      contiguous target view=.fail .panic := by
  unfold ProstAdapterCandidate.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put
  have hr : contiguous.remaining view=.ok view.len := rfl
  rw [hr]
  simp only [bind_tc_ok,ProstAdapterCandidate.alloc.vec.Vec.reserve]
  rw [if_neg (by simpa only [Slice.len_val] using Nat.not_le.mpr overflow)]
  rfl

/-- Projection of the same source Buf methods between extraction-local types.
The additional has_remaining method is bytes' actual remaining()>0 default. -/
def forwardBuf {B : Type} (inst : SealedSenderAppend.bytes.buf.buf_impl.Buf B) :
    ProstAdapterCandidate.bytes.buf.buf_impl.Buf B where
  remaining := inst.remaining
  chunk := inst.chunk
  advance := inst.advance
  has_remaining := fun buf => do
    let n ← inst.remaining buf
    .ok (n>0#usize)

/-- Actual Vec override, retaining the unchanged extracted loop. The three
unused unsafe BufMut methods were removed by explicit metadata scope (review pending). -/
def actualVecDictionary : SealedSenderAppend.bytes.buf.buf_mut.BufMut (alloc.vec.Vec U8) where
  put := fun inst target source =>
    ProstAdapterCandidate.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put (forwardBuf inst) target source

theorem forward_contiguous :
    forwardBuf SealedSenderAppend.Shared0SliceU8.Insts.BytesBufBuf_implBuf = contiguous := rfl

/-- Actual unchanged prost Vec BytesAdapter::append_to plus actual unchanged
bytes Vec BufMut::put. No payload-correctness/success predicate is an input. -/
theorem actual_adapter_appends (value target : alloc.vec.Vec U8)
    (fits : target.length+value.length≤Usize.max) :
    ∃ after, SealedSenderAppend.alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.append_to
        actualVecDictionary value target=.ok after ∧ after.val=target.val++value.val := by
  unfold SealedSenderAppend.alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.append_to
  change (∃ after, (do
    let source ← Result.ok (alloc.vec.Vec.deref value)
    ProstAdapterCandidate.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put
      (forwardBuf SealedSenderAppend.Shared0SliceU8.Insts.BytesBufBuf_implBuf) target source)=.ok after ∧
      after.val=target.val++value.val)
  rw [forward_contiguous]
  simp only [bind_tc_ok]
  exact actual_put_slice_appends target (alloc.vec.Vec.deref value) fits

theorem actual_adapter_overflow (value target : alloc.vec.Vec U8)
    (overflow : Usize.max<target.length+value.length) :
    SealedSenderAppend.alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.append_to
      actualVecDictionary value target=.fail .panic := by
  unfold SealedSenderAppend.alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.append_to
  change (do
    let source ← Result.ok (alloc.vec.Vec.deref value)
    ProstAdapterCandidate.alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put
      (forwardBuf SealedSenderAppend.Shared0SliceU8.Insts.BytesBufBuf_implBuf) target source)=.fail .panic
  rw [forward_contiguous]
  simp only [bind_tc_ok]
  exact actual_put_slice_overflow target (alloc.vec.Vec.deref value) overflow

end LibSignalReference.Candidate.SealedSenderPayload
