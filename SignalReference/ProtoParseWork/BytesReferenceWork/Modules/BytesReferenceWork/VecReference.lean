import ProtoParseWork.BytesReferenceWork.Generated.vec_replace_put_body.Funs

namespace LibSignalReference.Candidate.ProstVecAdapter
open Aeneas Aeneas.Std ProstAdapterCandidate
set_option maxHeartbeats 500000

def fromSlice (view : Slice U8) : alloc.vec.Vec U8 := ⟨view.val,view.property⟩

theorem clone_u8 (view : Slice U8) : Slice.clone core.clone.CloneU8.clone view = .ok view := by
  obtain ⟨next,hn,he⟩ := WP.spec_imp_exists (Slice.clone_spec (s := view) (by intros; rfl))
  simpa only [← he] using hn

theorem extend_empty (view : Slice U8) :
    Aeneas.Std.alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.new U8) view =
      .ok (fromSlice view) := by
  unfold Aeneas.Std.alloc.vec.Vec.extend_from_slice
  have hn : (alloc.vec.Vec.new U8).length + view.length ≤ Usize.max := by
    simpa using view.property
  rw [dif_pos hn]
  have hc : Slice.clone (liftFun1 core.clone.impls.CloneU8.clone) view = .ok view := clone_u8 view
  split
  · rename_i next he
    rw [hc] at he
    cases he
    rfl
  · rename_i error he
    rw [hc] at he
    cases he
  · rename_i he
    rw [hc] at he
    cases he

theorem reserve_empty (view : Slice U8) :
    alloc.vec.Vec.reserve Global (alloc.vec.Vec.new U8) view.len = .ok (alloc.vec.Vec.new U8) := by
  unfold alloc.vec.Vec.reserve
  apply if_pos
  change 0 + view.len.val ≤ Usize.max
  simpa only [Slice.len_val,Nat.zero_add] using view.property

theorem put_loop_done {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (value : alloc.vec.Vec U8) (empty : B) (hz : inst.has_remaining empty = .ok false) :
    alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop inst value empty = .ok value := by
  rw [alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop,loop.eq_1]
  simp [alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop.body,hz]

/-- The actual Vec<u8>::put loop copies a contiguous chunk once and stops. -/
theorem put_loop_one_chunk {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (buf empty : B) (view : Slice U8)
    (hh : inst.has_remaining buf = .ok true)
    (hc : inst.chunk buf = .ok view)
    (ha : inst.advance buf view.len = .ok empty)
    (hz : inst.has_remaining empty = .ok false) :
    alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop inst (alloc.vec.Vec.new U8) buf =
      .ok (fromSlice view) := by
  rw [alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop,loop.eq_1]
  simp only [uncurry_apply_pair,alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put_loop.body,
    hh,bind_tc_ok,if_true,hc,extend_empty,ha]
  exact put_loop_done inst (fromSlice view) empty hz

theorem put_empty_buffer {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (buf : B) (hr : inst.remaining buf = .ok 0#usize) (hz : inst.has_remaining buf = .ok false) :
    alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put inst (alloc.vec.Vec.new U8) buf =
      .ok (alloc.vec.Vec.new U8) := by
  unfold alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put
  simp only [hr,bind_tc_ok,alloc.vec.Vec.reserve]
  rw [if_pos (by simp : (alloc.vec.Vec.new U8).length + (0#usize).val ≤ Usize.max)]
  simp only [bind_tc_ok]
  exact put_loop_done _ _ _ hz

theorem put_one_chunk {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (buf empty : B) (view : Slice U8)
    (hr : inst.remaining buf = .ok view.len)
    (hh : inst.has_remaining buf = .ok true)
    (hc : inst.chunk buf = .ok view)
    (ha : inst.advance buf view.len = .ok empty)
    (hz : inst.has_remaining empty = .ok false) :
    alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put inst (alloc.vec.Vec.new U8) buf =
      .ok (fromSlice view) := by
  simp only [alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.put,hr,bind_tc_ok,reserve_empty]
  exact put_loop_one_chunk _ _ _ _ hh hc ha hz

/-- The actual Prost Vec adapter clears the old bytes before copying the new chunk. -/
theorem replace_one_chunk {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (old : alloc.vec.Vec U8) (buf empty : B) (view : Slice U8)
    (hr : inst.remaining buf = .ok view.len)
    (hh : inst.has_remaining buf = .ok true)
    (hc : inst.chunk buf = .ok view)
    (ha : inst.advance buf view.len = .ok empty)
    (hz : inst.has_remaining empty = .ok false) :
    alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.replace_with inst old buf =
      .ok (fromSlice view) := by
  simp only [alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.replace_with,
    alloc.vec.Vec.clear,bind_tc_ok,hr,reserve_empty]
  exact put_one_chunk _ _ _ _ hr hh hc ha hz


theorem replace_empty_buffer {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (old : alloc.vec.Vec U8) (buf : B)
    (hr : inst.remaining buf = .ok 0#usize) (hz : inst.has_remaining buf = .ok false) :
    alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.replace_with inst old buf =
      .ok (alloc.vec.Vec.new U8) := by
  simp only [alloc.vec.VecU8.Insts.ProstEncodingSealedBytesAdapter.replace_with,
    alloc.vec.Vec.clear,bind_tc_ok,hr,alloc.vec.Vec.reserve]
  rw [if_pos (by simp : (alloc.vec.Vec.new U8).length + (0#usize).val ≤ Usize.max)]
  simp only [bind_tc_ok]
  exact put_empty_buffer _ _ hr hz

#print axioms clone_u8
#print axioms extend_empty
#print axioms reserve_empty
#print axioms put_loop_done
#print axioms put_loop_one_chunk
#print axioms put_empty_buffer
#print axioms put_one_chunk
#print axioms replace_one_chunk
#print axioms replace_empty_buffer
end LibSignalReference.Candidate.ProstVecAdapter
