import ProstEncodingWork.Generated.EncodeSelected.Funs

namespace LibSignalReference.Candidate.ProstEncoding

open Aeneas Aeneas.Std
open _root_.ProstEncoding

set_option maxHeartbeats 2000000

/-- Proof-only finite unfolding of the actual loop. It keeps the supplied
buffer operations and propagates their failure/divergence unchanged. -/
def run (put : B → U8 → Result B) : Nat → U64 → B → Result B
  | 0, _, buf => .ok buf
  | fuel + 1, value, buf =>
    if value < 128#u64 then put buf (UScalar.cast .U8 value)
    else do
      let nextBuf ← put buf (UScalar.cast .U8 ((value &&& 127#u64) ||| 128#u64))
      let nextValue ← value >>> 7#i32
      run put fuel nextValue nextBuf

def nextIndex (index : I32) (hi : index.val < 10) : I32 :=
  I32.ofIntCore (index.val + 1) (by scalar_tac)

theorem range_next (index : I32) (hi : index.val < 10) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 ⟨index,10#i32⟩ =
      .ok (some index, ⟨nextIndex index hi,10#i32⟩) := by
  have hb : index.val + 1 ≤ I32.max := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.iter.range.IScalarStep.forward_checked,
    core.cmp.impls.PartialOrdI32.lt, hi, hb, nextIndex]
  rfl

theorem nextIndex_val (index : I32) (hi : index.val < 10) :
    (nextIndex index hi).val = index.val + 1 := by
  simp [nextIndex]

theorem range_done :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 ⟨10#i32,10#i32⟩ =
      .ok (none, ⟨10#i32,10#i32⟩) := by rfl

theorem shift_seven (value : U64) :
    value >>> 7#i32 = .ok (⟨value.bv >>> 7⟩ : U64) := by rfl

theorem loop_body (dictionary : bytes.buf.buf_mut.BufMut B) (index : I32)
    (hi : index.val < 10) (value : U64) (buf : B) :
    encoding.varint.encode_varint_loop.body dictionary ⟨index,10#i32⟩ value buf =
      (if value < 128#u64 then do
        let nextBuf ← dictionary.put_u8 buf (UScalar.cast .U8 value)
        .ok (.done nextBuf)
      else do
        let nextBuf ← dictionary.put_u8 buf
          (UScalar.cast .U8 ((value &&& 127#u64) ||| 128#u64))
        .ok (.cont (⟨nextIndex index hi,10#i32⟩, (⟨value.bv >>> 7⟩ : U64), nextBuf))) := by
  rw [encoding.varint.encode_varint_loop.body, range_next index hi]
  simp only [bind_tc_ok, lift]
  split <;> rfl

/-- Exact equality for the actual generic loop, including any error or
divergence returned by its supplied buffer dictionary. -/
theorem loop_eq_run (dictionary : bytes.buf.buf_mut.BufMut B) (index : I32)
    (hi0 : 0 ≤ index.val) (hi : index.val ≤ 10) (value : U64) (buf : B) :
    encoding.varint.encode_varint_loop dictionary ⟨index,10#i32⟩ value buf =
      run dictionary.put_u8 (10 - index.val.toNat) value buf := by
  generalize hn : 10 - index.val.toNat = fuel
  induction fuel generalizing index value buf with
  | zero =>
    have he : index = 10#i32 := by scalar_tac
    subst index
    unfold encoding.varint.encode_varint_loop
    rw [loop]
    simp [encoding.varint.encode_varint_loop.body, range_done, run]
  | succ fuel ih =>
    have hit : index.val < 10 := by omega
    have hn0 : 0 ≤ (nextIndex index hit).val := by rw [nextIndex_val]; omega
    have hn10 : (nextIndex index hit).val ≤ 10 := by rw [nextIndex_val]; omega
    have hcount : 10 - (nextIndex index hit).val.toNat = fuel := by
      rw [nextIndex_val]
      omega
    unfold encoding.varint.encode_varint_loop
    rw [loop]
    dsimp only
    rw [loop_body dictionary index hit]
    simp only [run, shift_seven]
    by_cases hv : value < 128#u64
    · simp only [if_pos hv]
      cases hp : dictionary.put_u8 buf (UScalar.cast .U8 value) <;> simp
    · simp only [if_neg hv]
      cases hp : dictionary.put_u8 buf
        (UScalar.cast .U8 ((value &&& 127#u64) ||| 128#u64)) with
      | fail e => simp
      | div => simp
      | ok nextBuf =>
        simp only [bind_tc_ok]
        simpa only [encoding.varint.encode_varint_loop] using
          ih (nextIndex index hit) hn0 hn10 ⟨value.bv >>> 7⟩ nextBuf hcount

theorem encode_eq_run (dictionary : bytes.buf.buf_mut.BufMut B) (value : U64) (buf : B) :
    encoding.varint.encode_varint dictionary value buf = run dictionary.put_u8 10 value buf := by
  exact loop_eq_run dictionary 0#i32 (by decide) (by decide) value buf

/-- The unchanged actual default method writes the one-byte slice through
the supplied put_slice field; no append behavior is assumed here. -/
theorem put_u8_default (dictionary : bytes.buf.buf_mut.BufMut B) (buf : B) (byte : U8) :
    bytes.buf.buf_mut.BufMut.put_u8.default dictionary buf byte =
      dictionary.put_slice buf (Array.to_slice (Array.make 1#usize [byte])) := by
  rfl

end LibSignalReference.Candidate.ProstEncoding
