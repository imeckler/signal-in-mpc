import SpqrReference.VarintGenerated.Funs
import ProstEncodingWork.VecBridge

/-! Operation equivalence for the actual SPQR 1.6.0 varint loop. The finite
unfolding preserves every result of the unchanged official Vec.push model;
the append theorem then proves success under its explicit size bound. -/

namespace LibSignalReference.Candidate.SpqrVarint

open Aeneas Aeneas.Std TlsMpc
open LibSignalReference.Candidate.ProstEncoding

set_option maxHeartbeats 2000000

def nextIndex (index : Usize) (hi : index.val < 10) : Usize :=
  Usize.ofNatCore (index.val + 1) (by scalar_tac)

theorem range_next (index : Usize) (hi : index.val < 10) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨index,10#usize⟩ =
      .ok (some index, ⟨nextIndex index hi,10#usize⟩) := by
  have hb : index.val + 1 ≤ Usize.max := by scalar_tac
  have hb' : index.val < UScalar.max .Usize := by rw [UScalar.max_USize_eq]; omega
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hi, hb', nextIndex]
  rfl

theorem nextIndex_val (index : Usize) (hi : index.val < 10) :
    (nextIndex index hi).val = index.val + 1 := by simp [nextIndex]

theorem range_done :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨10#usize,10#usize⟩ =
      .ok (none, ⟨10#usize,10#usize⟩) := by rfl

theorem small_byte (value : U64) (h : value < 128#u64) :
    UScalar.cast .U8 (value &&& 127#u64) = UScalar.cast .U8 value := by
  apply UScalar.eq_of_val_eq
  simp only [UScalar.cast_val_eq, UScalar.val_and]
  change (value.val &&& 127) % 256 = value.val % 256
  have hm : value.val &&& 127 = value.val % 128 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod value.val 7
  have hv : value.val < 128 := h
  rw [hm, Nat.mod_eq_of_lt hv]

theorem continued_byte (value : U64) :
    128#u8 ||| UScalar.cast .U8 (value &&& 127#u64) =
      UScalar.cast .U8 ((value &&& 127#u64) ||| 128#u64) := by
  apply UScalar.eq_of_val_eq
  simp only [UScalar.val_or, UScalar.cast_val_eq, UScalar.val_and]
  change 128 ||| ((value.val &&& 127) % 256) = ((value.val &&& 127) ||| 128) % 256
  have hm : value.val &&& 127 = value.val % 128 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod value.val 7
  have ho : value.val % 128 ||| 128 = value.val % 128 + 128 := by
    have h := Nat.two_pow_add_eq_or_of_lt (i := 7) (by omega : value.val % 128 < 2^7) 1
    simpa [Nat.or_comm, Nat.add_comm] using h.symm
  rw [hm, Nat.mod_eq_of_lt (by omega : value.val % 128 < 256), Nat.or_comm, ho]
  omega

theorem loop_body (index : Usize) (hi : index.val < 10) (value : U64)
    (buf : alloc.vec.Vec U8) :
    _root_.SpqrReference.encode_varint_loop.body ⟨index,10#usize⟩ value buf =
      (if value < 128#u64 then do
        let nextBuf ← alloc.vec.Vec.push buf (UScalar.cast .U8 value)
        .ok (.done nextBuf)
      else do
        let nextBuf ← alloc.vec.Vec.push buf
          (UScalar.cast .U8 ((value &&& 127#u64) ||| 128#u64))
        .ok (.cont (⟨nextIndex index hi,10#usize⟩, (⟨value.bv >>> 7⟩ : U64), nextBuf))) := by
  rw [_root_.SpqrReference.encode_varint_loop.body, range_next index hi]
  simp only [bind_tc_ok, lift]
  by_cases hv : value < 128#u64
  · simp only [if_pos hv, small_byte value hv]
    rfl
  · simp only [if_neg hv, continued_byte]
    rfl

/-- Equality retains Vec.push failures and divergence; success is not assumed. -/
theorem loop_eq_run (index : Usize) (hi : index.val ≤ 10) (value : U64)
    (buf : alloc.vec.Vec U8) :
    _root_.SpqrReference.encode_varint_loop ⟨index,10#usize⟩ value buf =
      run alloc.vec.Vec.push (10 - index.val) value buf := by
  generalize hn : 10 - index.val = fuel
  induction fuel generalizing index value buf with
  | zero =>
    have he : index = 10#usize := by scalar_tac
    subst index
    unfold _root_.SpqrReference.encode_varint_loop
    rw [loop]
    simp [_root_.SpqrReference.encode_varint_loop.body, range_done, run]
  | succ fuel ih =>
    have hit : index.val < 10 := by omega
    have hn10 : (nextIndex index hit).val ≤ 10 := by rw [nextIndex_val]; omega
    have hcount : 10 - (nextIndex index hit).val = fuel := by rw [nextIndex_val]; omega
    unfold _root_.SpqrReference.encode_varint_loop
    rw [loop]
    dsimp only
    rw [loop_body index hit]
    simp only [run, shift_seven]
    by_cases hv : value < 128#u64
    · simp only [if_pos hv]
      cases hp : alloc.vec.Vec.push buf (UScalar.cast .U8 value) <;> simp
    · simp only [if_neg hv]
      cases hp : alloc.vec.Vec.push buf
        (UScalar.cast .U8 ((value &&& 127#u64) ||| 128#u64)) with
      | fail e => simp
      | div => simp
      | ok nextBuf =>
        simp only [bind_tc_ok]
        simpa only [_root_.SpqrReference.encode_varint_loop] using
          ih (nextIndex index hit) hn10 ⟨value.bv >>> 7⟩ nextBuf hcount

theorem encode_eq_run (value : U64) (buf : alloc.vec.Vec U8) :
    _root_.SpqrReference.encode_varint value buf = run alloc.vec.Vec.push 10 value buf := by
  simpa [_root_.SpqrReference.encode_varint, _root_.SpqrReference.MAX_VARINT_BYTES_LEN] using
    loop_eq_run 0#usize (by decide) value buf

theorem push_appends_within : AppendsWithin alloc.vec.Vec.push vecContents Usize.max := by
  intro buf byte hsize
  obtain ⟨after, ha, hv⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec buf byte (by simpa [vecContents] using hsize))
  refine ⟨after, ha, ?_⟩
  simp [vecContents, hv]

/-- Actual SPQR encode_varint appends canonical publicNat bytes for every U64. -/
theorem encode_appends (value : U64) (buf : alloc.vec.Vec U8)
    (hsize : buf.length + 10 ≤ Usize.max) :
    ∃ after, _root_.SpqrReference.encode_varint value buf = .ok after ∧
      vecContents after = vecContents buf ++ Signal.Varint.publicNat ByteAuth.concrete value.val := by
  rw [encode_eq_run]
  exact run_appends_within alloc.vec.Vec.push vecContents Usize.max push_appends_within
    10 value buf (by simpa [vecContents] using hsize)

end LibSignalReference.Candidate.SpqrVarint
