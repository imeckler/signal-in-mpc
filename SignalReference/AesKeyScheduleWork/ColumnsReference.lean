import AesKeyScheduleWork.CopyReference
import LibSignalReference.Proofs.AesLayoutReference
import TlsMpc.Signal.AesKeyColumns

namespace LibSignalReference.Candidate.AesKeyColumns

open Aeneas Aeneas.Std
open RustCryptoAesKeySchedule
open TlsMpc.Signal.AesKeyColumns (column concrete)
open LibSignalReference.Proofs.AesLayout (shift_left_i32)

set_option maxHeartbeats 2000000

def next (index : Usize) (hi : index.val < 8) : Usize :=
  Usize.ofNatCore (index.val + 1) (by scalar_tac)

theorem range_next (index : Usize) (hi : index.val < 8) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨index,8#usize⟩ =
      .ok (some index, ⟨next index hi,8#usize⟩) := by
  have hb : index.val < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hi, hb, next]
  rfl

theorem range_done :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨8#usize,8#usize⟩ =
      .ok (none, ⟨8#usize,8#usize⟩) := by rfl

def update (offset distance rotation index : Nat) (words : Slice U64) : Slice U64 :=
  words.setAtNat (offset + index)
    ⟨column concrete rotation
      (words.val[offset + index - distance]?.getD 0#u64).bv
      (words.val[offset + index]?.getD 0#u64).bv⟩

def run (offset distance rotation : Nat) : Nat → Nat → Slice U64 → Slice U64
  | _, 0, words => words
  | index, count + 1, words =>
      run offset distance rotation (index + 1) count (update offset distance rotation index words)

theorem update_length (offset distance rotation index : Nat) (words : Slice U64) :
    (update offset distance rotation index words).length = words.length := by
  simp [update, Slice.length]

theorem run_length (offset distance rotation index count : Nat) (words : Slice U64) :
    (run offset distance rotation index count words).length = words.length := by
  induction count generalizing index words with
  | zero => rfl
  | succ count ih => simp only [run, ih, update_length]

theorem column_body (offset distance : Usize) (rotation : U32) (index : Usize)
    (words : Slice U64) (hi : index.val < 8) (hd : distance.val ≤ offset.val)
    (hs : offset.val + 8 ≤ words.length) :
    soft.fixslice.xor_columns_loop.body offset distance rotation ⟨index,8#usize⟩ words =
      .ok (.cont (⟨next index hi,8#usize⟩,
        update offset.val distance.val rotation.val index.val words)) := by
  have hmax : offset.val + index.val ≤ Usize.max := by scalar_tac
  obtain ⟨pos, hp, hpos⟩ := WP.spec_imp_exists (Usize.add_spec (x := offset) (y := index) hmax)
  have hsub : distance.val ≤ pos.val := by omega
  obtain ⟨prev, hv, hprev⟩ := WP.spec_imp_exists (Usize.sub_spec (x := pos) (y := distance) hsub)
  have hpl : pos.val < words.length := by omega
  have hvl : prev.val < words.length := by omega
  have hpidx : offset.val + index.val < words.val.length := by change _ < words.length; omega
  have hvidx : offset.val + index.val - distance.val < words.val.length := by change _ < words.length; omega
  rw [soft.fixslice.xor_columns_loop.body, range_next index hi]
  with_unfolding_all simp [hp, hv, Slice.index_usize, Slice.update,
    soft.fixslice.ror, lift, shift_left_i32, core.num.U64.rotate_right,
    UScalar.rotate_right, update, column, concrete, Slice.setAtNat,
    hpos, hprev, List.getElem?_eq_getElem hpidx, List.getElem?_eq_getElem hvidx]
  rfl

theorem columns_loop (offset distance : Usize) (rotation : U32) (index : Usize)
    (words : Slice U64) (hi : index.val ≤ 8) (hd : distance.val ≤ offset.val)
    (hs : offset.val + 8 ≤ words.length) :
    soft.fixslice.xor_columns_loop ⟨index,8#usize⟩ words offset distance rotation =
      .ok (run offset.val distance.val rotation.val index.val (8 - index.val) words) := by
  generalize hn : 8 - index.val = count
  induction count generalizing index words with
  | zero =>
    have hi8 : index = 8#usize := by scalar_tac
    subst index
    unfold soft.fixslice.xor_columns_loop
    rw [loop]
    simp [soft.fixslice.xor_columns_loop.body, range_done, run]
  | succ count ih =>
    have hi' : index.val < 8 := by omega
    have hn' : 8 - (next index hi').val = count := by simp only [next]; scalar_tac
    have hi'' : (next index hi').val ≤ 8 := by simp only [next]; scalar_tac
    have hs' : offset.val + 8 ≤
        (update offset.val distance.val rotation.val index.val words).length := by
      rw [update_length]
      exact hs
    unfold soft.fixslice.xor_columns_loop
    rw [loop]
    dsimp only
    rw [column_body offset distance rotation index words hi' hd hs]
    have h := ih (next index hi') (update offset.val distance.val rotation.val index.val words) hi'' hs' hn'
    have hnval : (next index hi').val = index.val + 1 := rfl
    rw [hnval] at h
    simpa only [soft.fixslice.xor_columns_loop, run] using h

theorem xor_columns_spec (offset distance : Usize) (rotation : U32) (words : Slice U64)
    (hd : distance.val ≤ offset.val) (hs : offset.val + 8 ≤ words.length) :
    soft.fixslice.xor_columns words offset distance rotation =
      .ok (run offset.val distance.val rotation.val 0 8 words) := by
  exact columns_loop offset distance rotation 0#usize words (by decide) hd hs

end LibSignalReference.Candidate.AesKeyColumns
