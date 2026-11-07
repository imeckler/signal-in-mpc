import LibSignalReference.Generated.AesShift.Funs
import TlsMpc.Signal.AesShift
import LibSignalReference.Proofs.AesLayoutReference

namespace LibSignalReference.Proofs.AesLinear

open Aeneas Aeneas.Std TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open LibSignalReference.Proofs.AesLayout

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem delta1_reference (word mask : U64) (shift : U32) (hs : shift.val < 64) :
    RustCryptoAesLinear.soft.fixslice.delta_swap_1 word shift mask =
      .ok ⟨deltaWord word.bv shift.val mask.bv⟩ := by
  simp [RustCryptoAesLinear.soft.fixslice.delta_swap_1, deltaWord, lift,
    shift_right_u32 _ _ hs, shift_left_u32 _ _ hs]
  rfl

theorem shift1_body (it : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64) :
    RustCryptoAesLinear.soft.fixslice.shift_rows_1_loop.body it back =
      if h : it.i < it.slice.length then
        .ok (.cont ({it with i := it.i + 1}, fun im => back {im with
          slice := im.slice.setAtNat it.i ⟨shiftWord1 it.slice[it.i].bv⟩}))
      else .ok (.done (back it)) := by
  unfold RustCryptoAesLinear.soft.fixslice.shift_rows_1_loop.body
  unfold core.slice.iter.IteratorIterMut.next
  simp only [Slice.len_val]
  split <;> simp [delta1_reference, shiftWord1] <;> rfl

theorem shift1_reference (words : Words (BitVec 64)) :
    RustCryptoAesLinear.soft.fixslice.shift_rows_1 (wordSlice words) =
      .ok (wordSlice (mapWords shiftWord1 words)) := by
  have hlength : (wordSlice words).length = 8 := by simp [wordSlice, Words.list]
  have hlen : Slice.len (wordSlice words) = 8#usize := by scalar_tac
  simp only [RustCryptoAesLinear.soft.fixslice.shift_rows_1]
  simp [hlen, massert, core.slice.Slice.iter_mut]
  unfold RustCryptoAesLinear.soft.fixslice.shift_rows_1_loop
  iterate 9 (rw [loop]; dsimp only; rw [shift1_body]; simp [hlength])
  rfl

theorem shift2_body (it : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64) :
    RustCryptoAesLinear.soft.fixslice.shift_rows_2_loop.body it back =
      if h : it.i < it.slice.length then
        .ok (.cont ({it with i := it.i + 1}, fun im => back {im with
          slice := im.slice.setAtNat it.i ⟨shiftWord2 it.slice[it.i].bv⟩}))
      else .ok (.done (back it)) := by
  unfold RustCryptoAesLinear.soft.fixslice.shift_rows_2_loop.body
  unfold core.slice.iter.IteratorIterMut.next
  simp only [Slice.len_val]
  split <;> simp [delta1_reference, shiftWord2] <;> rfl

theorem shift2_reference (words : Words (BitVec 64)) :
    RustCryptoAesLinear.soft.fixslice.shift_rows_2 (wordSlice words) =
      .ok (wordSlice (mapWords shiftWord2 words)) := by
  have hlength : (wordSlice words).length = 8 := by simp [wordSlice, Words.list]
  have hlen : Slice.len (wordSlice words) = 8#usize := by scalar_tac
  simp only [RustCryptoAesLinear.soft.fixslice.shift_rows_2]
  simp [hlen, massert, core.slice.Slice.iter_mut]
  unfold RustCryptoAesLinear.soft.fixslice.shift_rows_2_loop
  iterate 9 (rw [loop]; dsimp only; rw [shift2_body]; simp [hlength])
  rfl

theorem shift3_body (it : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64) :
    RustCryptoAesLinear.soft.fixslice.shift_rows_3_loop.body it back =
      if h : it.i < it.slice.length then
        .ok (.cont ({it with i := it.i + 1}, fun im => back {im with
          slice := im.slice.setAtNat it.i ⟨shiftWord3 it.slice[it.i].bv⟩}))
      else .ok (.done (back it)) := by
  unfold RustCryptoAesLinear.soft.fixslice.shift_rows_3_loop.body
  unfold core.slice.iter.IteratorIterMut.next
  simp only [Slice.len_val]
  split <;> simp [delta1_reference, shiftWord3] <;> rfl

theorem shift3_reference (words : Words (BitVec 64)) :
    RustCryptoAesLinear.soft.fixslice.shift_rows_3 (wordSlice words) =
      .ok (wordSlice (mapWords shiftWord3 words)) := by
  have hlength : (wordSlice words).length = 8 := by simp [wordSlice, Words.list]
  have hlen : Slice.len (wordSlice words) = 8#usize := by scalar_tac
  simp only [RustCryptoAesLinear.soft.fixslice.shift_rows_3]
  simp [hlen, massert, core.slice.Slice.iter_mut]
  unfold RustCryptoAesLinear.soft.fixslice.shift_rows_3_loop
  iterate 9 (rw [loop]; dsimp only; rw [shift3_body]; simp [hlength])
  rfl

theorem shift1_rejects_shape (words : Slice U64) (h : Slice.len words ≠ 8#usize) :
    RustCryptoAesLinear.soft.fixslice.shift_rows_1 words = .fail .assertionFailure := by
  simp [RustCryptoAesLinear.soft.fixslice.shift_rows_1, massert, h]

theorem shift2_rejects_shape (words : Slice U64) (h : Slice.len words ≠ 8#usize) :
    RustCryptoAesLinear.soft.fixslice.shift_rows_2 words = .fail .assertionFailure := by
  simp [RustCryptoAesLinear.soft.fixslice.shift_rows_2, massert, h]

theorem shift3_rejects_shape (words : Slice U64) (h : Slice.len words ≠ 8#usize) :
    RustCryptoAesLinear.soft.fixslice.shift_rows_3 words = .fail .assertionFailure := by
  simp [RustCryptoAesLinear.soft.fixslice.shift_rows_3, massert, h]

end LibSignalReference.Proofs.AesLinear
