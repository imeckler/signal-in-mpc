import AesKeyScheduleWork.Generated.Funs
import LibSignalReference.Proofs.ShaCompactReference

namespace LibSignalReference.Candidate.AesKeyCopy

open Aeneas Aeneas.Std
open RustCryptoAesKeySchedule

set_option maxHeartbeats 2000000

def copyBackward (src dst : Nat) : Nat → Slice U64 → Slice U64
  | 0, words => words
  | n + 1, words => copyBackward src dst n
      (words.setAtNat (dst + n) (words.val[src + n]?.getD 0#u64))

theorem copyBackward_length (src dst n : Nat) (words : Slice U64) :
    (copyBackward src dst n words).length = words.length := by
  induction n generalizing words with
  | zero => rfl
  | succ n ih => simp [copyBackward, ih]

theorem reverse_next (finish : Usize) (hf : 0 < finish.val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      ⟨⟨0#usize, finish⟩⟩ =
      .ok (some (Usize.ofNatCore (finish.val - 1) (by scalar_tac)),
        ⟨⟨0#usize, Usize.ofNatCore (finish.val - 1) (by scalar_tac)⟩⟩) := by
  have hf1 : 1 ≤ finish.val := hf
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hf, hf1]
  rfl

theorem reverse_done :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      ⟨⟨0#usize, 0#usize⟩⟩ = .ok (none, ⟨⟨0#usize, 0#usize⟩⟩) := by
  rfl

theorem copy_body (src dst finish : Usize) (words : Slice U64)
    (hf : 0 < finish.val)
    (hsrc : src.val + finish.val ≤ words.length)
    (hdst : dst.val + finish.val ≤ words.length) :
    soft.fixslice.memshift32_loop.body src dst ⟨⟨0#usize, finish⟩⟩ words =
      .ok (.cont (⟨⟨0#usize, Usize.ofNatCore (finish.val - 1) (by scalar_tac)⟩⟩,
        words.setAtNat (dst.val + (finish.val - 1))
          (words.val[src.val + (finish.val - 1)]?.getD 0#u64))) := by
  let last := Usize.ofNatCore (finish.val - 1) (by scalar_tac)
  have hlast : last.val = finish.val - 1 := rfl
  have hsrcMax : src.val + last.val ≤ Usize.max := by scalar_tac
  have hdstMax : dst.val + last.val ≤ Usize.max := by scalar_tac
  obtain ⟨source, hs, hsource⟩ := WP.spec_imp_exists (Usize.add_spec (x := src) (y := last) hsrcMax)
  obtain ⟨destination, hd, hdest⟩ := WP.spec_imp_exists (Usize.add_spec (x := dst) (y := last) hdstMax)
  have hslt : source.val < words.length := by omega
  have hdlt : destination.val < words.length := by omega
  have hsindex : src.val + (finish.val - 1) < words.val.length := by change _ < words.length; omega
  have hdindex : dst.val + (finish.val - 1) < words.val.length := by change _ < words.length; omega
  rw [soft.fixslice.memshift32_loop.body, reverse_next finish hf]
  with_unfolding_all change (show Result (ControlFlow
      (core.iter.adapters.rev.Rev (core.ops.range.Range Usize) × Slice U64) (Slice U64)) from do
    let i1 ← src + last
    let value ← Slice.index_usize words i1
    let i3 ← dst + last
    let next ← Slice.update words i3 value
    .ok (.cont (⟨⟨0#usize,last⟩⟩,next))) = _
  with_unfolding_all rw [hs]
  with_unfolding_all simp [hs, hd, Slice.index_usize, Slice.update, hslt, hdlt,
    Slice.setAtNat, hsource, hdest, hlast, List.getElem?_eq_getElem hsindex,
    List.getElem?_eq_getElem hdindex]
  rfl

theorem copy_loop (src dst finish : Usize) (words : Slice U64)
    (hsrc : src.val + finish.val ≤ words.length)
    (hdst : dst.val + finish.val ≤ words.length) :
    soft.fixslice.memshift32_loop ⟨⟨0#usize, finish⟩⟩ words src dst =
      .ok (copyBackward src.val dst.val finish.val words) := by
  generalize hn : finish.val = count
  induction count generalizing finish words with
  | zero =>
    have hf : finish = 0#usize := by scalar_tac
    subst finish
    unfold soft.fixslice.memshift32_loop
    rw [loop]
    simp [soft.fixslice.memshift32_loop.body, reverse_done, copyBackward]
  | succ count ih =>
    have hf : 0 < finish.val := by omega
    let last := Usize.ofNatCore (finish.val - 1) (by scalar_tac)
    have hlast : last.val = count := by change finish.val - 1 = count; omega
    let updated := words.setAtNat (dst.val + (finish.val - 1))
      (words.val[src.val + (finish.val - 1)]?.getD 0#u64)
    have hul : updated.length = words.length := by simp [updated, Slice.length]
    have hs' : src.val + last.val ≤ updated.length := by rw [hul]; omega
    have hd' : dst.val + last.val ≤ updated.length := by rw [hul]; omega
    unfold soft.fixslice.memshift32_loop
    rw [loop]
    dsimp only
    rw [copy_body src dst finish words hf hsrc hdst]
    simpa only [soft.fixslice.memshift32_loop, hn, copyBackward, Nat.add_sub_cancel,
      updated, last] using ih last updated hs' hd' hlast

theorem memshift32_spec (src : Usize) (words : Slice U64)
    (halign : src.val % 8 = 0) (hsize : src.val + 16 ≤ words.length) :
    soft.fixslice.memshift32 words src =
      .ok (copyBackward src.val (src.val + 8) 8 words) := by
  have hmod : ((src % 8#usize) : Result Usize) = .ok 0#usize := by
    obtain ⟨remainder, hr, hv⟩ := WP.spec_imp_exists (Usize.rem_spec src (y := 8#usize) (by decide))
    have hz : remainder = 0#usize := by scalar_tac
    simpa only [hz] using hr
  have hm1 : src.val + (8#usize).val ≤ Usize.max := by scalar_tac
  obtain ⟨dst, hd, hdst⟩ := WP.spec_imp_exists (Usize.add_spec (x := src) (y := 8#usize) hm1)
  have hm2 : dst.val + (8#usize).val ≤ Usize.max := by scalar_tac
  obtain ⟨finish, hf, hfinish⟩ := WP.spec_imp_exists (Usize.add_spec (x := dst) (y := 8#usize) hm2)
  have hbound : finish ≤ Slice.len words := by scalar_tac
  have hs : src.val + (8#usize).val ≤ words.length := by scalar_tac
  have hdst' : dst.val + (8#usize).val ≤ words.length := by scalar_tac
  simp only [soft.fixslice.memshift32, hmod, bind_tc_ok, massert, hd, hf]
  simp [hbound, core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default, copy_loop src dst 8#usize words hs hdst', hdst]

end LibSignalReference.Candidate.AesKeyCopy
