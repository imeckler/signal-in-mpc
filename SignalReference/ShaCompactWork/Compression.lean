import ShaCompactWork.Reference

namespace SignalReference.ShaCompact

open Aeneas Aeneas.Std TlsMpc.Sha256
open CandidateShaStep

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem loop_spec (i : Usize) (hi : i.val ≤ 64) (block : Array U32 16#usize)
    (s : State (BitVec 32)) :
    sha256.soft.compact.compress_u32_loop ⟨i,64#usize⟩ block
      ⟨s.a⟩ ⟨s.b⟩ ⟨s.c⟩ ⟨s.d⟩ ⟨s.e⟩ ⟨s.f⟩ ⟨s.g⟩ ⟨s.h⟩ =
      .ok (tuple (TlsMpc.Signal.ShaCompact.run concrete (64 - i.val) i.val (value block) s)) := by
  generalize hcount : 64 - i.val = count
  induction count using Nat.strong_induction_on generalizing i block s with
  | h count ih =>
    by_cases hend : i.val = 64
    · have heq : i = 64#usize := by scalar_tac
      subst i
      have hc : count = 0 := by simpa using hcount.symm
      subst count
      unfold sha256.soft.compact.compress_u32_loop
      rw [loop]
      simp [sha256.soft.compact.compress_u32_loop.body, range_done,
        TlsMpc.Signal.ShaCompact.run, tuple]
    · have hlt : i.val < 64 := by omega
      obtain ⟨result, hr, updated, hvalue, hresult⟩ := WP.spec_imp_exists (body_spec i hlt block s)
      rw [hresult] at hr
      unfold sha256.soft.compact.compress_u32_loop
      rw [loop]
      dsimp only
      rw [hr]
      have hn : (next i hlt).val ≤ 64 := by rw [next_val]; omega
      have hc : 64 - (next i hlt).val < count := by rw [next_val]; omega
      have hs : count = (64 - (next i hlt).val) + 1 := by rw [next_val]; omega
      rw [hs, TlsMpc.Signal.ShaCompact.run]
      simpa only [sha256.soft.compact.compress_u32_loop, next_val, hvalue, tuple] using
        ih (64 - (next i hlt).val) hc (next i hlt) hn updated
          (round concrete (constants[i.val]?.getD 0)
            (TlsMpc.Signal.ShaCompact.schedule concrete i.val (value block)).2 s) rfl

open LibSignalReference.Proofs.Sha256Round

theorem compress_spec (s : State (BitVec 32)) (block : Array U32 16#usize) :
    sha256.soft.compact.compress_u32 (encodeState s) block =
      .ok (encodeState (TlsMpc.Signal.ShaCompact.compress concrete s (value block))) := by
  have hl := loop_spec 0#usize (by decide) block s
  change sha256.soft.compact.compress_u32_loop ⟨0#usize,64#usize⟩ block
    ⟨s.a⟩ ⟨s.b⟩ ⟨s.c⟩ ⟨s.d⟩ ⟨s.e⟩ ⟨s.f⟩ ⟨s.g⟩ ⟨s.h⟩ =
      .ok (tuple (TlsMpc.Signal.ShaCompact.run concrete 64 0 (value block) s)) at hl
  generalize ht : TlsMpc.Signal.ShaCompact.run concrete 64 0 (value block) s = t at hl
  unfold TlsMpc.Signal.ShaCompact.compress
  rw [ht]
  simp only [tuple] at hl
  unfold sha256.soft.compact.compress_u32
  simp only [encodeState, Array.index_usize, Array.getElem?_Usize_eq,
    UScalar.ofNatCore_val_eq, Usize.ofNatCore, List.getElem?_cons_zero,
    List.getElem?_cons_succ, bind_tc_ok, hl]
  rfl

end SignalReference.ShaCompact
