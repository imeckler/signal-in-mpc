import MetadataWork.Generated.ShaCompactStep.Funs
import ShaCompactWork.Circuit
import LibSignalReference.Proofs.Sha256Round

namespace SignalReference.ShaCompact

open Aeneas Aeneas.Std TlsMpc.Sha256
open CandidateShaStep

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000


def tuple (s : State (BitVec 32)) : U32 × U32 × U32 × U32 × U32 × U32 × U32 × U32 :=
  (⟨s.a⟩, ⟨s.b⟩, ⟨s.c⟩, ⟨s.d⟩, ⟨s.e⟩, ⟨s.f⟩, ⟨s.g⟩, ⟨s.h⟩)

def value (block : Array U32 16#usize) : List (BitVec 32) := block.val.map UScalar.bv

def next (i : Usize) (hi : i.val < 64) : Usize :=
  Usize.ofNatCore (i.val + 1) (by scalar_tac)

theorem next_val (i : Usize) (hi : i.val < 64) : (next i hi).val = i.val + 1 := by rfl

theorem range_next (i : Usize) (hi : i.val < 64) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨i,64#usize⟩ =
      .ok (some i, ⟨next i hi,64#usize⟩) := by
  have hb : i.val < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked, core.cmp.impls.PartialOrdUsize.lt, hi, hb, next]
  rfl

theorem range_done :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨64#usize,64#usize⟩ =
      .ok (none, ⟨64#usize,64#usize⟩) := by rfl

theorem value_get (block : Array U32 16#usize) (i : Nat) :
    (value block)[i ]?.getD 0#32 = (block.val[i]?.getD 0#u32).bv := by
  simp only [value, List.getElem?_map]
  cases block.val[i]? <;> rfl

theorem value_index (block : Array U32 16#usize) (i : Nat) (hi : i < 16) :
    (value block)[i ]?.getD 0#32 = (block.val[i]'(by simp; exact hi)).bv := by
  have hb : i < block.val.length := by simpa using hi
  simp [value, List.getElem?_eq_getElem hb]

theorem value_mod (block : Array U32 16#usize) (i : Nat) :
    (value block)[i % 16 ]?.getD 0#32 = (block.val[i % 16]'(by simp; omega)).bv :=
  value_index block (i % 16) (by omega)

theorem mapped_mod (block : Array U32 16#usize) (i : Nat) :
    (block.val.map UScalar.bv)[i % 16]?.getD 0#32 =
      (block.val[i % 16]'(by simp; omega)).bv := value_mod block i

theorem k32_value : consts.K32.val = constants.map (fun n => (⟨BitVec.ofNat 32 n⟩ : U32)) := by
  unfold consts.K32 constants
  rfl

theorem k32_get (i : Nat) (hi : i < 64) :
    (consts.K32.val[i]'(by simp; exact hi)).bv = BitVec.ofNat 32 (constants[i]?.getD 0) := by
  have hc : i < constants.length := by change i < 64; exact hi
  simp only [k32_value, List.getElem_map, List.getElem?_eq_getElem hc, Option.getD_some]

theorem body_spec (i : Usize) (hi : i.val < 64) (block : Array U32 16#usize)
    (s : State (BitVec 32)) :
    sha256.soft.compact.compress_u32_loop.body ⟨i,64#usize⟩ block
      ⟨s.a⟩ ⟨s.b⟩ ⟨s.c⟩ ⟨s.d⟩ ⟨s.e⟩ ⟨s.f⟩ ⟨s.g⟩ ⟨s.h⟩
      ⦃ result =>
        let scheduled := TlsMpc.Signal.ShaCompact.schedule concrete i.val (value block)
        let t := round concrete (constants[i.val]?.getD 0) scheduled.2 s
        ∃ updated,
          value updated = scheduled.1 ∧
          result = .cont (⟨next i hi,64#usize⟩, updated,
            (⟨t.a⟩ : U32), (⟨t.b⟩ : U32), (⟨t.c⟩ : U32), (⟨t.d⟩ : U32),
            (⟨t.e⟩ : U32), (⟨t.f⟩ : U32), (⟨t.g⟩ : U32), (⟨t.h⟩ : U32)) ⦄ := by
  unfold sha256.soft.compact.compress_u32_loop.body
  rw [range_next i hi]
  step*
  · have early : i.val < 16 := by scalar_tac
    refine ⟨block, by simp [TlsMpc.Signal.ShaCompact.schedule, early], ?_⟩
    simp_all [TlsMpc.Signal.ShaCompact.schedule, early, round, concrete,
      big0, big1, choose, majority, xor3,
      core.num.U32.wrapping_add, UScalar.wrapping_add,
      core.num.U32.rotate_right, UScalar.rotate_right,
      ControlFlow.cont.injEq, Prod.mk.injEq, UScalar.eq_equiv_bv_eq,
      UScalar.bv_xor, UScalar.bv_and, UScalar.bv_not,
      k32_get i.val hi, value_index block i.val early]
    ac_rfl
  · have late : ¬ i.val < 16 := by scalar_tac
    refine ⟨a1, ?_, ?_⟩
    · rw [a1_post]
      simp only [value, Array.set_val_eq, List.map_set]
      change (value block).set i21.val new_w.bv = _
      rw [i21_post]
      simp only [TlsMpc.Signal.ShaCompact.schedule, if_neg late, Prod.fst]
      congr 1
      with_unfolding_all simp only [small0, small1, xor3, concrete, value_mod]
      simp only [new_w_post, i20_post, i16_post, core.num.U32.wrapping_add,
        UScalar.wrapping_add, i15_post, i19_post, s0_post2, i5_post2, i3_post,
        i4_post, i6_post2, w15_post, s1_post2, i11_post2, i9_post, i10_post,
        i12_post2, w2_post, core.num.U32.rotate_right, UScalar.rotate_right]
      simp only [i14_post, i13_post1, i18_post, i17_post1, i2_post, i1_post1,
        i8_post, i7_post1]
      have hb (j : Nat) : j % 16 < block.val.length := by simp; omega
      simp only [List.getElem?_map,
        List.getElem?_eq_getElem (hb (i.val - 16)),
        List.getElem?_eq_getElem (hb (i.val - 15)),
        List.getElem?_eq_getElem (hb (i.val - 7)),
        List.getElem?_eq_getElem (hb (i.val - 2)), Option.map_some, Option.getD_some]
      rfl
    · simp_all [TlsMpc.Signal.ShaCompact.schedule, late, round, concrete,
        big0, big1, small0, small1, choose, majority, xor3,
        core.num.U32.wrapping_add, UScalar.wrapping_add,
        core.num.U32.rotate_right, UScalar.rotate_right,
        ControlFlow.cont.injEq, Prod.mk.injEq, UScalar.eq_equiv_bv_eq,
        UScalar.bv_xor, UScalar.bv_and, UScalar.bv_not,
        k32_get i.val hi, value_mod]
      have late2 : ¬ i.val < 16 := by omega
      with_unfolding_all simp only [if_neg late2, Prod.snd, value_mod]
      ac_rfl

end SignalReference.ShaCompact
