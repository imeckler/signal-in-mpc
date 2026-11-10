/-
Copyright 2025-2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in SignalReference/licenses/baf-apache-2.0.txt.
Selected proof adaptations for pinned dalek source; see baf-provenance.json.
-/
import XEdDsaReferenceWork.Generated.FieldDecode.Funs
open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Aeneas.Std.Array
/-- Local finite-sum definition; equivalent to little-endian base-2^bits digits. -/
def asNat {ty : UScalarTy} {n : Usize} (bits : Nat) (a : Array (UScalar ty) n) : Nat :=
  ∑ j ∈ Finset.range n.val, 2 ^ (bits*j) * a[j]!.val

theorem asNat_eq_sum {ty : UScalarTy} {n : Usize} (bits : Nat) (a : Array (UScalar ty) n) :
    a.asNat bits = ∑ j ∈ Finset.range n.val, 2 ^ (bits*j) * a[j]!.val := rfl
theorem index_usize_getElem!_spec {α : Type} [Inhabited α] {n : Usize} (v : Array α n) (i : Usize)
    (hi : i.val < n.val) :
    v.index_usize i ⦃ (x : α) => x = v[i.val]! ⦄ := by
  step*
  simp_lists [*]

/-- `Slice.index_usize` with the result as `getElem!`. Activated with
`open scoped Helpers.IndexStep Helpers.UpdateStep`. -/
theorem _root_.Aeneas.Std.Slice.index_usize_getElem!_spec {α : Type} [Inhabited α] (s : Slice α)
    (i : Usize) (hi : i.val < s.length) :
    s.index_usize i ⦃ (x : α) => x = s[i.val]! ⦄ := by
  step*
  simp_lists [*]

end Aeneas.Std.Array
theorem _root_.Nat.forall_lt_five {P : ℕ → Prop} :
    (∀ i : ℕ, i < 5 → P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i hi
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4

namespace Nat
theorem sum_pow_mul_lt (bits k : ℕ) (x : ℕ → ℕ) (hx : ∀ j < k, x j < 2 ^ bits) :
    ∑ j ∈ Finset.range k, 2 ^ (bits * j) * x j < 2 ^ (bits * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_succ, Nat.pow_add]
    calc ∑ j ∈ Finset.range k, 2 ^ (bits * j) * x j + 2 ^ (bits * k) * x k
        < 2 ^ (bits * k) + 2 ^ (bits * k) * x k :=
          Nat.add_lt_add_right (ih fun j hj => hx j (by omega)) _
      _ = 2 ^ (bits * k) * (x k + 1) := by ring
      _ ≤ 2 ^ (bits * k) * 2 ^ bits := Nat.mul_le_mul_left _ (hx k (by omega))

end Nat
namespace Aeneas.Std
theorem UScalar.and_two_pow_sub_one_spec {ty : UScalarTy} (x m : UScalar ty) (n : ℕ)
    (hm : m.val = 2 ^ n - 1) :
    lift (x &&& m) ⦃ (r : UScalar ty) => r.val = x.val % 2 ^ n ⦄ := by
  step*
  simp only [*, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod]

end Aeneas.Std
namespace Nat
theorem or_shiftLeft_eq_add_pow_mul {acc k : ℕ} (b : ℕ) (hacc : acc < 2 ^ k) :
    acc ||| b <<< k = acc + 2 ^ k * b := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hacc, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.add_comm]

end Nat
namespace Helpers.IndexStep
attribute [scoped step] Array.index_usize_getElem!_spec Slice.index_usize_getElem!_spec
end Helpers.IndexStep
namespace Helpers.MaskStep
attribute [scoped step] UScalar.and_two_pow_sub_one_spec
end Helpers.MaskStep
namespace XEdDsaReference.backend.serial.u64.field.FieldElement51
def asNat (r : FieldElement51) : Nat :=
  r[0]!.val + 2^51*r[1]!.val + 2^102*r[2]!.val + 2^153*r[3]!.val + 2^204*r[4]!.val
theorem asNat_eq (r : FieldElement51) :
  r.asNat = r[0]!.val + 2^51*r[1]!.val + 2^102*r[2]!.val + 2^153*r[3]!.val + 2^204*r[4]!.val := rfl
abbrev LimbsLt (n : Nat) (r : FieldElement51) := ∀ i < 5, r[i]!.val < 2^n
end XEdDsaReference.backend.serial.u64.field.FieldElement51
