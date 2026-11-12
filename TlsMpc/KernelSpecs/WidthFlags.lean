import TlsMpc.KernelSpecs.SignalKernels

/-!
# What the `signal-widths` flags mean

New file; it changes no definition and no emitter imports it.

`signal-widths` opens `widthFlagsWith` of the session's counters and epoch
(`signalWidths_spec`, `TlsMpc/KernelSpecs/SignalKernels.lean`). This file proves what a flag says.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `widthFlags_value`: for a big-endian byte string `bytes` with value `v` (`bigEndian bytes`),
  flag `k` (k = 0, 1, …) is 255 exactly when `v ≥ 2^(7(k+1))`, and 0 otherwise. So the number of
  255 flags is the number of 7-bit groups after the first: a varint of `v` takes
  `1 + (number of 255 flags)` bytes (as long as enough groups were asked for). When
  `7(k+1) ≥ 8 · bytes.length` the flag is 0 (the value is below `2^(8 · length)`).
* `signalWidths_value`: the kernel-level statement, `signalWidths_spec` with every flag list
  replaced by these comparisons.
-/
namespace TlsMpc.KernelSpecs.WidthFlags
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open SignalKernels (widthFlagsWith)

/-- The value of a big-endian byte string. -/
def bigEndian (bytes : List (BitVec 8)) : Nat := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

theorem bigEndian_snoc (bs : List (BitVec 8)) (b : BitVec 8) :
    bigEndian (bs ++ [b]) = 2 ^ 8 * bigEndian bs + b.toNat := by
  simp only [bigEndian, List.foldl_append, List.foldl_cons, List.foldl_nil]
  omega

theorem bigEndian_lt (bytes : List (BitVec 8)) : bigEndian bytes < 2 ^ (8 * bytes.length) := by
  obtain ⟨r, rfl⟩ : ∃ r, bytes = r.reverse := ⟨bytes.reverse, by simp⟩
  induction r with
  | nil => simp [bigEndian]
  | cons b r ih =>
      rw [List.reverse_cons, bigEndian_snoc, List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one,
        Nat.pow_add]
      have hb := b.isLt
      have : bigEndian r.reverse + 1 ≤ 2 ^ (8 * r.reverse.length) := ih
      calc 2 ^ 8 * bigEndian r.reverse + b.toNat < 2 ^ 8 * bigEndian r.reverse + 2 ^ 8 := by omega
        _ = 2 ^ 8 * (bigEndian r.reverse + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ 2 ^ 8 * 2 ^ (8 * r.reverse.length) := Nat.mul_le_mul_left _ this
        _ = 2 ^ (8 * r.reverse.length) * 2 ^ 8 := Nat.mul_comm _ _

/-- Bit `j` of the value is bit `j % 8` of byte `n − 1 − j / 8`. -/
theorem testBit_bigEndian (bytes : List (BitVec 8)) (j : Nat) (hj : j < 8 * bytes.length) :
    (bigEndian bytes).testBit j = (bytes.getD (bytes.length - 1 - j / 8) 0).getLsbD (j % 8) := by
  obtain ⟨r, rfl⟩ : ∃ r, bytes = r.reverse := ⟨bytes.reverse, by simp⟩
  induction r generalizing j with
  | nil => simp at hj
  | cons b r ih =>
      simp only [List.reverse_cons] at hj ⊢
      rw [bigEndian_snoc, Nat.testBit_two_pow_mul_add _ b.isLt]
      simp only [List.length_append, List.length_singleton] at hj ⊢
      by_cases small : j < 8
      · rw [if_pos small, show r.reverse.length + 1 - 1 - j / 8 = r.reverse.length by
          rw [Nat.div_eq_of_lt small]; omega, Nat.mod_eq_of_lt small]
        simp [List.getD_eq_getElem?_getD, BitVec.testBit_toNat]
      · rw [if_neg small, ih (j - 8) (by omega)]
        have idx : r.reverse.length + 1 - 1 - j / 8 = r.reverse.length - 1 - (j - 8) / 8 := by omega
        have lt : r.reverse.length - 1 - (j - 8) / 8 < r.reverse.length := by omega
        rw [idx, show (j - 8) % 8 = j % 8 by omega]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left lt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem maskBit_value (x : BitVec 8) (i : Nat) (hi : i < 8) :
    ByteAuth.concrete.maskBit x i = if x.getLsbD i then 255 else 0 := by
  have all : ∀ x : BitVec 8, ∀ i : Fin 8, ByteAuth.concrete.maskBit x i = if x.getLsbD i then 255 else 0 := by
    decide +kernel
  exact all x ⟨i, hi⟩

theorem zero_ne : (0 : BitVec 8) ≠ 255 := by decide

theorem ite_iff {α : Type} {c d : Prop} [Decidable c] [Decidable d] (h : c ↔ d) (x y : α) :
    (if c then x else y) = (if d then x else y) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos (h.mp hc)]
  · rw [if_neg hc, if_neg (fun hd => hc (h.mpr hd))]

theorem either_value (x y : BitVec 8) (hx : x = 0 ∨ x = 255) (hy : y = 0 ∨ y = 255) :
    TlsWebSocketUpgrade.either ByteAuth.concrete x y = if x = 255 ∨ y = 255 then 255 else 0 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

/-- The flag fold: 255 exactly when some index in the list passes the guard with its bit set. -/
theorem flagFold (m : Nat) (bit : Nat → BitVec 8) (hbit : ∀ j, bit j = 0 ∨ bit j = 255) :
    ∀ (js : List Nat) (acc : BitVec 8), (acc = 0 ∨ acc = 255) →
      js.foldl (fun acc j => if m ≤ j then TlsWebSocketUpgrade.either ByteAuth.concrete acc (bit j) else acc) acc =
        if acc = 255 ∨ ∃ j ∈ js, m ≤ j ∧ bit j = 255 then 255 else 0
  | [], acc, hacc => by
      rcases hacc with rfl | rfl
      · simp [zero_ne]
      · simp
  | j :: js, acc, hacc => by
      simp only [List.foldl_cons]
      have next : ∀ acc' : BitVec 8, (acc' = 0 ∨ acc' = 255) →
          (acc' = 255 ↔ (acc = 255 ∨ (m ≤ j ∧ bit j = 255))) →
          (if acc' = 255 ∨ ∃ k ∈ js, m ≤ k ∧ bit k = 255 then (255 : BitVec 8) else 0) =
            if acc = 255 ∨ ∃ k ∈ j :: js, m ≤ k ∧ bit k = 255 then 255 else 0 := by
        intro acc' _ hiff
        refine ite_iff ?_ _ _
        rw [hiff]
        constructor
        · rintro ((h | h) | ⟨k, hk, hmk⟩)
          · exact Or.inl h
          · exact Or.inr ⟨j, List.mem_cons_self, h⟩
          · exact Or.inr ⟨k, List.mem_cons_of_mem j hk, hmk⟩
        · rintro (h | ⟨k, hk, hmk⟩)
          · exact Or.inl (Or.inl h)
          · rcases List.mem_cons.mp hk with rfl | hk
            · exact Or.inl (Or.inr hmk)
            · exact Or.inr ⟨k, hk, hmk⟩
      by_cases hj : m ≤ j
      · rw [if_pos hj, either_value acc (bit j) hacc (hbit j)]
        have h01 : (if acc = 255 ∨ bit j = 255 then (255 : BitVec 8) else 0) = 0 ∨
            (if acc = 255 ∨ bit j = 255 then (255 : BitVec 8) else 0) = 255 := by split <;> simp
        rw [flagFold m bit hbit js _ h01]
        apply next _ h01
        constructor
        · intro h
          by_cases c : acc = 255 ∨ bit j = 255
          · rcases c with c | c
            · exact Or.inl c
            · exact Or.inr ⟨hj, c⟩
          · rw [if_neg c] at h; exact absurd h zero_ne
        · rintro (h | ⟨_, h⟩)
          · rw [if_pos (Or.inl h)]
          · rw [if_pos (Or.inr h)]
      · rw [if_neg hj, flagFold m bit hbit js acc hacc]
        apply next _ hacc
        constructor
        · exact Or.inl
        · rintro (h | ⟨h, _⟩)
          · exact h
          · exact absurd h hj

/-- `v ≥ 2^m` exactly when some bit `j ≥ m` (below the width) is set. -/
theorem ge_pow_iff (v m width : Nat) (hv : v < 2 ^ width) :
    2 ^ m ≤ v ↔ ∃ j, j < width ∧ m ≤ j ∧ v.testBit j = true := by
  constructor
  · intro hge
    apply Classical.byContradiction
    intro none
    have : v < 2 ^ m := Nat.lt_pow_two_of_testBit v (fun i hi => by
      cases h : v.testBit i
      · rfl
      · by_cases wi : i < width
        · exact absurd ⟨i, wi, hi, h⟩ none
        · have : v < 2 ^ i := Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega))
          rw [Nat.testBit_lt_two_pow this] at h
          exact (Bool.false_ne_true h).elim)
    omega
  · rintro ⟨j, _, hmj, hb⟩
    have : ¬ v < 2 ^ j := fun lt => by rw [Nat.testBit_lt_two_pow lt] at hb; exact Bool.false_ne_true hb
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hmj) (by omega)

/-- **Flag `k` of `widthFlagsWith` is 255 exactly when the big-endian value is at least
`2^(7(k+1))`.** -/
theorem widthFlags_value (bytes : List (BitVec 8)) (groups : Nat) :
    widthFlagsWith ByteAuth.concrete 0 bytes groups =
      (List.range groups).map (fun k => if 2 ^ (7 * (k + 1)) ≤ bigEndian bytes then 255 else 0) := by
  simp only [widthFlagsWith]
  apply List.map_congr_left
  intro k _
  have hbit : ∀ j, ByteAuth.concrete.maskBit (bytes.getD (bytes.length - 1 - j / 8) 0) (j % 8) = 0 ∨
      ByteAuth.concrete.maskBit (bytes.getD (bytes.length - 1 - j / 8) 0) (j % 8) = 255 := by
    intro j
    rw [maskBit_value _ _ (Nat.mod_lt _ (by decide))]
    split <;> simp
  rw [show (ByteAuth.concrete.const 0 : BitVec 8) = 0 from rfl,
    flagFold (7 * (k + 1)) _ hbit (List.range (8 * bytes.length)) 0 (Or.inl rfl)]
  refine ite_iff ?_ _ _
  rw [ge_pow_iff (bigEndian bytes) (7 * (k + 1)) (8 * bytes.length) (bigEndian_lt bytes)]
  simp only [List.mem_range, zero_ne, false_or]
  constructor
  · rintro ⟨j, hj, hmj, hb⟩
    refine ⟨j, hj, hmj, ?_⟩
    rw [testBit_bigEndian bytes j hj]
    rw [maskBit_value _ _ (Nat.mod_lt _ (by decide))] at hb
    split at hb
    · assumption
    · exact absurd hb zero_ne
  · rintro ⟨j, hj, hmj, hb⟩
    refine ⟨j, hj, hmj, ?_⟩
    rw [maskBit_value _ _ (Nat.mod_lt _ (by decide)), ← testBit_bigEndian bytes j hj, hb, if_pos rfl]

open TlsMpc.HybridKernel (lookup) in
/-- **`signal-widths` opens the width comparisons of the session's counter, previous counter,
SPQR epoch and next counter**: flag `k` of each list is 255 exactly when the big-endian value is
at least `2^(7(k+1))`, else 0. -/
theorem signalWidths_value (cert : Nat) (assign : BVExpr.Assignment) :
    let session := (((lookup (SignalKernels.widthsInputs cert) "conversation").map (BVExpr.eval assign)).drop cert).take 262
    let flags := fun (bytes : List (BitVec 8)) (groups : Nat) =>
      (List.range groups).map (fun k => if 2 ^ (7 * (k + 1)) ≤ bigEndian bytes then (255 : BitVec 8) else 0)
    (HybridKernel.signalWidths cert).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [flags ((session.drop 1).take 4) 4, flags ((session.drop 5).take 4) 4, flags ((session.drop 109).take 8) 9,
        flags (ChainSend.nextCounter Sha256.concrete ByteAuth.concrete ((session.drop 105).take 4)) 4] := by
  intro session flags
  rw [SignalKernels.signalWidths_spec]
  simp only [widthFlags_value]
  rfl

#print axioms widthFlags_value
#print axioms signalWidths_value

end TlsMpc.KernelSpecs.WidthFlags
