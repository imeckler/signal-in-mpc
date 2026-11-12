import TlsMpc.KernelSpecs.RequestCtr

/-!
# The padded decimal slot encoder against the decimal digits of the number

New file; it changes no definition and no emitter imports it.

The device id (3 bytes) and registration id (10 bytes) slots of the request kernels are
`paddedDecimalWith` over `PrivateDecimal.encode` (`HybridKernel.paddedDecimal` on values).

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`; the mask-only part of the
encoder, a function of the digit count 1..20, by `decide +kernel`):

* `paddedDecimal_value`: for every 64-bit number `w` and slot width below 20, the validity byte is
  255 exactly when `numDigits w ≤ width`, and the slot is `refPadded w width`: the decimal digits
  of `w` (`refDecimal`, written independently: digit `j` is `w / 10^j % 10`, most significant first,
  `numDigits` digits, one for 0) followed by spaces up to `width`.
  On the way: `decimalMask_value` (mask k is 255 exactly when `w` has k digits), `encode_value`
  (the private buffer holds the digits and the length `numDigits w`).
* `parseDecimal_refDecimal`, `parsePadded_refPadded`, `paddedDecimal_parse`: reading the digits
  before the first space gives the number back, for every valid slot.
-/
namespace TlsMpc.KernelSpecs.SlotDecimal
open TlsMpc TlsMpc.Signal

abbrev Byte := BitVec 8

/-- The 20 digit-count masks when the number has `L` digits: 255 at position `L − 1`. -/
def ind (L : Nat) : List Byte := (List.range 20).map (fun i => if i + 1 = L then 255 else 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Everything `PrivateDecimal.encode` computes from the masks alone, for each digit count. -/
theorem fromMasks : ∀ L : Fin 21, L.val ≠ 0 →
    ByteAuth.equalMask ByteAuth.concrete
        (PrivateDecimal.count ByteAuth.concrete (ind L) (PrivateBuffer.publicLength ByteAuth.concrete 0))
        (PrivateBuffer.publicLength ByteAuth.concrete 1) = 255 ∧
      (List.range 16).map (PrivateDecimal.lengthBit ByteAuth.concrete (ind L)) =
        PrivateBuffer.publicLength ByteAuth.concrete L ∧
      PrivateBuffer.canonicalBits ByteAuth.concrete (PrivateBuffer.publicLength ByteAuth.concrete L) = 255 ∧
      PrivateBuffer.less ByteAuth.concrete (PrivateBuffer.publicLength ByteAuth.concrete 20)
        (PrivateBuffer.publicLength ByteAuth.concrete L) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lessTable : ∀ i : Fin 20, ∀ L : Fin 21,
    PrivateBuffer.less ByteAuth.concrete (PrivateBuffer.publicLength ByteAuth.concrete i)
      (PrivateBuffer.publicLength ByteAuth.concrete L) = if i.val < L.val then 255 else 0 := by
  decide +kernel

/-! ### The reference: decimal digits -/

/-- Number of decimal digits (1 for 0). -/
def numDigits (n : Nat) : Nat := if n < 10 then 1 else numDigits (n / 10) + 1
decreasing_by omega

/-- The decimal representation of `n` in ASCII, most significant digit first. -/
def refDecimal (n : Nat) : List Byte :=
  (List.range (numDigits n)).reverse.map (fun j => BitVec.ofNat 8 (48 + n / 10 ^ j % 10))

/-- The slot text: the digits, then spaces up to `width` (cut to `width` when too long). -/
def refPadded (n width : Nat) : List Byte := (refDecimal n ++ List.replicate width 32).take width

theorem numDigits_spec : ∀ n : Nat, 1 ≤ numDigits n ∧ n < 10 ^ numDigits n ∧
    (numDigits n = 1 ∨ 10 ^ (numDigits n - 1) ≤ n) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      unfold numDigits
      by_cases h : n < 10
      · simp [h]
      · rw [if_neg h]
        obtain ⟨_, lt, low⟩ := ih (n / 10) (by omega)
        refine ⟨by omega, ?_, Or.inr ?_⟩
        · rw [Nat.pow_succ]; omega
        · rw [show numDigits (n / 10) + 1 - 1 = numDigits (n / 10) by omega]
          rcases low with e | le
          · rw [e]; simp; omega
          · rw [show numDigits (n / 10) = numDigits (n / 10) - 1 + 1 by omega, Nat.pow_succ]; omega

theorem ite_iff {α : Type} {c d : Prop} [Decidable c] [Decidable d] (h : c ↔ d) (x y : α) :
    (if c then x else y) = (if d then x else y) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos (h.mp hc)]
  · rw [if_neg hc, if_neg (fun hd => hc (h.mpr hd))]

theorem pow_mono {a b : Nat} (h : a ≤ b) : 10 ^ a ≤ 10 ^ b := Nat.pow_le_pow_right (by decide) h

/-- `numDigits n = k` exactly when `10^(k−1) ≤ n < 10^k` (or `k = 1` and `n < 10`). -/
theorem numDigits_eq (n k : Nat) (hk : 1 ≤ k) :
    numDigits n = k ↔ n < 10 ^ k ∧ (k = 1 ∨ 10 ^ (k - 1) ≤ n) := by
  obtain ⟨h1, lt, low⟩ := numDigits_spec n
  constructor
  · rintro rfl; exact ⟨lt, low⟩
  · rintro ⟨lt', low'⟩
    apply Nat.le_antisymm
    · apply Classical.byContradiction; intro hc
      have : 10 ^ k ≤ 10 ^ (numDigits n - 1) := pow_mono (by omega)
      rcases low with e | le
      · omega
      · omega
    · apply Classical.byContradiction; intro hc
      have : 10 ^ numDigits n ≤ 10 ^ (k - 1) := pow_mono (by omega)
      rcases low' with e | le
      · omega
      · omega

theorem numDigits_le (n : Nat) (h : n < 2 ^ 64) : numDigits n ≤ 20 := by
  apply Classical.byContradiction; intro hc
  obtain ⟨_, _, low⟩ := numDigits_spec n
  have : 10 ^ 20 ≤ 10 ^ (numDigits n - 1) := pow_mono (by omega)
  rcases low with e | le
  · omega
  · have : (2 : Nat) ^ 64 ≤ 10 ^ 20 := by decide
    omega

/-! ### The circuit's pieces on concrete values -/

theorem pow_lt (i : Nat) (h : i ≤ 19) : 10 ^ i < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (pow_mono h) (by decide)

theorem digit_value (w : BitVec 64) (i : Nat) (h : i ≤ 19) :
    RelayEncoding.decimalConcrete.digit w i = BitVec.ofNat 8 (48 + w.toNat / 10 ^ i % 10) := by
  apply BitVec.eq_of_toNat_eq
  have hp := pow_lt i h
  simp only [RelayEncoding.decimalConcrete, BitVec.toNat_add, BitVec.extractLsb'_toNat, BitVec.toNat_umod,
    BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp, Nat.shiftRight_zero]
  have : w.toNat / 10 ^ i % 10 < 10 := Nat.mod_lt _ (by decide)
  simp only [show (10 : BitVec 64).toNat = 10 from rfl, show (48 : BitVec 8).toNat = 48 from rfl,
    show (2 : Nat) ^ 8 = 256 from rfl]
  omega

theorem extract_zero (q : BitVec 64) (s : Nat) : q.extractLsb' s 8 = 0 ↔ q.toNat / 2 ^ s % 256 = 0 := by
  rw [← BitVec.toNat_inj]
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- A number below `2^64` whose eight bytes are zero is zero. -/
theorem zero_of_bytes (Q : Nat) (lt : Q < 2 ^ 64) (h : ∀ k < 8, Q / 2 ^ (8 * k) % 256 = 0) : Q = 0 := by
  have step : ∀ k, Q / 2 ^ (8 * (k + 1)) = Q / 2 ^ (8 * k) / 256 := by
    intro k
    rw [Nat.div_div_eq_div_mul, show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
  have down : ∀ m, m ≤ 8 → Q / 2 ^ (8 * (8 - m)) = 0 := by
    intro m
    induction m with
    | zero => intro _; exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mpr lt
    | succ m ih =>
        intro hm
        have prev := ih (by omega)
        have e : 8 - m = (8 - (m + 1)) + 1 := by omega
        rw [e, step] at prev
        have hb := h (8 - (m + 1)) (by omega)
        omega
  have := down 8 (Nat.le_refl _)
  simpa using this

theorem quotient_value (w : BitVec 64) (p : Nat) (h : p ≤ 19) :
    ByteAuth.equalMask ByteAuth.concrete ((List.range 8).map (RelayEncoding.decimalConcrete.quotientByte w p))
        (List.replicate 8 (ByteAuth.concrete.const 0)) = if w.toNat < 10 ^ p then 255 else 0 := by
  rw [ByteAuth.equalMask_value]
  have hp := pow_lt p h
  have q : (w / BitVec.ofNat 64 (10 ^ p)).toNat = w.toNat / 10 ^ p := by
    simp only [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  have lt : w.toNat / 10 ^ p < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) w.isLt
  have pos : 0 < 10 ^ p := Nat.pow_pos (by decide)
  have small : w.toNat < 10 ^ p ↔ w.toNat / 10 ^ p = 0 := by
    rw [show (w.toNat / 10 ^ p = 0) ↔ w.toNat / 10 ^ p < 1 by omega, Nat.div_lt_iff_lt_mul pos, Nat.one_mul]
  apply ite_iff
  rw [small, show ByteAuth.concrete.const 0 = (0 : Byte) from rfl,
    show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    show List.replicate 8 (0 : Byte) = [0, 0, 0, 0, 0, 0, 0, 0] from rfl]
  simp only [List.map_cons, List.map_nil, RelayEncoding.decimalConcrete, List.cons.injEq, and_true, extract_zero, q]
  generalize w.toNat / 10 ^ p = Q at lt ⊢
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    apply zero_of_bytes Q lt
    intro k hk
    match k, hk with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | 6, _ => exact h6
    | 7, _ => exact h7
  · intro h0
    subst h0
    simp

theorem and_masks (A B : Prop) [Decidable A] [Decidable B] :
    ((if A then (255 : Byte) else 0) &&& (if B then 255 else 0)) = if A ∧ B then 255 else 0 := by
  by_cases a : A <;> by_cases b : B <;> simp [a, b]

theorem ofNat_digit_ne (d : Nat) (hd : d < 10) (h : d ≠ 0) : BitVec.ofNat 8 (48 + d) ≠ (48 : Byte) := by
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this
  rw [show (48 : Byte).toNat = 48 from rfl] at this
  omega

/-- **Mask `k` is 255 exactly when the number has `k` digits.** -/
theorem decimalMask_value (w : BitVec 64) (k : Nat) (h1 : 1 ≤ k) (h20 : k ≤ 20) :
    RelayEncoding.decimalMask RelayEncoding.decimalConcrete ByteAuth.concrete w k =
      if numDigits w.toNat = k then 255 else 0 := by
  have hw := w.isLt
  have F1 : (if k = 20 then ByteAuth.concrete.const 255 else ByteAuth.equalMask ByteAuth.concrete
      ((List.range 8).map (RelayEncoding.decimalConcrete.quotientByte w k))
      (List.replicate 8 (ByteAuth.concrete.const 0))) = if w.toNat < 10 ^ k then 255 else 0 := by
    by_cases h : k = 20
    · subst h
      have : (2 : Nat) ^ 64 ≤ 10 ^ 20 := by decide
      rw [if_pos rfl, if_pos (by omega)]
      rfl
    · rw [if_neg h, quotient_value w k (by omega)]
  have F2 : (if k = 1 then ByteAuth.concrete.const 255 else ByteAuth.concrete.not (ByteAuth.eqMask ByteAuth.concrete
      (RelayEncoding.decimalConcrete.digit w (k - 1)) (ByteAuth.concrete.const 48))) =
      if (k = 1 ∨ w.toNat / 10 ^ (k - 1) % 10 ≠ 0) then 255 else 0 := by
    by_cases h : k = 1
    · rw [if_pos h, if_pos (Or.inl h)]
      rfl
    · rw [if_neg h, digit_value w (k - 1) (by omega), show ByteAuth.concrete.const 48 = (48 : Byte) from rfl,
        ByteAuth.eqMask_value]
      have dl : w.toNat / 10 ^ (k - 1) % 10 < 10 := Nat.mod_lt _ (by decide)
      by_cases hd : w.toNat / 10 ^ (k - 1) % 10 = 0
      · rw [if_pos (by rw [hd]; rfl), if_neg (by simp [h, hd])]
        rfl
      · rw [if_neg (ofNat_digit_ne _ dl hd), if_pos (Or.inr hd)]
        rfl
  unfold RelayEncoding.decimalMask
  rw [F1, F2]
  show ((if w.toNat < 10 ^ k then (255 : Byte) else 0) &&& (if (k = 1 ∨ w.toNat / 10 ^ (k - 1) % 10 ≠ 0) then 255 else 0)) = _
  rw [and_masks]
  apply ite_iff
  rw [numDigits_eq w.toNat k h1]
  by_cases h : k = 1
  · simp [h]
  · have hP : 10 ^ k = 10 * 10 ^ (k - 1) := by
      rw [Nat.mul_comm, ← Nat.pow_succ]
      congr 1
      omega
    have pos : 0 < 10 ^ (k - 1) := Nat.pow_pos (by decide)
    constructor
    · rintro ⟨lt, h' | hd⟩
      · exact absurd h' h
      · refine ⟨lt, Or.inr ?_⟩
        have : w.toNat / 10 ^ (k - 1) < 10 := (Nat.div_lt_iff_lt_mul pos).mpr (by rw [← hP]; exact lt)
        rw [Nat.mod_eq_of_lt this] at hd
        have : 1 ≤ w.toNat / 10 ^ (k - 1) := Nat.pos_of_ne_zero hd
        have := (Nat.le_div_iff_mul_le pos).mp this
        simpa using this
    · rintro ⟨lt, h' | le⟩
      · exact absurd h' h
      · refine ⟨lt, Or.inr ?_⟩
        have : w.toNat / 10 ^ (k - 1) < 10 := (Nat.div_lt_iff_lt_mul pos).mpr (by rw [← hP]; exact lt)
        rw [Nat.mod_eq_of_lt this]
        have : 1 ≤ w.toNat / 10 ^ (k - 1) := (Nat.le_div_iff_mul_le pos).mpr (by simpa using le)
        exact Nat.pos_iff_ne_zero.mp this

theorem masks_value (w : BitVec 64) :
    (List.range 20).map (fun i => RelayEncoding.decimalMask RelayEncoding.decimalConcrete ByteAuth.concrete w (i + 1)) =
      ind (numDigits w.toNat) := by
  simp only [ind]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [decimalMask_value w (i + 1) (by omega) (by omega)]
  apply ite_iff
  constructor <;> intro h <;> omega

theorem get_ind (L n : Nat) (hn : n < 20) :
    OpenResult.get ByteAuth.concrete (ind L) n = if n + 1 = L then 255 else 0 := by
  simp [OpenResult.get, ind, List.getElem?_map, List.getElem?_range hn]

/-- The digit selected for position `index`: digit `L − 1 − index` when `index < L`, else 0. -/
theorem digitAt_value (w : BitVec 64) (L : Nat) (hL1 : 1 ≤ L) (index : Nat) :
    PrivateDecimal.digitAt RelayEncoding.decimalConcrete ByteAuth.concrete w (ind L) index =
      if index < L ∧ L ≤ 20 then RelayEncoding.decimalConcrete.digit w (L - 1 - index) else 0 := by
  have gen : ∀ n, n ≤ 20 →
      (List.range n).foldl (fun acc i => ByteAuth.concrete.xor acc
        (if index < i + 1 then ByteAuth.concrete.and (OpenResult.get ByteAuth.concrete (ind L) i)
          (RelayEncoding.decimalConcrete.digit w (i - index)) else ByteAuth.concrete.const 0)) (ByteAuth.concrete.const 0) =
        if index < L ∧ L ≤ n then RelayEncoding.decimalConcrete.digit w (L - 1 - index) else 0 := by
    intro n
    induction n with
    | zero => intro _; rw [if_neg (by omega)]; rfl
    | succ n ih =>
        intro hn
        rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
          get_ind L n (by omega)]
        by_cases e : n + 1 = L
        · subst e
          by_cases hi : index < n + 1
          · rw [if_pos hi, if_pos rfl, if_neg (by omega), if_pos ⟨hi, Nat.le_refl _⟩,
              show n + 1 - 1 - index = n - index by omega]
            show (0 : Byte) ^^^ ((255 : Byte) &&& _) = _
            simp
          · rw [if_neg hi, if_neg (by omega), if_neg (by omega)]
            rfl
        · have z : (if index < n + 1 then ByteAuth.concrete.and (if n + 1 = L then (255 : Byte) else 0)
              (RelayEncoding.decimalConcrete.digit w (n - index)) else ByteAuth.concrete.const 0) = 0 := by
            rw [if_neg e]
            split
            · show (0 : Byte) &&& _ = 0; simp
            · rfl
          rw [z]
          show (if index < L ∧ L ≤ n then RelayEncoding.decimalConcrete.digit w (L - 1 - index) else 0) ^^^ (0 : Byte) = _
          have xz : ∀ x : Byte, x ^^^ (0 : Byte) = x := fun x => by simp
          rw [xz]
          apply ite_iff
          constructor <;> intro h <;> omega
  exact gen 20 (Nat.le_refl _)

local notation "pl" => PrivateBuffer.publicLength ByteAuth.concrete

theorem and255 (x : Byte) : ByteAuth.concrete.and 255 x = x := by
  have all : ∀ x : Byte, ByteAuth.concrete.and 255 x = x := by decide
  exact all x

theorem and0 (x : Byte) : ByteAuth.concrete.and 0 x = 0 := by
  have all : ∀ x : Byte, ByteAuth.concrete.and 0 x = 0 := by decide
  exact all x

theorem sel0 (y x : Byte) : TlsInner.select ByteAuth.concrete 0 y x = x := by
  show ByteAuth.concrete.xor (ByteAuth.concrete.and 0 (ByteAuth.concrete.xor y x)) x = x
  rw [and0]
  show (0 : Byte) ^^^ x = x
  simp

theorem publicLength_length (n : Nat) : (pl n).length = 16 := by
  simp [PrivateBuffer.publicLength, PrivateBuffer.decodeLength]

/-- The digit at position `i` of the 20-byte buffer: digit `L − 1 − i` of the number, or 0. -/
def bufferData (w : BitVec 64) (L : Nat) : List Byte :=
  (List.range 20).map (fun i => if i < L then RelayEncoding.decimalConcrete.digit w (L - 1 - i) else 0)

/-- **`PrivateDecimal.encode` on a 64-bit number**: valid, length = the number of digits `L`, and
the digits, most significant first, then zeros. -/
theorem encode_value (w : BitVec 64) :
    PrivateDecimal.encode RelayEncoding.decimalConcrete ByteAuth.concrete w =
      ⟨255, pl (numDigits w.toNat), bufferData w (numDigits w.toNat)⟩ := by
  have hL1 : 1 ≤ numDigits w.toNat := (numDigits_spec _).1
  have hL20 : numDigits w.toNat ≤ 20 := numDigits_le _ w.isLt
  generalize hL : numDigits w.toNat = L at hL1 hL20
  have facts := fromMasks ⟨L, by omega⟩ (by simp only; omega)
  simp only at facts
  obtain ⟨u, b, c, l⟩ := facts
  have hdata : (List.range 20).map (fun i => ByteAuth.concrete.and (PrivateBuffer.less ByteAuth.concrete (pl i) (pl L))
      (OpenResult.get ByteAuth.concrete
        ((List.range 20).map (PrivateDecimal.digitAt RelayEncoding.decimalConcrete ByteAuth.concrete w (ind L))) i)) =
      bufferData w L := by
    simp only [bufferData]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have lt := lessTable ⟨i, hi⟩ ⟨L, by omega⟩
    simp only at lt
    rw [lt]
    simp only [OpenResult.get, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]
    rw [digitAt_value w L hL1 i]
    by_cases h : i < L
    · rw [if_pos (show i < L ∧ L ≤ 20 from ⟨h, hL20⟩), if_pos h, and255]
      simp [h]
    · rw [if_neg (show ¬(i < L ∧ L ≤ 20) from fun e => h e.1), if_neg h, and0]
      simp [h]
  simp only [PrivateDecimal.encode]
  rw [masks_value, hL, u, b]
  unfold PrivateBuffer.make
  rw [if_pos ⟨by decide, publicLength_length L, by simp⟩]
  simp only [c, l, hdata, PrivateProtobuf.gate, PrivateBuffer.finish]
  have v : ByteAuth.concrete.and 255 (ByteAuth.eqMask ByteAuth.concrete 255 (ByteAuth.concrete.const 255)) = 255 := by
    decide
  have v' : ByteAuth.concrete.and 255 (ByteAuth.concrete.not 0) = 255 := by decide
  simp only [v, v', ByteAuth.release_accept]

/-! ### The padded slot -/

theorem digit_ne_zero (w : BitVec 64) (j : Nat) (h : j ≤ 19) : RelayEncoding.decimalConcrete.digit w j ≠ 0 := by
  rw [digit_value w j h]
  intro e
  have := congrArg BitVec.toNat e
  have dl : w.toNat / 10 ^ j % 10 < 10 := Nat.mod_lt _ (by decide)
  simp only [BitVec.toNat_ofNat] at this
  rw [show (0 : Byte).toNat = 0 from rfl] at this
  omega

theorem refDecimal_length (n : Nat) : (refDecimal n).length = numDigits n := by
  simp [refDecimal]

theorem refDecimal_get (n i : Nat) (h : i < numDigits n) :
    (refDecimal n)[i]'(by rw [refDecimal_length]; exact h) =
      BitVec.ofNat 8 (48 + n / 10 ^ (numDigits n - 1 - i) % 10) := by
  simp [refDecimal, List.getElem_reverse]

theorem refDecimal_get' (n i L : Nat) (hL : numDigits n = L) (h : i < L) (h' : i < (refDecimal n).length) :
    (refDecimal n)[i]'h' = BitVec.ofNat 8 (48 + n / 10 ^ (L - 1 - i) % 10) := by
  subst hL
  exact refDecimal_get n i h

/-- **The padded decimal slot.** For a 64-bit number and a slot of `width < 20` bytes, the validity
byte is 255 exactly when the number's decimal digits fit in the slot, and the slot holds the
decimal digits (most significant first) followed by spaces up to `width` (cut to `width` if they
do not fit). -/
theorem paddedDecimal_value (w : BitVec 64) (width : Nat) (hw : width < 20) :
    paddedDecimalWith RelayEncoding.decimalConcrete ByteAuth.concrete 0 w width =
      (if numDigits w.toNat ≤ width then 255 else 0, refPadded w.toNat width) := by
  have hL1 : 1 ≤ numDigits w.toNat := (numDigits_spec _).1
  have hL20 : numDigits w.toNat ≤ 20 := numDigits_le _ w.isLt
  unfold paddedDecimalWith
  rw [encode_value]
  simp only
  generalize hL : numDigits w.toNat = L at hL1 hL20
  have zm := ByteAuth.zeroMask_value
  congr 1
  · have g : (bufferData w L).getD width 0 = if width < L then RelayEncoding.decimalConcrete.digit w (L - 1 - width) else 0 := by
      simp [bufferData, List.getD_eq_getElem?_getD, List.getElem?_range hw]
    rw [g]
    by_cases h : width < L
    · rw [if_pos h, zm, if_neg (digit_ne_zero w _ (by omega)), if_neg (by omega)]
      decide
    · rw [if_neg h, zm, if_pos rfl, if_pos (by omega)]
      decide
  · have len1 : ((bufferData w L).take width).length = width := by simp [bufferData]; omega
    apply List.ext_getElem
    · rw [List.length_map, len1, refPadded, List.length_take, List.length_append, refDecimal_length]; simp
    · intro i h1 h2
      rw [List.length_map, len1] at h1
      simp only [List.getElem_map, List.getElem_take, bufferData, List.getElem_range]
      simp only [refPadded, List.getElem_take]
      by_cases hi : i < L
      · rw [List.getElem_append_left (by rw [refDecimal_length, hL]; exact hi)]
        rw [refDecimal_get' w.toNat i L hL hi, if_pos hi, zm, if_neg (digit_ne_zero w _ (by omega)),
          digit_value w _ (by omega), sel0]
      · rw [List.getElem_append_right (by rw [refDecimal_length, hL]; omega)]
        rw [if_neg hi, zm, if_pos rfl]
        simp only [List.getElem_replicate]
        decide

/-! ### Reading the slot back -/

/-- Decimal digits (ASCII) to their value. -/
def parseDecimal (chars : List Byte) : Nat := chars.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

/-- The value of a padded slot: the digits before the first space. -/
def parsePadded (slot : List Byte) : Nat := parseDecimal (slot.takeWhile (· != 32))

theorem refDecimal_step (n : Nat) (h : 10 ≤ n) :
    refDecimal n = refDecimal (n / 10) ++ [BitVec.ofNat 8 (48 + n % 10)] := by
  have e : numDigits n = numDigits (n / 10) + 1 := by
    rw [numDigits]; simp [show ¬ n < 10 by omega]
  simp only [refDecimal, e, List.range_succ_eq_map, List.reverse_cons, List.map_append, List.map_reverse,
    List.map_map, List.map_cons, List.map_nil, Nat.pow_zero, Nat.div_one]
  congr 2
  apply List.map_congr_left
  intro j _
  show BitVec.ofNat 8 (48 + n / 10 ^ (j + 1) % 10) = _
  rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

theorem parseDecimal_snoc (xs : List Byte) (c : Byte) : parseDecimal (xs ++ [c]) = parseDecimal xs * 10 + (c.toNat - 48) := by
  simp [parseDecimal, List.foldl_append]

/-- **Round trip:** the decimal digits read back to the number. -/
theorem parseDecimal_refDecimal (n : Nat) : parseDecimal (refDecimal n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases h : n < 10
      · have : numDigits n = 1 := by rw [numDigits]; simp [h]
        simp only [refDecimal, this]
        simp [parseDecimal, BitVec.toNat_ofNat]
        omega
      · rw [refDecimal_step n (by omega), parseDecimal_snoc, ih (n / 10) (by omega)]
        simp only [BitVec.toNat_ofNat]
        have : n % 10 < 10 := Nat.mod_lt _ (by decide)
        omega

theorem refDecimal_no_space (n : Nat) : ∀ c ∈ refDecimal n, (c != 32) = true := by
  intro c hc
  simp only [refDecimal, List.mem_map, List.mem_reverse, List.mem_range] at hc
  obtain ⟨j, _, rfl⟩ := hc
  have : n / 10 ^ j % 10 < 10 := Nat.mod_lt _ (by decide)
  simp only [bne_iff_ne, ne_eq]
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this
  rw [show (32 : Byte).toNat = 32 from rfl] at this
  omega

/-- **Round trip for the slot:** when the digits fit, the padded slot reads back to the number. -/
theorem parsePadded_refPadded (n width : Nat) (h : numDigits n ≤ width) : parsePadded (refPadded n width) = n := by
  have len : (refDecimal n).length ≤ width := by rw [refDecimal_length]; exact h
  simp only [parsePadded, refPadded, List.take_append, List.take_of_length_le len]
  rw [List.takeWhile_append_of_pos (refDecimal_no_space n)]
  have sp : List.takeWhile (fun x => x != 32) (List.take (width - (refDecimal n).length) (List.replicate width (32 : Byte))) = [] := by
    rw [List.take_replicate]
    cases hm : min (width - (refDecimal n).length) width with
    | zero => rfl
    | succ k => simp [List.replicate_succ]
  rw [sp, List.append_nil, parseDecimal_refDecimal]

/-- The circuit's padded slot reads back to the number when it is valid. -/
theorem paddedDecimal_parse (w : BitVec 64) (width : Nat) (hw : width < 20)
    (valid : (paddedDecimalWith RelayEncoding.decimalConcrete ByteAuth.concrete 0 w width).1 = 255) :
    parsePadded (paddedDecimalWith RelayEncoding.decimalConcrete ByteAuth.concrete 0 w width).2 = w.toNat := by
  rw [paddedDecimal_value w width hw] at valid ⊢
  simp only at valid ⊢
  have fits : numDigits w.toNat ≤ width := by
    by_cases h : numDigits w.toNat ≤ width
    · exact h
    · rw [if_neg h] at valid; exact absurd valid (by decide)
  exact parsePadded_refPadded _ _ fits

#print axioms paddedDecimal_value
#print axioms parseDecimal_refDecimal
#print axioms parsePadded_refPadded
#print axioms paddedDecimal_parse

end TlsMpc.KernelSpecs.SlotDecimal
