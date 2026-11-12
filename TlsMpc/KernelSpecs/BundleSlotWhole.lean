import TlsMpc.KernelSpecs.BundleItemWhole

/-!
# `bundle-slot` against `BundleResponse.device` on the body the server sent

No emitter imports this file. Closes the gap left by `BundleItemWhole.bundleSlot_whole` (which
links `bundle-slot` only to the body with the item already spliced) and replaces
`check_bundle_slots.py` as the source of truth for the decimal slots. Updated for the emitter
batch (EMITTER_BATCH.md): the splice now pads with the `filler` byte 0 instead of `0` (48), and
`slotValid` requires the padding to be the filler and the rest digits.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`; `decide` only on closed
byte-sized facts):

* Numbers. `numberBits_value`: on any bytes, `numberBits` is `4 · length` mask bits whose value is
  Horner's rule over the low four bits of each character (it never overflows);
  `numberBits_decimal`: on digits that is the decimal value. `numberBits_zeros`,
  `numberBytes_zeros`, `tail_zeros`: leading filler bytes (0) only add zero bits at the top, so
  neither the decoded bytes nor the range check change.
* (a) for one slot. `slotValid_pad`: a slot of `m` bytes made of `m − n` filler bytes and `n` characters,
  checked with the declared width `n` (`1 ≤ n ≤ m < 256`), is accepted EXACTLY when `numberValid`
  accepts the `n` characters (same validity byte, not only the same verdict).
* (b) the splice. `spliced_eq`: the runtime's `BundleSlots.spliced` (fold over `splice w`, whose
  runs are merged) is the run-by-run splice `applyRuns`. `spliced_layout`: for an item of digit
  counts `w` (`w.ok`), the splice has the slot item's size, its template text is in place exactly
  when the original's is, and each slot field is the original field preceded by `0`s
  (`splice_pieces` is the general form, for any two templates that `Fits`).
* (a) for the item. `deviceSlots_splice`: `BundleSlots.deviceSlots` with the counts as `widths`
  (`widthBytes w`) on the response with the item spliced is `BundleResponse.device` with `w` on the
  response as it was — all outputs, validity included.
* End to end. `bundleSlot_device`: for the body `X` the server sent and an item placed at `start`
  as `layout?` places it, `bundle-slot`'s outputs are `device` on `X` at `start` with `w`;
  `bundleSlot_eq_bundleItem`: so they are `bundle-item`'s outputs.
* Wrong digit counts. `device_unique`: `device` accepts an item with at most one set of digit
  counts. `device_valid_mask`, `deviceSlots_valid_mask`: the validity byte is always 0 or 255.
  `bundleSlot_wrong_counts`: if the item is accepted with its true counts `w` and the runtime
  splices it with, and declares, other counts `w'`, every output is 0 (validity included).
  `bundleSlot_parses_or_refuses`: whatever counts the runtime uses, the kernel either outputs
  `device` with the only counts that parse the item, or releases nothing.
* A `widths` input that disagrees with the splice. `slotValid_width`: a slot accepts only its
  true width byte (whatever the number, provided its first byte is not the filler).
  `deviceSlots_any_widths`, `bundleSlot_any_widths`: for ANY item spliced with its counts (no
  longer only one `device` accepts) and ANY five `widths` bytes, the kernel gives `device`'s
  outputs with the true counts or nothing.

The former COUNTEREXAMPLE (`inconsistent_width_accepts`: device id `05` spliced with count 2 into
`005` and declared with width 1 was accepted as 5, while `device` refuses `05`) is now
`inconsistent_width_refused` (refused for every width byte). `zero_padding_ambiguous` shows why the
padding byte had to change: with `0` padding, `05` spliced with two digits and `5` spliced with one
were the same slot, so no change to the kernel alone could tell them apart.

NOT PROVED here: what `numberBytes` and `decode` mean as integers/bytes (`number_spec` and the
base64 meaning in `TlsMpc/BundleProofs.lean`; they concern `device` itself, hence `bundle-item`
too; `numberBits_decimal` covers the bits); that the C++ worker binds the inputs as stated (the
cut around the item, the splice from `splice w` with the filler 0 — `service_kernels.h`
`bundle_establish` —, `widths` = the counts); the kernel on an `item` input that is not a splice
of the body (e.g. a non-filler padding byte), which only the test covers.
-/

namespace TlsMpc.KernelSpecs.BundleSlotWhole
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open Establish (part)
open BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid numberBytes
  digitValid pushDigit)
open PrivateBuffer.Semantics (mask value)

abbrev Byte := BitVec 8

local notation "C" => ByteAuth.concrete

/-! ### Concrete byte operations -/

theorem c_and (x y : Byte) : ByteAuth.concrete.and x y = x &&& y := rfl
theorem c_not (x : Byte) : ByteAuth.concrete.not x = ~~~x := rfl
theorem c_const (n : Nat) : ByteAuth.concrete.const n = BitVec.ofNat 8 n := rfl

theorem and255 : ∀ x : Byte, x &&& 255 = x := by decide
theorem and255' : ∀ x : Byte, 255 &&& x = x := by decide
theorem and0 : ∀ x : Byte, x &&& 0 = 0 := by decide
theorem and0' : ∀ x : Byte, 0 &&& x = 0 := by decide

theorem ite_iff {α : Type} {c d : Prop} [Decidable c] [Decidable d] (h : c ↔ d) (x y : α) :
    (if c then x else y) = (if d then x else y) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos (h.mp hc)]
  · rw [if_neg hc, if_neg (fun hd => hc (h.mpr hd))]

theorem ofNat_inj (n k : Nat) (hn : n < 256) (hk : k < 256) : BitVec.ofNat 8 n = BitVec.ofNat 8 k ↔ n = k := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  · intro h; rw [h]

theorem foldl_and (init : Byte) (xs : List Byte) :
    xs.foldl ByteAuth.concrete.and init = init &&& xs.foldl ByteAuth.concrete.and 255 := by
  induction xs generalizing init with
  | nil => exact (and255 init).symm
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (ByteAuth.concrete.and init x), ih (ByteAuth.concrete.and 255 x), c_and, c_and, and255', BitVec.and_assoc]

theorem all_append (xs ys : List Byte) :
    ReceiveFirst.all C (xs ++ ys) = ReceiveFirst.all C xs &&& ReceiveFirst.all C ys := by
  simp only [ReceiveFirst.all, List.foldl_append]
  rw [foldl_and]
  rfl

theorem all_nil : ReceiveFirst.all C [] = 255 := rfl

theorem all_single (x : Byte) : ReceiveFirst.all C [x] = x := by
  show ByteAuth.concrete.and (ByteAuth.concrete.const 255) x = x
  rw [c_and, c_const]; exact and255' x

theorem all_255 (xs : List Byte) (h : ∀ x ∈ xs, x = 255) : ReceiveFirst.all C xs = 255 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [show x :: xs = [x] ++ xs from rfl, all_append, all_single, h x (by simp),
        ih (fun y hy => h y (by simp [hy]))]
      rfl

/-- The conjunction of a list that is 255 except at index `p`, where it is `X`. -/
theorem all_ite (p : Nat) (X : Byte) (xs : List Nat) :
    ReceiveFirst.all C (xs.map (fun j => if j = p then X else 255)) = if p ∈ xs then X else 255 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, show ∀ (y : Byte) ys, y :: ys = [y] ++ ys from fun _ _ => rfl, all_append, all_single, ih]
      by_cases hx : x = p
      · subst hx
        rw [if_pos rfl, if_pos (List.mem_cons_self)]
        by_cases hm : x ∈ xs
        · rw [if_pos hm, BitVec.and_self]
        · rw [if_neg hm]; exact and255 X
      · rw [if_neg hx, and255']
        apply ite_iff
        simp only [List.mem_cons]
        constructor
        · intro h; exact Or.inr h
        · rintro (h | h)
          · exact absurd h.symm hx
          · exact h

theorem either_masks (A B : Prop) [Decidable A] [Decidable B] :
    ReceiveFirst.either C (if A then 255 else 0) (if B then 255 else 0) = if A ∨ B then 255 else 0 := by
  by_cases a : A <;> by_cases b : B <;> simp [a, b] <;> decide

theorem any_ite_foldl (P : Nat → Prop) [DecidablePred P] (xs : List Nat) :
    ∀ (Q : Prop) [Decidable Q], (xs.map (fun k => if P k then (255 : Byte) else 0)).foldl (ReceiveFirst.either C)
      (if Q then 255 else 0) = if Q ∨ ∃ k ∈ xs, P k then 255 else 0 := by
  induction xs with
  | nil => intro Q _; simp
  | cons x xs ih =>
      intro Q _
      rw [List.map_cons, List.foldl_cons, either_masks, ih]
      apply ite_iff
      simp only [List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem any_ite (P : Nat → Prop) [DecidablePred P] (xs : List Nat) :
    ReceiveFirst.any C (xs.map (fun k => if P k then (255 : Byte) else 0)) = if ∃ k ∈ xs, P k then 255 else 0 := by
  have h := any_ite_foldl P xs False
  rw [if_neg (fun h => h)] at h
  simp only [ReceiveFirst.any, c_const]
  rw [show (BitVec.ofNat 8 0 : Byte) = 0 from rfl, h]
  apply ite_iff
  simp

/-! ### `numberBits`: the value of the digits, so leading `0`s change nothing -/

theorem value_append (xs ys : List Bool) : value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
      simp only [List.cons_append, value, ih, List.length_cons]
      have : 2 ^ (xs.length + 1) * value ys = 2 * (2 ^ xs.length * value ys) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ xs.length) 2, Nat.mul_assoc]
      omega

theorem value_lt (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
      simp only [value, List.length_cons, Nat.pow_succ]
      have : b.toNat ≤ 1 := by cases b <;> decide
      omega

theorem value_replicate (k : Nat) : value (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, value, ih]

theorem value_inj : ∀ (xs ys : List Bool), xs.length = ys.length → value xs = value ys → xs = ys
  | [], [], _, _ => rfl
  | b :: xs, c :: ys, hl, hv => by
      simp only [value] at hv
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hb : b.toNat ≤ 1 := by cases b <;> decide
      have hc : c.toNat ≤ 1 := by cases c <;> decide
      have e1 : b.toNat = c.toNat := by omega
      have e2 : value xs = value ys := by omega
      have : b = c := by cases b <;> cases c <;> simp_all
      rw [this, value_inj xs ys hl e2]

/-- Reading `W` positions of a bit list, `false` past its end (what `addLoop` reads). -/
theorem read_eq (M : List Bool) (W : Nat) :
    (List.range W).map (fun i => M[i]?.getD false) = M.take W ++ List.replicate (W - M.length) false := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    by_cases hi : i < M.length
    · rw [List.getElem_append_left (by simp; omega), List.getElem_take, List.getElem?_eq_getElem hi]
      rfl
    · rw [List.getElem_append_right (by simp; omega), List.getElem_replicate, List.getElem?_eq_none (by omega)]
      rfl

theorem value_read (M : List Bool) (W : Nat) :
    value ((List.range W).map (fun i => M[i]?.getD false)) = value M % 2 ^ W := by
  rw [read_eq, value_append, value_replicate, Nat.mul_zero, Nat.add_zero]
  have split := value_append (M.take W) (M.drop W)
  rw [List.take_append_drop] at split
  by_cases hW : W ≤ M.length
  · have hl : (M.take W).length = W := by simp; omega
    rw [hl] at split
    rw [split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by have := value_lt (M.take W); rw [hl] at this; exact this)]
  · rw [List.take_of_length_le (by omega)]
    have := value_lt M
    have : 2 ^ M.length ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.mod_eq_of_lt (by omega)]

theorem add_length : ∀ (pairs : List (Bool × Bool)) (carry : Bool),
    (PrivateBuffer.Semantics.add pairs carry).1.length = pairs.length
  | [], _ => rfl
  | (x, y) :: rest, carry => by
      simp only [PrivateBuffer.Semantics.add, List.length_cons]
      rw [add_length rest]

theorem const0 : ByteAuth.concrete.const 0 = mask false := rfl

/-- `BundleResponse.add` on mask bits is addition modulo `2^W`. -/
theorem add_value (W : Nat) (X Y : List Bool) :
    ∃ R : List Bool, BundleResponse.add C W (X.map mask) (Y.map mask) = R.map mask ∧ R.length = W ∧
      value R = (value X + value Y) % 2 ^ W := by
  have hm := PrivateBuffer.Semantics.addLoop_masks X Y (List.range W) false
  have hv := PrivateBuffer.Semantics.add_value
    ((List.range W).map (fun i => (X[i]?.getD false, Y[i]?.getD false))) false
  refine ⟨(PrivateBuffer.Semantics.add ((List.range W).map (fun i => (X[i]?.getD false, Y[i]?.getD false))) false).1,
    ?_, ?_, ?_⟩
  · simp only [BundleResponse.add]
    rw [const0, hm]
  · rw [add_length]; simp
  · simp only [List.map_map, Function.comp_def, List.length_map, List.length_range, Bool.toNat_false,
      Nat.add_zero] at hv
    rw [value_read, value_read] at hv
    have lt := value_lt (PrivateBuffer.Semantics.add
      ((List.range W).map (fun i => (X[i]?.getD false, Y[i]?.getD false))) false).1
    rw [add_length] at lt
    simp only [List.length_map, List.length_range] at lt
    rw [Nat.add_mod, ← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lt]

theorem maskBit_low : ∀ c : Byte, (List.range 4).map (ByteAuth.concrete.maskBit c) = ((List.range 4).map c.getLsbD).map mask := by
  decide

theorem value_low : ∀ c : Byte, value ((List.range 4).map c.getLsbD) = c.toNat % 16 := by
  decide

theorem pushDigit_value (W : Nat) (L : List Bool) (c : Byte) :
    ∃ R : List Bool, pushDigit C W (L.map mask) c = R.map mask ∧ R.length = W ∧
      value R = (10 * value L + c.toNat % 16) % 2 ^ W := by
  obtain ⟨R1, e1, _, v1⟩ := add_value W (false :: L) (false :: false :: false :: L)
  obtain ⟨R2, e2, l2, v2⟩ := add_value W R1 ((List.range 4).map c.getLsbD)
  refine ⟨R2, ?_, l2, ?_⟩
  · simp only [pushDigit]
    rw [const0, show mask false :: mask false :: mask false :: L.map mask = (false :: false :: false :: L).map mask from rfl,
      show mask false :: L.map mask = (false :: L).map mask from rfl,
      e1, maskBit_low, e2]
  · rw [v2, v1, value_low]
    simp only [value, Bool.toNat_false]
    rw [Nat.mod_add_mod]
    congr 1
    omega

/-- Horner's rule over the low four bits of each character (for digits: the decimal value). -/
def horner (acc : Nat) (cs : List Byte) : Nat := cs.foldl (fun acc c => 10 * acc + c.toNat % 16) acc

theorem horner_mod (M : Nat) : ∀ (cs : List Byte) (a : Nat), horner (a % M) cs % M = horner a cs % M
  | [], a => by simp [horner]
  | c :: cs, a => by
      simp only [horner, List.foldl_cons]
      have h1 := horner_mod M cs (10 * (a % M) + c.toNat % 16)
      have h2 := horner_mod M cs (10 * a + c.toNat % 16)
      simp only [horner] at h1 h2
      rw [← h1, ← h2]
      congr 2
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

theorem horner_lt (k : Nat) : ∀ (cs : List Byte) (a : Nat), a < 16 ^ k → horner a cs < 16 ^ (k + cs.length)
  | [], a, h => by simpa [horner] using h
  | c :: cs, a, h => by
      simp only [horner, List.foldl_cons, List.length_cons]
      have step : 10 * a + c.toNat % 16 < 16 ^ (k + 1) := by
        have : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
        rw [Nat.pow_succ]; omega
      have := horner_lt (k + 1) cs _ step
      simp only [horner] at this
      rw [show k + (cs.length + 1) = k + 1 + cs.length by omega]
      exact this

theorem foldl_push (W : Nat) : ∀ (cs : List Byte) (L : List Bool), L.length = W →
    ∃ R : List Bool, cs.foldl (pushDigit C W) (L.map mask) = R.map mask ∧ R.length = W ∧
      value R = horner (value L) cs % 2 ^ W
  | [], L, h => ⟨L, rfl, h, by rw [Nat.mod_eq_of_lt (by have := value_lt L; rw [h] at this; exact this)]; rfl⟩
  | c :: cs, L, h => by
      obtain ⟨R1, e1, l1, v1⟩ := pushDigit_value W L c
      obtain ⟨R, e, l, v⟩ := foldl_push W cs R1 l1
      refine ⟨R, ?_, l, ?_⟩
      · rw [List.foldl_cons, e1, e]
      · rw [v, v1, horner_mod]
        rfl

/-- **`numberBits` on concrete bytes**: `4 · length` bits whose value is `horner 0` of the
characters (no overflow: `horner 0 cs < 16^length`). -/
theorem numberBits_value (cs : List Byte) :
    ∃ R : List Bool, numberBits C cs = R.map mask ∧ R.length = 4 * cs.length ∧ value R = horner 0 cs := by
  obtain ⟨R, e, l, v⟩ := foldl_push (4 * cs.length) cs (List.replicate (4 * cs.length) false) (by simp)
  refine ⟨R, ?_, l, ?_⟩
  · simp only [numberBits]
    rw [const0, ← List.map_replicate, e]
  · rw [v, value_replicate]
    have := horner_lt 0 cs 0 (by decide)
    rw [Nat.zero_add, show (16 : Nat) ^ cs.length = 2 ^ (4 * cs.length) by rw [Nat.pow_mul]] at this
    exact Nat.mod_eq_of_lt this

theorem horner_zeros (k : Nat) (a : Nat) (h : a = 0) : horner a (List.replicate k (0 : Byte)) = 0 := by
  subst h
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ]
      simp only [horner, List.foldl_cons] at ih ⊢
      exact ih

/-- **Leading `0`s add zero bits at the top and change nothing else.** -/
theorem numberBits_zeros (k : Nat) (cs : List Byte) :
    numberBits C (List.replicate k 0 ++ cs) = numberBits C cs ++ List.replicate (4 * k) 0 := by
  obtain ⟨R', e', l', v'⟩ := numberBits_value (List.replicate k 0 ++ cs)
  obtain ⟨R, e, l, v⟩ := numberBits_value cs
  have hv : value R' = value (R ++ List.replicate (4 * k) false) := by
    rw [v', value_append, value_replicate, Nat.mul_zero, Nat.add_zero, v]
    simp only [horner, List.foldl_append]
    have := horner_zeros k 0 rfl
    simp only [horner] at this
    rw [this]
  have hl : R'.length = (R ++ List.replicate (4 * k) false).length := by
    simp only [l', l, List.length_append, List.length_replicate]; omega
  rw [e', e, value_inj _ _ hl hv, List.map_append, List.map_replicate]
  rfl

/-- The value of decimal digits (ASCII `0`–`9`), most significant first. -/
def decimal (cs : List Byte) : Nat := cs.foldl (fun acc c => 10 * acc + (c.toNat - 48)) 0

theorem horner_digits : ∀ (cs : List Byte) (a : Nat), (∀ c ∈ cs, 48 ≤ c.toNat ∧ c.toNat ≤ 57) →
    horner a cs = cs.foldl (fun acc c => 10 * acc + (c.toNat - 48)) a
  | [], _, _ => rfl
  | c :: cs, a, h => by
      simp only [horner, List.foldl_cons] at *
      have hc := h c (by simp)
      rw [show c.toNat % 16 = c.toNat - 48 by omega]
      exact horner_digits cs _ (fun d hd => h d (by simp [hd]))

/-- **On digits, `numberBits` is the binary expansion of the decimal value** (`4 · length` bits,
least significant first; no overflow). -/
theorem numberBits_decimal (cs : List Byte) (h : ∀ c ∈ cs, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    ∃ R : List Bool, numberBits C cs = R.map mask ∧ R.length = 4 * cs.length ∧ value R = decimal cs := by
  obtain ⟨R, e, l, v⟩ := numberBits_value cs
  exact ⟨R, e, l, by rw [v, horner_digits cs 0 h]; rfl⟩

theorem get_zeros (xs : List Byte) (e i : Nat) :
    OpenResult.get C (xs ++ List.replicate e 0) i = OpenResult.get C xs i := by
  simp only [OpenResult.get]
  by_cases h : i < xs.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
    rw [List.getElem?_eq_none (show xs.length ≤ i by omega)]
    split <;> rfl

theorem fromBits_zeros (xs : List Byte) (e first : Nat) :
    BundleResponse.fromBits C (xs ++ List.replicate e 0) first = BundleResponse.fromBits C xs first := by
  simp only [BundleResponse.fromBits, get_zeros]

/-- The big-endian bytes of a number do not change with leading `0`s. -/
theorem numberBytes_zeros (count k : Nat) (cs : List Byte) :
    numberBytes C count (List.replicate k 0 ++ cs) = numberBytes C count cs := by
  simp only [numberBytes, numberBits_zeros, fromBits_zeros]

/-- Nor does the range check (the bits at and above `limit` are zero). -/
theorem tail_zeros (limit k : Nat) (cs : List Byte) :
    ReceiveFirst.all C (((numberBits C (List.replicate k 0 ++ cs)).drop limit).map ByteAuth.concrete.not) =
      ReceiveFirst.all C (((numberBits C cs).drop limit).map ByteAuth.concrete.not) := by
  have hz : ∀ d, ReceiveFirst.all C ((List.drop d (List.replicate (4 * k) (0 : Byte))).map ByteAuth.concrete.not) =
      255 := by
    intro d
    apply all_255
    intro x hx
    simp only [List.mem_map, List.drop_replicate, List.mem_replicate] at hx
    obtain ⟨y, ⟨_, rfl⟩, rfl⟩ := hx
    decide
  rw [numberBits_zeros, List.drop_append, List.map_append, all_append, hz, and255]

/-! ### A slot against the number it holds -/

theorem either255 : ∀ x : Byte, ReceiveFirst.either C x 255 = 255 := by decide
theorem either255' : ∀ x : Byte, ReceiveFirst.either C 255 x = 255 := by decide
theorem either0 : ∀ z : Byte, ReceiveFirst.either C 0 z = z := by decide

theorem get_slot_pad (cs : List Byte) (g j : Nat) (h : j < g) :
    OpenResult.get C (List.replicate g 0 ++ cs) j = 0 := by
  simp only [OpenResult.get]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate, if_pos h]
  rfl

theorem get_slot_digit (cs : List Byte) (g i : Nat) :
    OpenResult.get C (List.replicate g 0 ++ cs) (g + i) = OpenResult.get C cs i := by
  simp only [OpenResult.get]
  rw [List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left]

theorem is_value (n k : Nat) :
    ByteAuth.eqMask C (BitVec.ofNat 8 n) (ByteAuth.concrete.const k) =
      if BitVec.ofNat 8 n = BitVec.ofNat 8 k then 255 else 0 :=
  ByteAuth.eqMask_value _ _

/-- The width check: the declared width is one of `1 … m`. -/
theorem width_ok (n m : Nat) (h1 : 1 ≤ n) (hnm : n ≤ m) :
    ReceiveFirst.any C ((List.range m).map (fun k => ByteAuth.eqMask C (BitVec.ofNat 8 n) (ByteAuth.concrete.const (k + 1)))) =
      255 := by
  rw [show (fun k => ByteAuth.eqMask C (BitVec.ofNat 8 n) (ByteAuth.concrete.const (k + 1))) =
      (fun k => if BitVec.ofNat 8 n = BitVec.ofNat 8 (k + 1) then (255 : Byte) else 0) from
      funext (fun k => is_value n (k + 1)), any_ite, if_pos ⟨n - 1, by simp; omega, by congr 1; omega⟩]

/-- The padding mask at position `j` of a slot of `m` bytes, for a declared width `u`: 255 exactly
when `u < m − j`. -/
theorem pad_value (v : Byte) (u m j : Nat) (hv : v = BitVec.ofNat 8 u) (hu : u < 256) (hm : m < 256) :
    ReceiveFirst.any C ((List.range (m - j)).map (fun k => ByteAuth.eqMask C v (ByteAuth.concrete.const k))) =
      if u < m - j then 255 else 0 := by
  subst hv
  rw [show (fun k => ByteAuth.eqMask C (BitVec.ofNat 8 u) (ByteAuth.concrete.const k)) =
      (fun k => if BitVec.ofNat 8 u = BitVec.ofNat 8 k then (255 : Byte) else 0) from
      funext (fun k => is_value u k), any_ite]
  by_cases h : u < m - j
  · rw [if_pos ⟨u, List.mem_range.mpr h, rfl⟩, if_pos h]
  · rw [if_neg, if_neg h]
    rintro ⟨k, hk, e⟩
    simp only [List.mem_range] at hk
    have := (ofNat_inj u k hu (by omega)).mp e
    omega

theorem and255'' : ∀ x : Byte, ByteAuth.concrete.and 255 x = x := and255'
theorem and0'' : ∀ x : Byte, ByteAuth.concrete.and 0 x = 0 := and0'

/-- One position of the padding/digit check, with the padding mask 255: the byte is the filler. -/
theorem entry_pad (c : Byte) :
    ReceiveFirst.either C (ByteAuth.concrete.and 255 (ByteAuth.eqMask C c (ByteAuth.concrete.const BundleSlots.filler)))
      (ByteAuth.concrete.and (ByteAuth.concrete.not 255) (BundleResponse.digitValid C c)) =
      ByteAuth.eqMask C c (ByteAuth.concrete.const BundleSlots.filler) := by
  rw [and255'', show ByteAuth.concrete.not 255 = (0 : Byte) from rfl, and0'']
  rw [ByteAuth.eqMask_value]
  split <;> decide

/-- One position of the padding/digit check, with the padding mask 0: the byte is a digit. -/
theorem entry_digit (c : Byte) :
    ReceiveFirst.either C (ByteAuth.concrete.and 0 (ByteAuth.eqMask C c (ByteAuth.concrete.const BundleSlots.filler)))
      (ByteAuth.concrete.and (ByteAuth.concrete.not 0) (BundleResponse.digitValid C c)) =
      BundleResponse.digitValid C c := by
  rw [and0'', show ByteAuth.concrete.not 0 = (255 : Byte) from rfl, and255'', either0]

theorem range_get_map (cs : List Byte) (f : Byte → Byte) :
    (List.range cs.length).map (fun i => f (OpenResult.get C cs i)) = cs.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, OpenResult.get]
    rw [List.getElem?_eq_getElem (by simpa using h1)]
    rfl

/-- The padding and digit checks on a slot of `m` bytes made of `m − n` filler bytes and `n`
characters, with the declared width `n`: exactly the digit checks of the `n` characters. -/
theorem pads_digits (n m : Nat) (cs : List Byte) (hn : cs.length = n) (hnm : n ≤ m) (hm : m < 256) :
    ReceiveFirst.all C ((List.range m).map (fun j => ReceiveFirst.either C
      (ByteAuth.concrete.and (ReceiveFirst.any C ((List.range (m - j)).map
          (fun k => ByteAuth.eqMask C (BitVec.ofNat 8 n) (ByteAuth.concrete.const k))))
        (ByteAuth.eqMask C (OpenResult.get C (List.replicate (m - n) 0 ++ cs) j)
          (ByteAuth.concrete.const BundleSlots.filler)))
      (ByteAuth.concrete.and (ByteAuth.concrete.not (ReceiveFirst.any C ((List.range (m - j)).map
          (fun k => ByteAuth.eqMask C (BitVec.ofNat 8 n) (ByteAuth.concrete.const k)))))
        (BundleResponse.digitValid C (OpenResult.get C (List.replicate (m - n) 0 ++ cs) j))))) =
    ReceiveFirst.all C (cs.map (BundleResponse.digitValid C)) := by
  subst hn
  have hr : List.range m = List.range (m - cs.length) ++ (List.range cs.length).map ((m - cs.length) + ·) := by
    rw [← List.range_add]; congr 1; omega
  rw [hr, List.map_append, all_append, all_255 _ ?_, and255', List.map_map]
  · rw [← range_get_map cs (BundleResponse.digitValid C)]
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [pad_value _ cs.length _ _ rfl (by omega) (by omega), if_neg (by omega), get_slot_digit, entry_digit]
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [pad_value _ cs.length _ _ rfl (by omega) (by omega), if_pos (by omega), get_slot_pad cs _ j hj, entry_pad]
    decide

/-- The first-digit check: the only one that can fail is at the number's first digit, and only
when the number has more than one digit; there it is `numberValid`'s leading-zero check. -/
theorem firsts_eq (n m : Nat) (cs : List Byte) (h1 : 1 ≤ n) (hnm : n ≤ m) (hm : m < 256) :
    ReceiveFirst.all C ((List.range (m - 1)).map (fun j => ByteAuth.concrete.not (ByteAuth.concrete.and
      (ByteAuth.eqMask C (BitVec.ofNat 8 n) (ByteAuth.concrete.const (m - j)))
      (ByteAuth.eqMask C (OpenResult.get C (List.replicate (m - n) 0 ++ cs) j) (ByteAuth.concrete.const 48))))) =
    ReceiveFirst.all C (BundleResponse.optional (decide (1 < n))
      [ByteAuth.concrete.not (ByteAuth.eqMask C (OpenResult.get C cs 0) (ByteAuth.concrete.const 48))]) := by
  have pointwise : ∀ j ∈ List.range (m - 1), ByteAuth.concrete.not (ByteAuth.concrete.and
      (ByteAuth.eqMask C (BitVec.ofNat 8 n) (ByteAuth.concrete.const (m - j)))
      (ByteAuth.eqMask C (OpenResult.get C (List.replicate (m - n) 0 ++ cs) j) (ByteAuth.concrete.const 48))) =
      if j = m - n then ByteAuth.concrete.not (ByteAuth.eqMask C (OpenResult.get C cs 0) (ByteAuth.concrete.const 48))
      else 255 := by
    intro j hj
    simp only [List.mem_range] at hj
    rw [is_value]
    by_cases e : j = m - n
    · have g := get_slot_digit cs (m - n) 0
      rw [Nat.add_zero] at g
      rw [if_pos e, if_pos ((ofNat_inj n (m - j) (by omega) (by omega)).mpr (by omega)), e, g, c_and, and255']
    · rw [if_neg e, if_neg (fun h => e (by have := (ofNat_inj n (m - j) (by omega) (by omega)).mp h; omega)),
        c_and, and0']
      rfl
  rw [List.map_congr_left pointwise, all_ite]
  by_cases hn1 : 1 < n
  · rw [if_pos (by simp; omega), decide_eq_true hn1]
    exact (all_single _).symm
  · rw [if_neg (by simp; omega), decide_eq_false hn1]
    rfl

/-- **A slot of `m` bytes holding `m − n` filler bytes and then `n` characters, checked with the
declared width `n`, is accepted exactly when `numberValid` accepts the `n` characters.** -/
theorem slotValid_pad (limit : Nat) (cs : List Byte) (m : Nat) (h1 : 1 ≤ cs.length) (hnm : cs.length ≤ m)
    (hm : m < 256) :
    BundleSlots.slotValid C limit (BitVec.ofNat 8 cs.length) (List.replicate (m - cs.length) 0 ++ cs) =
      numberValid C limit cs := by
  have hlen : (List.replicate (m - cs.length) 0 ++ cs).length = m := by simp; omega
  simp only [BundleSlots.slotValid, numberValid, hlen, all_append, all_single]
  have key : ∀ (A PD F T D' F' T' : Byte), A = 255 → PD = D' → F = F' → T = T' →
      ((A &&& PD) &&& F) &&& T = (D' &&& F') &&& T' := by
    intro A PD F T D' F' T' hA hPD hF hT
    rw [hA, hPD, hF, hT, and255']
  exact key _ _ _ _ _ _ _ (width_ok cs.length m h1 hnm) (pads_digits cs.length m cs rfl hnm hm)
    (firsts_eq cs.length m cs h1 hnm hm) (tail_zeros limit _ cs)

/-! ### The splice, piece by piece -/

/-- What a list of `(zeros, copy)` runs does to bytes: `zeros` copies of `z`, then the next `copy`
bytes, run after run. -/
def applyRuns {α : Type} (z : α) : List (Nat × Nat) → List α → List α
  | [], _ => []
  | (k, c) :: rs, bytes => List.replicate k z ++ bytes.take c ++ applyRuns z rs (bytes.drop c)

theorem spliced_fold {α : Type} (z : α) (bytes : List α) : ∀ (rs : List (Nat × Nat)) (acc : List α) (p : Nat),
    rs.foldl (fun (acc : List α × Nat) (r : Nat × Nat) =>
        (acc.1 ++ List.replicate r.1 z ++ (bytes.drop acc.2).take r.2, acc.2 + r.2)) (acc, p) =
      (acc ++ applyRuns z rs (bytes.drop p), p + (rs.map Prod.snd).sum)
  | [], acc, p => by simp [applyRuns]
  | (k, c) :: rs, acc, p => by
      rw [List.foldl_cons, spliced_fold z bytes rs]
      simp only [applyRuns, List.drop_drop, List.append_assoc, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem applyRuns_merge {α : Type} (z : α) (rs : List (Nat × Nat)) :
    ∀ bytes, applyRuns z (BundleSlots.merge rs) bytes = applyRuns z rs bytes := by
  induction rs using BundleSlots.merge.induct with
  | case1 k c c' rest ih =>
      intro bytes
      rw [BundleSlots.merge.eq_1, ih]
      simp only [applyRuns, List.replicate_zero, List.nil_append, List.take_add, List.drop_drop, List.append_assoc]
  | case2 r rest h ih =>
      intro bytes
      rw [BundleSlots.merge.eq_2 r rest h]
      obtain ⟨k, c⟩ := r
      simp only [applyRuns, ih]
  | case3 => intro bytes; rw [BundleSlots.merge.eq_3]

/-- **The runtime's splice is the run-by-run one.** -/
theorem spliced_eq {α : Type} (w : Widths) (bytes : List α) (z : α) :
    BundleSlots.spliced w bytes z =
      applyRuns z (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) bytes := by
  simp only [BundleSlots.spliced, BundleSlots.splice]
  rw [spliced_fold, applyRuns_merge]
  simp

/-- Two templates with the same text and number fields at least as wide. -/
def Fits : List Piece → List Piece → Prop
  | [], [] => True
  | .text s :: P, .text t :: Q => s = t ∧ Fits P Q
  | .field n :: P, .field m :: Q => n ≤ m ∧ Fits P Q
  | _, _ => False

/-- The size of the `k`-th field (0 past the end). -/
def fieldSize : List Piece → Nat → Nat
  | [], _ => 0
  | .text _ :: P, k => fieldSize P k
  | .field n :: _, 0 => n
  | .field _ :: P, k + 1 => fieldSize P k

theorem take_app {α : Type} (A B : List α) (c : Nat) (h : A.length = c) : (A ++ B).take c = A := by
  subst h; simp

theorem drop_app {α : Type} (A B : List α) (c : Nat) (h : A.length = c) : (A ++ B).drop c = B := by
  subst h; simp

theorem part_left {α : Type} (L : List α) (s c q : Nat) : (part L s (c + q)).take c = part L s c := by
  simp [part, List.take_take]

theorem part_right {α : Type} (L : List α) (s c q : Nat) : (part L s (c + q)).drop c = part L (s + c) q := by
  simp [part, List.drop_take, List.drop_drop]

theorem size_text (t : String) (P : List Piece) : size (.text t :: P) = t.toUTF8.size + size P := by
  rw [BundleItemWhole.size_cons]; rfl

theorem size_field (n : Nat) (P : List Piece) : size (.field n :: P) = n + size P := by
  rw [BundleItemWhole.size_cons]; rfl

theorem applyRuns_length {α : Type} (z : α) : ∀ (P Q : List Piece), Fits P Q → ∀ (I : List α), I.length = size P →
    (applyRuns z (BundleSlots.runs P Q) I).length = size Q
  | [], [], _, _, _ => rfl
  | .text t :: P, .text t' :: Q, ⟨e, hf⟩, I, hI => by
      subst e
      rw [size_text] at hI
      have := applyRuns_length z P Q hf (I.drop t.toUTF8.size) (by rw [List.length_drop]; omega)
      show (List.replicate 0 z ++ I.take t.toUTF8.size ++ applyRuns z (BundleSlots.runs P Q) (I.drop t.toUTF8.size)).length = _
      simp only [List.length_append, List.length_replicate, List.length_take, this, size_text]
      omega
  | .field n :: P, .field m :: Q, ⟨hnm, hf⟩, I, hI => by
      rw [size_field] at hI
      have := applyRuns_length z P Q hf (I.drop n) (by simp; omega)
      show (List.replicate (m - n) z ++ I.take n ++ applyRuns z (BundleSlots.runs P Q) (I.drop n)).length = _
      simp only [List.length_append, List.length_replicate, List.length_take, this, size_field]
      omega
  | [], _ :: _, h, _, _ => by simp [Fits] at h
  | _ :: _, [], h, _, _ => by simp [Fits] at h
  | .text _ :: _, .field _ :: _, h, _, _ => by simp [Fits] at h
  | .field _ :: _, .text _ :: _, h, _, _ => by simp [Fits] at h

theorem fieldOf_length {B : Type} : ∀ (P : List Piece) (X : List B) (s k : Nat), s + size P ≤ X.length →
    (fieldOf X s P k).length = fieldSize P k
  | [], _, _, _, _ => rfl
  | .text t :: P, X, s, k, h => by
      rw [size_text] at h
      simp only [fieldOf, fieldSize]
      exact fieldOf_length P X _ k (by omega)
  | .field n :: P, X, s, 0, h => by
      rw [size_field] at h
      simp only [fieldOf, fieldSize]
      exact BundleItemWhole.part_length X s n (by omega)
  | .field n :: P, X, s, k + 1, h => by
      rw [size_field] at h
      simp only [fieldOf, fieldSize]
      exact fieldOf_length P X _ k (by omega)

/-- **The template read through a splice.** If `Y` holds at `s'` the splice of what `X` holds at
`s`, then the text of `Q` is in place in `Y` exactly when the text of `P` is in place in `X`, and
every field of `Q` in `Y` is the field of `P` in `X` preceded by `z`s up to the wider size. -/
theorem splice_pieces {B : Type} (a : ByteAuth.Ops B) (z : B) : ∀ (P Q : List Piece), Fits P Q →
    ∀ (X Y : List B) (s s' : Nat), s + size P ≤ X.length →
    part Y s' (size Q) = applyRuns z (BundleSlots.runs P Q) (part X s (size P)) →
    literals a Y s' Q = literals a X s P ∧
      ∀ k, fieldOf Y s' Q k = List.replicate (fieldSize Q k - fieldSize P k) z ++ fieldOf X s P k
  | [], [], _, _, _, _, _, _, _ => ⟨rfl, fun k => by simp [fieldOf, fieldSize]⟩
  | .text t :: P, .text t' :: Q, ⟨e, hf⟩, X, Y, s, s', hx, hy => by
      subst e
      rw [size_text] at hx hy
      rw [size_text] at hy
      have hI := BundleItemWhole.part_length X s (t.toUTF8.size + size P) hx
      have hy' : part Y s' (t.toUTF8.size + size Q) =
          (part X s (t.toUTF8.size + size P)).take t.toUTF8.size ++
            applyRuns z (BundleSlots.runs P Q) ((part X s (t.toUTF8.size + size P)).drop t.toUTF8.size) := by
        rw [hy]; show List.replicate 0 z ++ _ ++ _ = _; rw [List.replicate_zero, List.nil_append]; rfl
      have lt : ((part X s (t.toUTF8.size + size P)).take t.toUTF8.size).length = t.toUTF8.size := by
        rw [List.length_take, hI]; omega
      have hL : part Y s' t.toUTF8.size = part X s t.toUTF8.size := by
        rw [← part_left Y s' _ (size Q), hy', take_app _ _ _ lt, part_left]
      have hR : part Y (s' + t.toUTF8.size) (size Q) =
          applyRuns z (BundleSlots.runs P Q) (part X (s + t.toUTF8.size) (size P)) := by
        rw [← part_right Y s' _ (size Q), hy', drop_app _ _ _ lt, part_right]
      obtain ⟨ih1, ih2⟩ := splice_pieces a z P Q hf X Y (s + t.toUTF8.size) (s' + t.toUTF8.size) (by omega) hR
      refine ⟨?_, fun k => ?_⟩
      · simp only [literals, ReceiveFirst.expect, BundleItemWhole.literal_length, hL, ih1]
      · simp only [fieldOf, fieldSize]
        exact ih2 k
  | .field n :: P, .field m :: Q, ⟨hnm, hf⟩, X, Y, s, s', hx, hy => by
      rw [size_field] at hx hy
      rw [size_field] at hy
      have hI := BundleItemWhole.part_length X s (n + size P) hx
      have hy' : part Y s' (m + size Q) =
          (List.replicate (m - n) z ++ (part X s (n + size P)).take n) ++
            applyRuns z (BundleSlots.runs P Q) ((part X s (n + size P)).drop n) := hy
      have lt : (List.replicate (m - n) z ++ (part X s (n + size P)).take n).length = m := by simp; omega
      have hF : part Y s' m = List.replicate (m - n) z ++ part X s n := by
        rw [← part_left Y s' _ (size Q), hy', take_app _ _ _ lt, part_left]
      have hR : part Y (s' + m) (size Q) = applyRuns z (BundleSlots.runs P Q) (part X (s + n) (size P)) := by
        rw [← part_right Y s' _ (size Q), hy', drop_app _ _ _ lt, part_right]
      obtain ⟨ih1, ih2⟩ := splice_pieces a z P Q hf X Y (s + n) (s' + m) (by omega) hR
      refine ⟨?_, fun k => ?_⟩
      · simp only [literals, ih1]
      · cases k with
        | zero => simp only [fieldOf, fieldSize, hF]
        | succ k => simp only [fieldOf, fieldSize]; exact ih2 k
  | [], _ :: _, h, _, _, _, _, _, _ => by simp [Fits] at h
  | _ :: _, [], h, _, _, _, _, _, _ => by simp [Fits] at h
  | .text _ :: _, .field _ :: _, h, _, _, _, _, _, _ => by simp [Fits] at h
  | .field _ :: _, .text _ :: _, h, _, _, _, _, _, _ => by simp [Fits] at h

/-! ### `deviceSlots` on the spliced item is `device` on the original -/

/-- The digit counts as the kernel's `widths` input (one byte each). -/
def widthBytes (w : Widths) : List Byte :=
  [BitVec.ofNat 8 w.device, BitVec.ofNat 8 w.registration, BitVec.ofNat 8 w.signed, BitVec.ofNat 8 w.oneTime,
    BitVec.ofNat 8 w.kyber]

theorem ok_bounds (w : Widths) (ok : w.ok = true) :
    1 ≤ w.device ∧ w.device ≤ 3 ∧ 1 ≤ w.registration ∧ w.registration ≤ 5 ∧ 1 ≤ w.signed ∧ w.signed ≤ 10 ∧
      w.oneTime ≤ 10 ∧ 1 ≤ w.kyber ∧ w.kyber ≤ 10 := by
  simp only [Widths.ok, Bool.and_eq_true, decide_eq_true_eq] at ok
  omega

theorem fits_item (w : Widths) (ok : w.ok = true) : Fits (item w) (item (BundleSlots.slots (w.oneTime != 0))) := by
  obtain ⟨_, hd, _, hr, _, hs, hp, _, hk⟩ := ok_bounds w ok
  by_cases hz : w.oneTime = 0
  · simp [BundleResponse.item, BundleSlots.slots, hz, Fits, hd, hr, hs, hk]
  · simp [BundleResponse.item, BundleSlots.slots, hz, Fits, hd, hr, hs, hk, hp]

theorem part_mid (pre A post : List Byte) : part (pre ++ A ++ post) pre.length A.length = A := by
  rw [List.append_assoc]
  have := BundleItemWhole.part_append_right pre (A ++ post) 0 A.length
  rw [Nat.add_zero] at this
  rw [this]
  simp [part]

theorem part_pre (pre A post : List Byte) (o c : Nat) (h : o + c ≤ pre.length) :
    part (pre ++ A ++ post) o c = part pre o c := by
  rw [List.append_assoc, BundleItemWhole.part_append_left _ _ _ _ h]

theorem part_post (pre A post : List Byte) (o c : Nat) :
    part (pre ++ A ++ post) (pre.length + A.length + o) c = part post o c := by
  rw [show pre.length + A.length + o = (pre ++ A).length + o by simp]
  exact BundleItemWhole.part_append_right _ _ _ _

theorem part_after (pre A post : List Byte) (c : Nat) :
    part (pre ++ A ++ post) (pre.length + A.length) c = part post 0 c := by
  have := part_post pre A post 0 c
  rwa [Nat.add_zero] at this

/-- A number field: the slot is the field with `0`s in front, so the slot check with the declared
width is the field's `numberValid`, and the decoded bytes are the same. -/
theorem num_field (Y X : List Byte) (Q P : List Piece) (s k m n L c : Nat)
    (hf : fieldOf Y s Q k = List.replicate (m - n) 0 ++ fieldOf X s P k) (hl : (fieldOf X s P k).length = n)
    (h1 : 1 ≤ n) (hnm : n ≤ m) (hm : m < 256) :
    BundleSlots.slotValid C L (BitVec.ofNat 8 n) (fieldOf Y s Q k) = numberValid C L (fieldOf X s P k) ∧
      numberBytes C c (fieldOf Y s Q k) = numberBytes C c (fieldOf X s P k) := by
  rw [hf]
  subst hl
  exact ⟨slotValid_pad L _ m h1 hnm hm, numberBytes_zeros c _ _⟩

/-- **(a) `deviceSlots` on the item spliced with the digit counts `w` is `device` with `w` on the
item as it was**, the response around it unchanged (`pre` holds the header and the byte before
the item, `post` what follows it). -/
theorem deviceSlots_splice (w : Widths) (ok : w.ok = true) (pre I post : List Byte)
    (hI : I.length = size (item w)) (hpre : firstItem ≤ pre.length) (hpost : 2 ≤ post.length) :
    BundleSlots.deviceSlots C
        (pre ++ applyRuns 0 (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) I ++ post).length
        pre.length (w.oneTime != 0) (widthBytes w)
        (pre ++ applyRuns 0 (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) I ++ post) =
      BundleResponse.device C (pre ++ I ++ post).length pre.length w (pre ++ I ++ post) := by
  obtain ⟨hd1, hd, hr1, hr, hs1, hs, hp, hk1, hk⟩ := ok_bounds w ok
  have fits := fits_item w ok
  generalize ho : (w.oneTime != 0) = o at fits ⊢
  generalize hS : applyRuns 0 (BundleSlots.runs (item w) (item (BundleSlots.slots o))) I = S
  have hSl : S.length = size (item (BundleSlots.slots o)) := by
    rw [← hS]; exact applyRuns_length 0 _ _ fits I hI
  have hYS : part (pre ++ S ++ post) pre.length (size (item (BundleSlots.slots o))) = S := by
    rw [← hSl]; exact part_mid pre S post
  have hXI : part (pre ++ I ++ post) pre.length (size (item w)) = I := by
    rw [← hI]; exact part_mid pre I post
  have hXl : pre.length + size (item w) ≤ (pre ++ I ++ post).length := by simp; omega
  obtain ⟨hlit, hfield⟩ := splice_pieces C (0 : Byte) _ _ fits (pre ++ I ++ post) (pre ++ S ++ post)
    pre.length pre.length hXl (by rw [hYS, hXI, hS])
  have fl := fun k => fieldOf_length (item w) (pre ++ I ++ post) pre.length k hXl
  have fi : firstItem = 73 := rfl
  obtain ⟨hh1, hh2⟩ := BundleItemWhole.header_agree C (pre ++ S ++ post) (pre ++ I ++ post) (fun x c h => by
    rw [part_pre _ _ _ _ _ (by omega), part_pre _ _ _ _ _ (by omega)])
  have hb : ReceiveFirst.expect C (pre ++ S ++ post) (pre.length - 1)
        (RelayEncoding.literal C (if pre.length = firstItem then "[" else ",")) =
      ReceiveFirst.expect C (pre ++ I ++ post) (pre.length - 1)
        (RelayEncoding.literal C (if pre.length = firstItem then "[" else ",")) := by
    have l1 : (RelayEncoding.literal C (if pre.length = firstItem then "[" else ",")).length = 1 := by
      split
      · exact BundleItemWhole.litOpen C
      · exact BundleItemWhole.litComma C
    simp only [ReceiveFirst.expect, l1]
    rw [part_pre _ _ _ _ _ (by omega), part_pre _ _ _ _ _ (by omega)]
  have hstop : ReceiveFirst.expect C (pre ++ S ++ post) (pre.length + size (item (BundleSlots.slots o)))
        (RelayEncoding.literal C (if pre.length + size (item (BundleSlots.slots o)) + 2 = (pre ++ S ++ post).length
          then "]}" else ",")) =
      ReceiveFirst.expect C (pre ++ I ++ post) (pre.length + size (item w))
        (RelayEncoding.literal C (if pre.length + size (item w) + 2 = (pre ++ I ++ post).length then "]}" else ",")) := by
    rw [ite_iff (show pre.length + size (item (BundleSlots.slots o)) + 2 = (pre ++ S ++ post).length ↔
        post.length = 2 by simp only [List.length_append]; omega),
      ite_iff (show pre.length + size (item w) + 2 = (pre ++ I ++ post).length ↔ post.length = 2 by
        simp only [List.length_append]; omega)]
    simp only [ReceiveFirst.expect]
    rw [← hSl, ← hI, part_after, part_after]
  have hend : ReceiveFirst.expect C (pre ++ S ++ post) ((pre ++ S ++ post).length - 2) (RelayEncoding.literal C "]}") =
      ReceiveFirst.expect C (pre ++ I ++ post) ((pre ++ I ++ post).length - 2) (RelayEncoding.literal C "]}") := by
    simp only [ReceiveFirst.expect, BundleItemWhole.litClose]
    rw [show (pre ++ S ++ post).length - 2 = pre.length + S.length + (post.length - 2) by simp; omega, part_post,
      show (pre ++ I ++ post).length - 2 = pre.length + I.length + (post.length - 2) by simp; omega, part_post]
  have b64 : ∀ k, fieldSize (item (BundleSlots.slots o)) k = fieldSize (item w) k →
      fieldOf (pre ++ S ++ post) pre.length (item (BundleSlots.slots o)) k =
        fieldOf (pre ++ I ++ post) pre.length (item w) k := by
    intro k e
    rw [hfield k, e, Nat.sub_self]
    rfl
  have g0 : OpenResult.get C (widthBytes w) 0 = BitVec.ofNat 8 w.device := rfl
  have g1 : OpenResult.get C (widthBytes w) 1 = BitVec.ofNat 8 w.registration := rfl
  have g2 : OpenResult.get C (widthBytes w) 2 = BitVec.ofNat 8 w.signed := rfl
  have g3 : OpenResult.get C (widthBytes w) 3 = BitVec.ofNat 8 w.oneTime := rfl
  have g4 : OpenResult.get C (widthBytes w) 4 = BitVec.ofNat 8 w.kyber := rfl
  have nf := num_field (pre ++ S ++ post) (pre ++ I ++ post) (item (BundleSlots.slots o)) (item w) pre.length
  cases o with
  | false =>
      have hz : w.oneTime = 0 := by simpa using ho
      have fp : ∀ k, fieldSize (item w) k = fieldSize (item ⟨w.device, w.registration, w.signed, 0, w.kyber⟩) k := by
        intro k; cases w; simp only at hz; subst hz; rfl
      obtain ⟨v0, n0⟩ := nf 0 3 w.device 7 1 (by rw [hfield 0, fp]; rfl) (by rw [fl 0, fp]; rfl)
        hd1 hd (by decide)
      obtain ⟨v1, n1⟩ := nf 1 5 w.registration 32 4 (by rw [hfield 1, fp]; rfl)
        (by rw [fl 1, fp]; rfl) hr1 hr (by decide)
      obtain ⟨v2, n2⟩ := nf 2 10 w.signed 32 4 (by rw [hfield 2, fp]; rfl)
        (by rw [fl 2, fp]; rfl) hs1 hs (by decide)
      obtain ⟨v5, n5⟩ := nf 5 10 w.kyber 32 4 (by rw [hfield 5, fp]; rfl)
        (by rw [fl 5, fp]; rfl) hk1 hk (by decide)
      have f3 := b64 3 (by rw [fp]; rfl)
      have f4 := b64 4 (by rw [fp]; rfl)
      have f6 := b64 6 (by rw [fp]; rfl)
      have f7 := b64 7 (by rw [fp]; rfl)
      have q : (BundleSlots.slots false).oneTime = 0 := rfl
      simp only [BundleSlots.deviceSlots, BundleResponse.device, q, hz, hlit, hh1, hh2, hb, hstop, hend,
        g0, g1, g2, g4, v0, v1, v2, v5, n0, n1, n2, n5, f3, f4, f6, f7, ↓reduceIte, Nat.add_zero,
        BundleResponse.optional, bne_self_eq_false, Bool.false_eq_true]
  | true =>
      have hz : w.oneTime ≠ 0 := by simpa using ho
      have hp1 : 1 ≤ w.oneTime := by omega
      have fp : ∀ k, fieldSize (item w) k =
          fieldSize (item ⟨w.device, w.registration, w.signed, w.oneTime, w.kyber⟩) k := fun _ => rfl
      have fq : ∀ k, fieldSize (item w) k = fieldSize ([.text "{\"deviceId\":", .field w.device,
          .text ",\"registrationId\":", .field w.registration,
          .text ",\"signedPreKey\":{\"keyId\":", .field w.signed, .text ",\"publicKey\":\"", .field 44,
          .text "\",\"signature\":\"", .field 86, .text "\"},\"preKey\":",
          .text "{\"keyId\":", .field w.oneTime, .text ",\"publicKey\":\"", .field 44, .text "\"}",
          .text ",\"pqPreKey\":{\"keyId\":", .field w.kyber, .text ",\"publicKey\":\"", .field 2092,
          .text "\",\"signature\":\"", .field 86, .text "\"}}"] : List Piece) k := by
        intro k
        simp only [BundleResponse.item, hz, ↓reduceIte, List.cons_append, List.nil_append]
      obtain ⟨v0, n0⟩ := nf 0 3 w.device 7 1 (by rw [hfield 0, fq]; rfl) (by rw [fl 0, fq]; rfl)
        hd1 hd (by decide)
      obtain ⟨v1, n1⟩ := nf 1 5 w.registration 32 4 (by rw [hfield 1, fq]; rfl)
        (by rw [fl 1, fq]; rfl) hr1 hr (by decide)
      obtain ⟨v2, n2⟩ := nf 2 10 w.signed 32 4 (by rw [hfield 2, fq]; rfl)
        (by rw [fl 2, fq]; rfl) hs1 hs (by decide)
      obtain ⟨v5, n5⟩ := nf 5 10 w.oneTime 32 4 (by rw [hfield 5, fq]; rfl)
        (by rw [fl 5, fq]; rfl) hp1 hp (by decide)
      obtain ⟨v7, n7⟩ := nf 7 10 w.kyber 32 4 (by rw [hfield 7, fq]; rfl)
        (by rw [fl 7, fq]; rfl) hk1 hk (by decide)
      have f3 := b64 3 (by rw [fq]; rfl)
      have f4 := b64 4 (by rw [fq]; rfl)
      have f6 := b64 6 (by rw [fq]; rfl)
      have f8 := b64 8 (by rw [fq]; rfl)
      have f9 := b64 9 (by rw [fq]; rfl)
      have q : (BundleSlots.slots true).oneTime = 10 := rfl
      have t10 : ((10 : Nat) = 0) = False := by simp
      have b10 : ((10 : Nat) != 0) = true := rfl
      simp only [BundleSlots.deviceSlots, BundleResponse.device, q, t10, b10, hz, ho, hlit, hh1, hh2, hb, hstop, hend,
        g0, g1, g2, g3, g4, v0, v1, v2, v5, v7, n0, n1, n2, n5, n7, f3, f4, f6, f8, f9, ↓reduceIte, Nat.reduceAdd,
        BundleResponse.optional]

/-- **(b) The splice produces the slot layout.** For an item laid out for the digit counts `w`
(`size (item w)` bytes), `BundleSlots.spliced w` (what the runtime does, from `splice w`) has
the size of the slot item; its template text is in place exactly when the original's is; and
each of its fields is the original field preceded by `z`s up to the slot's size (base64 fields,
whose sizes do not change, are copied as they are). -/
theorem spliced_layout {B : Type} (a : ByteAuth.Ops B) (z : B) (w : Widths) (ok : w.ok = true) (I : List B)
    (hI : I.length = size (item w)) :
    (BundleSlots.spliced w I z).length = size (item (BundleSlots.slots (w.oneTime != 0))) ∧
      literals a (BundleSlots.spliced w I z) 0 (item (BundleSlots.slots (w.oneTime != 0))) = literals a I 0 (item w) ∧
      ∀ k, fieldOf (BundleSlots.spliced w I z) 0 (item (BundleSlots.slots (w.oneTime != 0))) k =
        List.replicate (fieldSize (item (BundleSlots.slots (w.oneTime != 0))) k - fieldSize (item w) k) z ++
          fieldOf I 0 (item w) k := by
  have fits := fits_item w ok
  have hl : (BundleSlots.spliced w I z).length = size (item (BundleSlots.slots (w.oneTime != 0))) := by
    rw [spliced_eq]; exact applyRuns_length z _ _ fits I hI
  refine ⟨hl, splice_pieces a z (item w) _ fits I (BundleSlots.spliced w I z) 0 0 (by omega) ?_⟩
  have p1 : part (BundleSlots.spliced w I z) 0 (size (item (BundleSlots.slots (w.oneTime != 0)))) =
      BundleSlots.spliced w I z := by
    rw [← hl]; simp [part]
  have p2 : part I 0 (size (item w)) = I := by rw [← hI]; simp [part]
  rw [p1, p2, spliced_eq]

open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-slot` computes `BundleResponse.device` on the body the server sent.** Let `X` be
the response body and the item of digit counts `w` (`w.ok`, as `layout?` returns them) start at
`start`, placed as `layout?` places it. If the kernel `bundle-slot FIRST LAST ONETIME` (with
`ONETIME` = whether `w` has a one-time prekey, as `BundleSlotKernel.arguments` chooses it) gets
as `head`, `before`, `item`, `after`, `end` the header, the byte before the item, the item spliced
by `BundleSlots.spliced w`, the byte after it and the body's last two bytes, and as `widths` the
five digit counts, then its outputs are `BundleResponse.device` on `X` at `start` with `w`:
exactly the outputs `bundle-item` has (`BundleItemWhole.bundleItem_whole`). -/
theorem bundleSlot_device (first last : Bool) (w : Widths) (ok : w.ok = true) (assign : BVExpr.Assignment)
    (X : List Byte) (start : Nat) (placed : BundleItemWhole.Placed X.length first last start (size (item w)))
    (inputs : let get := fun name =>
        (lookup (BundleSlotKernel.slotInputs first last (w.oneTime != 0)) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) ++
          BundleSlots.spliced w (part X start (size (item w))) 0 ++
          (if last then [] else part X (start + size (item w)) 1) ++ part X (X.length - 2) 2)
    (widths : (lookup (BundleSlotKernel.slotInputs first last (w.oneTime != 0)) "widths").map (BVExpr.eval assign) =
      widthBytes w) :
    let out := BundleResponse.device C X.length start w X
    values (BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []]) := by
  have placed' := placed
  obtain ⟨hh, hfit, hfirst, hlast⟩ := placed'
  have fi : firstItem = 73 := rfl
  rw [BundleSlotKernel.bundleSlot_spec]
  dsimp only at inputs ⊢
  rw [inputs, widths, spliced_eq]
  have hI : (part X start (size (item w))).length = size (item w) := BundleItemWhole.part_length X _ _ (by omega)
  generalize hA : part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) = pre
  generalize hC : (if last then [] else part X (start + size (item w)) 1) = af
  generalize hD : part X (X.length - 2) 2 = en
  have hpre : pre.length = firstItem + (if first then 0 else 1) := by
    rw [← hA, List.length_append, BundleItemWhole.part_length X 0 firstItem (by omega)]
    cases first
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [BundleItemWhole.part_length X _ 1 (by omega)]
    · rfl
  have hpost : 2 ≤ (af ++ en).length := by
    rw [List.length_append, ← hD, BundleItemWhole.part_length X _ 2 (by omega)]; omega
  have hcut : pre ++ part X start (size (item w)) ++ (af ++ en) =
      BundleItemWhole.cut X first last start (size (item w)) := by
    rw [← hA, ← hC, ← hD]; simp only [BundleItemWhole.cut, List.append_assoc]
  rw [List.append_assoc _ af en, ← hpre, deviceSlots_splice w ok pre _ (af ++ en) hI (by omega) hpost, hcut, hpre,
    show firstItem + (if first then 0 else 1) = BundleItemWhole.cutStart first from rfl,
    BundleItemWhole.device_cut C X first last start w placed]
  by_cases hz : w.oneTime = 0 <;> simp [hz]

open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-slot` and `bundle-item` give the same outputs** on the same item of the same body:
the first fed the splice and the digit counts, the second the item as it is. -/
theorem bundleSlot_eq_bundleItem (first last : Bool) (w : Widths) (ok : w.ok = true) (X : List Byte) (start : Nat)
    (placed : BundleItemWhole.Placed X.length first last start (size (item w)))
    (assign assign' : BVExpr.Assignment)
    (inputs : let get := fun name =>
        (lookup (BundleSlotKernel.slotInputs first last (w.oneTime != 0)) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) ++
          BundleSlots.spliced w (part X start (size (item w))) 0 ++
          (if last then [] else part X (start + size (item w)) 1) ++ part X (X.length - 2) 2)
    (widths : (lookup (BundleSlotKernel.slotInputs first last (w.oneTime != 0)) "widths").map (BVExpr.eval assign) =
      widthBytes w)
    (inputs' : let get := fun name => (lookup (BundleItemKernel.itemInputs first last w) name).map (BVExpr.eval assign')
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        BundleItemWhole.cut X first last start (size (item w))) :
    values (BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) assign =
      values (BundleItemKernel.bundleItem first last w) assign' := by
  rw [bundleSlot_device first last w ok assign X start placed inputs widths,
    BundleItemWhole.bundleItem_whole first last w assign' X start placed inputs']

/-! ### `device`'s validity byte is 0 or 255 -/

/-- The checks `BundleResponse.device` combines into its validity byte, as written there. -/
def okList (total start : Nat) (w : Widths) (body : List Byte) : List Byte :=
  let field := fieldOf body start (item w)
  let shift := if w.oneTime = 0 then 0 else 2
  let stop := start + size (item w)
  let identity := BundleResponse.decode C (fieldOf body 0 header 0)
  let signedKey := BundleResponse.decode C (field 3)
  let oneTimeKey := BundleResponse.decode C (field 6)
  let kyberKey := BundleResponse.decode C (field (6 + shift))
  [literals C body 0 header, literals C body start (item w),
      ReceiveFirst.expect C body (start - 1) (RelayEncoding.literal C (if start = firstItem then "[" else ",")),
      ReceiveFirst.expect C body stop (RelayEncoding.literal C (if stop + 2 = total then "]}" else ",")),
      ReceiveFirst.expect C body (total - 2) (RelayEncoding.literal C "]}"),
      BundleResponse.decodeValid C (fieldOf body 0 header 0),
      ByteAuth.eqMask C (OpenResult.get C identity 0) (ByteAuth.concrete.const 5),
      numberValid C 7 (field 0), numberValid C 32 (field 1), numberValid C 32 (field 2),
      BundleResponse.decodeValid C (field 3), ByteAuth.eqMask C (OpenResult.get C signedKey 0) (ByteAuth.concrete.const 5),
      BundleResponse.decodeValid C (field 4),
      numberValid C 32 (field (5 + shift)), BundleResponse.decodeValid C (field (6 + shift)),
      ByteAuth.eqMask C (OpenResult.get C kyberKey 0) (ByteAuth.concrete.const 8),
      BundleResponse.decodeValid C (field (7 + shift))] ++
    BundleResponse.optional (w.oneTime != 0) [numberValid C 32 (field 5), BundleResponse.decodeValid C (field 6),
      ByteAuth.eqMask C (OpenResult.get C oneTimeKey 0) (ByteAuth.concrete.const 5)]

theorem device_valid (total start : Nat) (w : Widths) (body : List Byte) :
    (BundleResponse.device C total start w body).getD 0 [] = [ReceiveFirst.all C (okList total start w body)] := rfl

def IsMask (x : Byte) : Prop := x = 0 ∨ x = 255

theorem mask_and {x y : Byte} (hx : IsMask x) (hy : IsMask y) : IsMask (ByteAuth.concrete.and x y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> unfold IsMask <;> decide

theorem mask_not {x : Byte} (hx : IsMask x) : IsMask (ByteAuth.concrete.not x) := by
  rcases hx with rfl | rfl <;> unfold IsMask <;> decide

theorem mask_ite (P : Prop) [Decidable P] : IsMask (if P then 255 else 0) := by
  by_cases h : P
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

theorem mask_foldl_and {α : Type} (f : α → Byte) (hf : ∀ a, IsMask (f a)) :
    ∀ (xs : List α) (init : Byte), IsMask init → IsMask (xs.foldl (fun m a => ByteAuth.concrete.and m (f a)) init)
  | [], _, h => h
  | x :: xs, _, h => mask_foldl_and f hf xs _ (mask_and h (hf x))

theorem mask_all (xs : List Byte) (h : ∀ x ∈ xs, IsMask x) : IsMask (ReceiveFirst.all C xs) := by
  have gen : ∀ (ys : List Byte) (init : Byte), IsMask init → (∀ x ∈ ys, IsMask x) →
      IsMask (ys.foldl ByteAuth.concrete.and init) := by
    intro ys
    induction ys with
    | nil => intro _ hi _; exact hi
    | cons y ys ih =>
        intro init hi hy
        exact ih _ (mask_and hi (hy y (by simp))) (fun x hx => hy x (by simp [hx]))
  exact gen xs _ (Or.inr rfl) h

theorem mask_eqMask (x y : Byte) : IsMask (ByteAuth.eqMask C x y) := by
  rw [ByteAuth.eqMask_value]; exact mask_ite _

theorem mask_expect (X : List Byte) (o : Nat) (lit : List Byte) : IsMask (ReceiveFirst.expect C X o lit) := by
  simp only [ReceiveFirst.expect]
  rw [ByteAuth.equalMask_value]; exact mask_ite _

theorem mask_literals (X : List Byte) : ∀ (P : List Piece) (s : Nat), IsMask (literals C X s P)
  | [], _ => Or.inr rfl
  | .text _ :: P, _ => mask_and (mask_expect _ _ _) (mask_literals X P _)
  | .field _ :: P, _ => mask_literals X P _

theorem mask_maskBit (x : Byte) (i : Nat) : IsMask (ByteAuth.concrete.maskBit x i) := by
  have : ∀ b : BitVec 1, b = 0 ∨ b = 1 := by decide
  rcases this (x.extractLsb' i 1) with h | h
  · left; show BitVec.replicate 8 (x.extractLsb' i 1) = 0; rw [h]; decide
  · right; show BitVec.replicate 8 (x.extractLsb' i 1) = 255; rw [h]; decide

theorem mask_decodeValid (chars : List Byte) : IsMask (BundleResponse.decodeValid C chars) := by
  unfold BundleResponse.decodeValid
  apply mask_and
  · apply mask_all
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx
    rw [TlsMpc.BundleKernel.sextetValid_value]; exact mask_ite _
  · exact mask_foldl_and _ (fun i => mask_not (mask_maskBit _ i)) _ _ (Or.inr rfl)

theorem mask_numberValid (L : Nat) (cs : List Byte) : IsMask (numberValid C L cs) := by
  unfold numberValid
  apply mask_all
  intro x hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with (⟨c, _, rfl⟩ | hx) | ⟨b, hb, rfl⟩
  · rw [TlsMpc.BundleKernel.digitValid_value]; exact mask_ite _
  · unfold BundleResponse.optional at hx
    split at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]; exact mask_not (mask_eqMask _ _)
    · simp at hx
  · apply mask_not
    obtain ⟨R, e, _, _⟩ := numberBits_value cs
    rw [e] at hb
    have hb' := List.mem_of_mem_drop hb
    simp only [List.mem_map] at hb'
    obtain ⟨bit, _, rfl⟩ := hb'
    cases bit
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- **`device`'s validity byte is always 0 or 255** (so a failed check releases nothing at all). -/
theorem device_valid_mask (total start : Nat) (w : Widths) (body : List Byte) :
    IsMask (ReceiveFirst.all C (okList total start w body)) := by
  apply mask_all
  intro x hx
  simp only [okList] at hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact mask_literals _ _ _
      | exact mask_expect _ _ _
      | exact mask_decodeValid _
      | exact mask_eqMask _ _
      | exact mask_numberValid _ _
  · unfold BundleResponse.optional at hx
    split at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact mask_numberValid _ _
      · exact mask_decodeValid _
      · exact mask_eqMask _ _
    · simp at hx

/-! ### Wrong digit counts are refused -/

theorem and_eq_255 (x y : Byte) (h : x &&& y = 255) : x = 255 ∧ y = 255 := by
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_and] at e
  have h1 : x.toNat &&& y.toNat ≤ x.toNat := Nat.and_le_left
  have h2 : x.toNat &&& y.toNat ≤ y.toNat := Nat.and_le_right
  have lx : x.toNat < 256 := x.isLt
  have ly : y.toNat < 256 := y.isLt
  rw [show (255 : Byte).toNat = 255 from rfl] at e
  constructor <;> apply BitVec.eq_of_toNat_eq <;> rw [show (255 : Byte).toNat = 255 from rfl] <;> omega

theorem all_mem_255 : ∀ (xs : List Byte), ReceiveFirst.all C xs = 255 → ∀ x ∈ xs, x = 255
  | [], _, x, hx => by simp at hx
  | y :: ys, h, x, hx => by
      rw [show y :: ys = [y] ++ ys from rfl, all_append, all_single] at h
      obtain ⟨h1, h2⟩ := and_eq_255 _ _ h
      rcases List.mem_cons.mp hx with rfl | hm
      · exact h1
      · exact all_mem_255 ys h2 x hm

theorem literals_append (X : List Byte) : ∀ (A B : List Piece) (s : Nat),
    literals C X s (A ++ B) = literals C X s A &&& literals C X (s + size A) B
  | [], B, s => by
      rw [List.nil_append, show size [] = 0 from rfl, Nat.add_zero]
      exact (and255' _).symm
  | .text t :: A, B, s => by
      simp only [List.cons_append, literals]
      rw [literals_append X A B, size_text, c_and, c_and, BitVec.and_assoc, Nat.add_assoc]
  | .field n :: A, B, s => by
      simp only [List.cons_append, literals]
      rw [literals_append X A B, size_field, Nat.add_assoc]

/-- Number of field pieces. -/
def fieldCount : List Piece → Nat
  | [] => 0
  | .text _ :: P => fieldCount P
  | .field _ :: P => fieldCount P + 1

theorem fieldOf_append (X : List Byte) : ∀ (A : List Piece) (n : Nat) (B : List Piece) (s : Nat),
    fieldOf X s (A ++ .field n :: B) (fieldCount A) = part X (s + size A) n
  | [], n, B, s => by simp [fieldOf, fieldCount, show size [] = 0 from rfl]
  | .text t :: A, n, B, s => by
      simp only [List.cons_append, fieldOf, fieldCount]
      rw [fieldOf_append X A n B, size_text, Nat.add_assoc]
  | .field m :: A, n, B, s => by
      simp only [List.cons_append, fieldCount, fieldOf]
      rw [fieldOf_append X A n B, size_field, Nat.add_assoc]

theorem split_at {α : Type} (P : List α) (i : Nat) (p : α) (hP : P[i]? = some p) :
    P = P.take i ++ p :: P.drop (i + 1) := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hP
  have := (List.take_append_drop i P).symm
  rw [List.drop_eq_getElem_cons hi, he] at this
  exact this

/-- Accepted template text is in the body. -/
theorem text_at (X : List Byte) (s : Nat) (P : List Piece) (h : literals C X s P = 255) (i : Nat) (t : String)
    (hP : P[i]? = some (.text t)) :
    part X (s + size (P.take i)) (RelayEncoding.literal C t).length = RelayEncoding.literal C t := by
  rw [split_at P i _ hP, literals_append] at h
  have h2 := (and_eq_255 _ _ h).2
  simp only [literals] at h2
  rw [c_and] at h2
  have h3 := (and_eq_255 _ _ h2).1
  simp only [ReceiveFirst.expect] at h3
  rw [ByteAuth.equalMask_value] at h3
  split at h3
  · assumption
  · exact absurd h3 (by decide)

theorem field_at (X : List Byte) (s : Nat) (P : List Piece) (i n : Nat) (hP : P[i]? = some (.field n)) :
    fieldOf X s P (fieldCount (P.take i)) = part X (s + size (P.take i)) n := by
  have key := fieldOf_append X (P.take i) n (P.drop (i + 1)) s
  rw [← split_at P i _ hP] at key
  exact key

theorem first_byte (X : List Byte) (o : Nat) (lit : List Byte) (c : Byte) (h : part X o lit.length = lit)
    (hc : lit[0]? = some c) : X[o]? = some c := by
  have hl : 0 < lit.length := by
    cases lit with
    | nil => simp at hc
    | cons _ _ => simp
  have := congrArg (·[0]?) h
  simp only [part, List.getElem?_take, List.getElem?_drop, if_pos hl, Nat.add_zero] at this
  rw [this, hc]

/-- The byte at `i`, if any, is a decimal digit. -/
def IsDigitAt (X : List Byte) (i : Nat) : Prop := ∀ c, X[i]? = some c → 48 ≤ c.toNat ∧ c.toNat ≤ 57

theorem numberValid_digits (L : Nat) (cs : List Byte) (h : numberValid C L cs = 255) :
    ∀ c ∈ cs, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  intro c hc
  have := all_mem_255 _ h (digitValid C c)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hc)))
  rw [TlsMpc.BundleKernel.digitValid_value] at this
  split at this
  · assumption
  · exact absurd this (by decide)

theorem digits_at (X : List Byte) (o n : Nat) (h : ∀ c ∈ part X o n, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    ∀ j < n, IsDigitAt X (o + j) := by
  intro j hj c hc
  apply h
  have : (part X o n)[j]? = some c := by
    simp only [part, List.getElem?_take, List.getElem?_drop, if_pos hj]
    exact hc
  exact List.mem_of_getElem? this

/-- Two decimal fields at the same place, each followed by `,`, have the same length. -/
theorem boundary (X : List Byte) (o n n' : Nat) (hd : ∀ j < n, IsDigitAt X (o + j)) (hc : X[o + n]? = some 44)
    (hd' : ∀ j < n', IsDigitAt X (o + j)) (hc' : X[o + n']? = some 44) : n = n' := by
  rcases Nat.lt_trichotomy n n' with h | h | h
  · exact absurd (hd' n h 44 hc) (by decide)
  · exact h
  · exact absurd (hd n' h 44 hc') (by decide)

/-- The item for digit counts `w`, written out, without and with a one-time prekey. -/
def itemNull (w : Widths) : List Piece :=
  [.text "{\"deviceId\":", .field w.device, .text ",\"registrationId\":", .field w.registration,
    .text ",\"signedPreKey\":{\"keyId\":", .field w.signed, .text ",\"publicKey\":\"", .field 44,
    .text "\",\"signature\":\"", .field 86, .text "\"},\"preKey\":", .text "null",
    .text ",\"pqPreKey\":{\"keyId\":", .field w.kyber, .text ",\"publicKey\":\"", .field 2092,
    .text "\",\"signature\":\"", .field 86, .text "\"}}"]

def itemOne (w : Widths) : List Piece :=
  [.text "{\"deviceId\":", .field w.device, .text ",\"registrationId\":", .field w.registration,
    .text ",\"signedPreKey\":{\"keyId\":", .field w.signed, .text ",\"publicKey\":\"", .field 44,
    .text "\",\"signature\":\"", .field 86, .text "\"},\"preKey\":",
    .text "{\"keyId\":", .field w.oneTime, .text ",\"publicKey\":\"", .field 44, .text "\"}",
    .text ",\"pqPreKey\":{\"keyId\":", .field w.kyber, .text ",\"publicKey\":\"", .field 2092,
    .text "\",\"signature\":\"", .field 86, .text "\"}}"]

theorem item_null (w : Widths) (hz : w.oneTime = 0) : item w = itemNull w := by
  simp [BundleResponse.item, itemNull, hz]

theorem item_one (w : Widths) (hz : w.oneTime ≠ 0) : item w = itemOne w := by
  simp [BundleResponse.item, itemOne, hz]

/-- Where the numbers of an item at `s` with digit counts `w` start. -/
def oR (s : Nat) (w : Widths) : Nat := s + 12 + w.device + 18
def oS (s : Nat) (w : Widths) : Nat := oR s w + w.registration + 25
def oQ (s : Nat) (w : Widths) : Nat := oS s w + w.signed + 171
def oK (s : Nat) (w : Widths) : Nat := if w.oneTime = 0 then oQ s w + 25 else oQ s w + 9 + w.oneTime + 81

/-- What an accepted item says about the body: each number is digits followed by `,`, and the
`preKey` value starts with `n` (`null`) or `{`. -/
structure Facts (X : List Byte) (s : Nat) (w : Widths) : Prop where
  d_digits : ∀ j < w.device, IsDigitAt X (s + 12 + j)
  d_comma : X[s + 12 + w.device]? = some 44
  r_digits : ∀ j < w.registration, IsDigitAt X (oR s w + j)
  r_comma : X[oR s w + w.registration]? = some 44
  s_digits : ∀ j < w.signed, IsDigitAt X (oS s w + j)
  s_comma : X[oS s w + w.signed]? = some 44
  q_byte : X[oQ s w]? = some (if w.oneTime = 0 then 110 else 123)
  p_digits : w.oneTime ≠ 0 → ∀ j < w.oneTime, IsDigitAt X (oQ s w + 9 + j)
  p_comma : w.oneTime ≠ 0 → X[oQ s w + 9 + w.oneTime]? = some 44
  k_digits : ∀ j < w.kyber, IsDigitAt X (oK s w + j)
  k_comma : X[oK s w + w.kyber]? = some 44

theorem comma_at (X : List Byte) (s : Nat) (P : List Piece) (h : literals C X s P = 255) (i : Nat) (t : String)
    (hP : P[i]? = some (.text t)) (c : Byte) (hc : (RelayEncoding.literal C t)[0]? = some c) (o : Nat)
    (ho : s + size (P.take i) = o) : X[o]? = some c := by
  rw [← ho]; exact first_byte X _ _ c (text_at X s P h i t hP) hc

theorem digits_field (X : List Byte) (s : Nat) (P : List Piece) (L k : Nat) (hn : numberValid C L (fieldOf X s P k) = 255)
    (i n : Nat) (hP : P[i]? = some (.field n)) (hk : fieldCount (P.take i) = k) (o : Nat)
    (ho : s + size (P.take i) = o) : ∀ j < n, IsDigitAt X (o + j) := by
  rw [← hk, field_at X s P i n hP, ho] at hn
  exact digits_at X o n (numberValid_digits L _ hn)

theorem facts (X : List Byte) (s : Nat) (w : Widths)
    (accepted : (BundleResponse.device C X.length s w X).getD 0 [] = [255]) : Facts X s w := by
  rw [device_valid] at accepted
  have hall := all_mem_255 _ (List.cons.inj accepted).1
  have hlit : literals C X s (item w) = 255 := hall _ (by simp [okList])
  have hn0 : numberValid C 7 (fieldOf X s (item w) 0) = 255 := hall _ (by simp [okList])
  have hn1 : numberValid C 32 (fieldOf X s (item w) 1) = 255 := hall _ (by simp [okList])
  have hn2 : numberValid C 32 (fieldOf X s (item w) 2) = 255 := hall _ (by simp [okList])
  have hnk : numberValid C 32 (fieldOf X s (item w) (5 + if w.oneTime = 0 then 0 else 2)) = 255 :=
    hall _ (by simp [okList])
  by_cases hz : w.oneTime = 0
  · rw [item_null w hz] at hlit hn0 hn1 hn2 hnk
    rw [if_pos hz] at hnk
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd hz h, fun h => absurd hz h, ?_, ?_⟩
    · have := digits_field X s _ 7 0 hn0 1 w.device rfl rfl (s + 12) rfl
      exact this
    · exact comma_at X s _ hlit 2 _ rfl 44 (by decide) _ (by show s + (12 + w.device) = _; omega)
    · exact digits_field X s _ 32 1 hn1 3 w.registration rfl rfl _ (by show s + (12 + w.device + 18) = _; simp only [oR]; omega)
    · exact comma_at X s _ hlit 4 _ rfl 44 (by decide) _
        (by show s + (12 + w.device + 18 + w.registration) = _; simp only [oR]; omega)
    · exact digits_field X s _ 32 2 hn2 5 w.signed rfl rfl _
        (by show s + (12 + w.device + 18 + w.registration + 25) = _; simp only [oS, oR]; omega)
    · exact comma_at X s _ hlit 6 _ rfl 44 (by decide) _
        (by show s + (12 + w.device + 18 + w.registration + 25 + w.signed) = _; simp only [oS, oR]; omega)
    · rw [if_pos hz]
      exact comma_at X s _ hlit 11 _ rfl 110 (by decide) _
        (by show s + (12 + w.device + 18 + w.registration + 25 + w.signed + 14 + 44 + 15 + 86 + 12) = _
            simp only [oQ, oS, oR]; omega)
    · exact digits_field X s _ 32 5 hnk 13 w.kyber rfl rfl _
        (by show s + (12 + w.device + 18 + w.registration + 25 + w.signed + 14 + 44 + 15 + 86 + 12 + 4 + 21) = _
            simp only [oK, oQ, oS, oR, if_pos hz]; omega)
    · exact comma_at X s _ hlit 14 _ rfl 44 (by decide) _
        (by show s + (12 + w.device + 18 + w.registration + 25 + w.signed + 14 + 44 + 15 + 86 + 12 + 4 + 21 +
              w.kyber) = _
            simp only [oK, oQ, oS, oR, if_pos hz]; omega)
  · have hnp : numberValid C 32 (fieldOf X s (item w) 5) = 255 := hall _ (by simp [okList, BundleResponse.optional, hz])
    rw [item_one w hz] at hlit hn0 hn1 hn2 hnk hnp
    rw [if_neg hz] at hnk
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_, fun _ => ?_, ?_, ?_⟩
    · exact digits_field X s _ 7 0 hn0 1 w.device rfl rfl (s + 12) rfl
    · exact comma_at X s _ hlit 2 _ rfl 44 (by decide) _ (by show s + (12 + w.device) = _; omega)
    · exact digits_field X s _ 32 1 hn1 3 w.registration rfl rfl _ (by show s + (12 + w.device + 18) = _; simp only [oR]; omega)
    · exact comma_at X s _ hlit 4 _ rfl 44 (by decide) _
        (by show s + (12 + w.device + 18 + w.registration) = _; simp only [oR]; omega)
    · exact digits_field X s _ 32 2 hn2 5 w.signed rfl rfl _
        (by show s + (12 + w.device + 18 + w.registration + 25) = _; simp only [oS, oR]; omega)
    · exact comma_at X s _ hlit 6 _ rfl 44 (by decide) _
        (by show s + (12 + w.device + 18 + w.registration + 25 + w.signed) = _; simp only [oS, oR]; omega)
    · rw [if_neg hz]
      exact comma_at X s _ hlit 11 _ rfl 123 (by decide) _
        (by show s + (12 + w.device + 18 + w.registration + 25 + w.signed + 14 + 44 + 15 + 86 + 12) = _
            simp only [oQ, oS, oR]; omega)
    · exact digits_field X s _ 32 5 hnp 12 w.oneTime rfl rfl _
        (by show s + (12 + w.device + 18 + w.registration + 25 + w.signed + 14 + 44 + 15 + 86 + 12 + 9) = _
            simp only [oQ, oS, oR]; omega)
    · exact comma_at X s _ hlit 13 _ rfl 44 (by decide) _
        (by show s + (12 + w.device + 18 + w.registration + 25 + w.signed + 14 + 44 + 15 + 86 + 12 + 9 +
              w.oneTime) = _
            simp only [oQ, oS, oR]; omega)
    · exact digits_field X s _ 32 7 hnk 17 w.kyber rfl rfl _
        (by show s + (12 + w.device + 18 + w.registration + 25 + w.signed + 14 + 44 + 15 + 86 + 12 + 9 +
              w.oneTime + 14 + 44 + 2 + 21) = _
            simp only [oK, oQ, oS, oR, if_neg hz]; omega)
    · exact comma_at X s _ hlit 18 _ rfl 44 (by decide) _
        (by show s + (12 + w.device + 18 + w.registration + 25 + w.signed + 14 + 44 + 15 + 86 + 12 + 9 +
              w.oneTime + 14 + 44 + 2 + 21 + w.kyber) = _
            simp only [oK, oQ, oS, oR, if_neg hz]; omega)

/-- **Only one set of digit counts parses an item.** If `device` accepts the item at `s` with
digit counts `w` and with `w'`, then `w = w'`. -/
theorem device_unique (X : List Byte) (s : Nat) (w w' : Widths)
    (hv : (BundleResponse.device C X.length s w X).getD 0 [] = [255])
    (hv' : (BundleResponse.device C X.length s w' X).getD 0 [] = [255]) : w = w' := by
  have F := facts X s w hv
  have F' := facts X s w' hv'
  have hd := boundary X (s + 12) _ _ F.d_digits F.d_comma F'.d_digits F'.d_comma
  have eR : oR s w' = oR s w := by simp only [oR, hd]
  have r' := F'.r_digits
  have rc' := F'.r_comma
  rw [eR] at r' rc'
  have hr := boundary X (oR s w) _ _ F.r_digits F.r_comma r' rc'
  have eS : oS s w' = oS s w := by simp only [oS, eR, hr]
  have s' := F'.s_digits
  have sc' := F'.s_comma
  rw [eS] at s' sc'
  have hs := boundary X (oS s w) _ _ F.s_digits F.s_comma s' sc'
  have eQ : oQ s w' = oQ s w := by simp only [oQ, eS, hs]
  have q' := F'.q_byte
  rw [eQ, F.q_byte] at q'
  have hzz : (w.oneTime = 0 ↔ w'.oneTime = 0) := by
    by_cases h1 : w.oneTime = 0 <;> by_cases h2 : w'.oneTime = 0 <;> simp only [h1, h2, ↓reduceIte] at q' <;>
      first | (exact ⟨fun _ => h2, fun _ => h1⟩) | (exact absurd q' (by decide)) | (simp [h1, h2])
  have hp : w.oneTime = w'.oneTime := by
    by_cases h1 : w.oneTime = 0
    · rw [h1, hzz.mp h1]
    · have h2 : w'.oneTime ≠ 0 := fun e => h1 (hzz.mpr e)
      have p' := F'.p_digits h2
      have pc' := F'.p_comma h2
      rw [eQ] at p' pc'
      exact boundary X (oQ s w + 9) _ _ (F.p_digits h1) (F.p_comma h1) p' pc'
  have eK : oK s w' = oK s w := by simp only [oK, eQ, hp]
  have k' := F'.k_digits
  have kc' := F'.k_comma
  rw [eK] at k' kc'
  have hk := boundary X (oK s w) _ _ F.k_digits F.k_comma k' kc'
  cases w
  cases w'
  simp only at hd hr hs hp hk
  rw [hd, hr, hs, hp, hk]

theorem getD_zero (L : List (List Byte)) (h : ∀ field ∈ L, ∀ byte ∈ field, byte = 0) (i : Nat) :
    ∀ byte ∈ L.getD i [], byte = 0 := by
  intro byte hb
  rw [List.getD_eq_getElem?_getD] at hb
  cases e : L[i]? with
  | none => rw [e] at hb; simp at hb
  | some f => rw [e] at hb; exact h f (List.mem_of_getElem? e) byte hb

open TlsMpc.ReceiveKernel (values) in
/-- Outputs laid out as `device`'s, for a `device` that refused: all zero. -/
theorem refused_zero (first last : Bool) (w' : Widths) (total start : Nat) (X : List Byte)
    (assign : BVExpr.Assignment)
    (refused : (BundleResponse.device C total start w' X).getD 0 [] = [0])
    (hv : let out := BundleResponse.device C total start w' X
      values (BundleSlotKernel.bundleSlot first last (w'.oneTime != 0)) assign =
        [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
          out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
        (if w'.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []])) :
    ∀ field ∈ values (BundleSlotKernel.bundleSlot first last (w'.oneTime != 0)) assign, ∀ byte ∈ field, byte = 0 := by
  have zero := TlsMpc.BundleKernel.device_rejects total start w' X refused
  dsimp only at hv
  rw [hv]
  intro field hf
  rw [List.mem_append] at hf
  rcases hf with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact getD_zero _ zero _
  · split at h
    · simp at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> exact getD_zero _ zero _

open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **Wrong digit counts: `bundle-slot` refuses.** If the item at `start` of the body `X` is
accepted by `device` with its true digit counts `w`, and the runtime instead splices it with,
and passes as `widths`, other counts `w'` (within `Widths.ok`, the cut placed for `w'`), every
output of the kernel is zero, the validity byte included: nothing is released, in particular
no other number. -/
theorem bundleSlot_wrong_counts (first last : Bool) (w w' : Widths) (ok' : w'.ok = true) (assign : BVExpr.Assignment)
    (X : List Byte) (start : Nat) (placed : BundleItemWhole.Placed X.length first last start (size (item w')))
    (inputs : let get := fun name =>
        (lookup (BundleSlotKernel.slotInputs first last (w'.oneTime != 0)) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) ++
          BundleSlots.spliced w' (part X start (size (item w'))) 0 ++
          (if last then [] else part X (start + size (item w')) 1) ++ part X (X.length - 2) 2)
    (widths : (lookup (BundleSlotKernel.slotInputs first last (w'.oneTime != 0)) "widths").map (BVExpr.eval assign) =
      widthBytes w')
    (accepted : (BundleResponse.device C X.length start w X).getD 0 [] = [255]) (wrong : w' ≠ w) :
    ∀ field ∈ values (BundleSlotKernel.bundleSlot first last (w'.oneTime != 0)) assign, ∀ byte ∈ field, byte = 0 := by
  have refused : (BundleResponse.device C X.length start w' X).getD 0 [] = [0] := by
    rw [device_valid]
    rcases device_valid_mask X.length start w' X with h | h
    · rw [h]
    · exact absurd (device_unique X start w w' accepted (by rw [device_valid, h])).symm wrong
  exact refused_zero first last w' X.length start X assign refused
    (bundleSlot_device first last w' ok' assign X start placed inputs widths)

open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-slot` either parses the item exactly as `device` does with the only digit counts
that fit, or releases nothing.** For whatever digit counts `w'` (within `Widths.ok`) the runtime
splices the item with and passes as `widths`: either `device` accepts the item with `w'`, `w'` is
the only set of digit counts with which it does, and the kernel's outputs are `device`'s; or every
output of the kernel, the validity byte included, is zero. -/
theorem bundleSlot_parses_or_refuses (first last : Bool) (w' : Widths) (ok' : w'.ok = true)
    (assign : BVExpr.Assignment) (X : List Byte) (start : Nat)
    (placed : BundleItemWhole.Placed X.length first last start (size (item w')))
    (inputs : let get := fun name =>
        (lookup (BundleSlotKernel.slotInputs first last (w'.oneTime != 0)) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) ++
          BundleSlots.spliced w' (part X start (size (item w'))) 0 ++
          (if last then [] else part X (start + size (item w')) 1) ++ part X (X.length - 2) 2)
    (widths : (lookup (BundleSlotKernel.slotInputs first last (w'.oneTime != 0)) "widths").map (BVExpr.eval assign) =
      widthBytes w') :
    ((BundleResponse.device C X.length start w' X).getD 0 [] = [255] ∧
      (∀ w, (BundleResponse.device C X.length start w X).getD 0 [] = [255] → w = w') ∧
      let out := BundleResponse.device C X.length start w' X
      values (BundleSlotKernel.bundleSlot first last (w'.oneTime != 0)) assign =
        [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
          out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
        (if w'.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []])) ∨
    (∀ field ∈ values (BundleSlotKernel.bundleSlot first last (w'.oneTime != 0)) assign, ∀ byte ∈ field, byte = 0) := by
  have hv := bundleSlot_device first last w' ok' assign X start placed inputs widths
  rcases device_valid_mask X.length start w' X with h | h
  · right
    exact refused_zero first last w' X.length start X assign (by rw [device_valid, h]) hv
  · left
    have acc : (BundleResponse.device C X.length start w' X).getD 0 [] = [255] := by rw [device_valid, h]
    exact ⟨acc, fun w hw => device_unique X start w w' hw acc, hv⟩

/-! ### A width byte that disagrees with the splice

The runtime derives the splice and the `widths` input from the same digit counts. If they ever
disagreed, a slot check still accepts only the true width: the padding is the `filler` byte (0),
which is not a digit, so a declared width above the digit count puts a filler where a digit must
be, and one below puts the number's first byte where the filler must be. The only hypothesis is
that the number's first byte is not itself the filler (a NUL, which no JSON text contains). -/

/-- **A slot accepts only its true width.** If `cs` (whose first byte is not the filler) is
spliced into a slot of `m` bytes, the slot check accepts the declared width byte `v` only when `v`
is the length of `cs`. (Before the emitter batch the padding was `0` and this needed `cs` to be a
canonical decimal: `zero_padding_ambiguous`.) -/
theorem slotValid_width (L : Nat) (cs : List Byte) (m : Nat) (v : Byte) (h1 : 1 ≤ cs.length) (hnm : cs.length ≤ m)
    (hm : m < 256) (hfirst : OpenResult.get C cs 0 ≠ 0)
    (acc : BundleSlots.slotValid C L v (List.replicate (m - cs.length) 0 ++ cs) = 255) :
    v = BitVec.ofNat 8 cs.length := by
  have hlen : (List.replicate (m - cs.length) 0 ++ cs).length = m := by simp; omega
  simp only [BundleSlots.slotValid, hlen] at acc
  have hall := all_mem_255 _ acc
  have isv : ∀ k, ByteAuth.eqMask C v (ByteAuth.concrete.const k) = if v = BitVec.ofNat 8 k then 255 else 0 :=
    fun k => ByteAuth.eqMask_value _ _
  -- the declared width is some `u` in `1 … m`
  have ha := hall _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_singleton_self _))))
  rw [show (fun k => ByteAuth.eqMask C v (ByteAuth.concrete.const (k + 1))) =
      (fun k => if v = BitVec.ofNat 8 (k + 1) then (255 : Byte) else 0) from funext (fun k => isv (k + 1)),
    any_ite] at ha
  split at ha
  · rename_i hex
    obtain ⟨k, hk, hv⟩ := hex
    rw [List.mem_range] at hk
    have hpd := fun j (hj : j < m) => hall _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hj)))))
    generalize hn : cs.length = n at *
    by_cases e : k + 1 = n
    · rw [hv, e]
    · exfalso
      rcases Nat.lt_or_gt_of_ne e with lt | gt
      · -- declared width below the digit count: the number's first byte is padding, so the filler
        have hp := hpd (m - n) (by omega)
        rw [pad_value v (k + 1) m (m - n) hv (by omega) hm, if_pos (by omega)] at hp
        have g := get_slot_digit cs (m - n) 0
        rw [Nat.add_zero] at g
        rw [g, entry_pad, ByteAuth.eqMask_value] at hp
        split at hp
        · rename_i h0
          exact hfirst h0
        · exact absurd hp (by decide)
      · -- declared width above the digit count: a filler byte would have to be a digit
        have hp := hpd (m - (k + 1)) (by omega)
        rw [pad_value v (k + 1) m (m - (k + 1)) hv (by omega) hm, if_neg (by omega),
          get_slot_pad cs (m - n) _ (by omega), entry_digit] at hp
        exact absurd hp (by decide)
  · exact absurd ha (by decide)

/-- **Why the padding byte changed.** With `0` (48) as padding, the device id `05` spliced with
its two digits and the device id `5` spliced with one digit were the SAME slot `005`, and every
other input of `bundle-slot` can be the same too; so no kernel on these inputs could accept `5` and
refuse `05` when the `widths` byte disagrees with the splice (the former counterexample
`inconsistent_width_accepts`: the slot `005` with width byte 1 was accepted as 5). With the filler
0 the two slots differ. -/
theorem zero_padding_ambiguous :
    List.replicate (3 - 2) (48 : Byte) ++ [48, 53] = List.replicate (3 - 1) 48 ++ [53] ∧
      List.replicate (3 - 2) (0 : Byte) ++ [48, 53] ≠ List.replicate (3 - 1) 0 ++ [53] := by
  decide

/-! ### Any `widths` input, for an item the server wrote -/

/-- The checks `BundleSlots.deviceSlots` combines into its validity byte, as written there. -/
def okListSlots (total start : Nat) (oneTime : Bool) (widths body : List Byte) : List Byte :=
  let w := BundleSlots.slots oneTime
  let field := fieldOf body start (item w)
  let width := fun i => OpenResult.get C widths i
  let shift := if w.oneTime = 0 then 0 else 2
  let stop := start + size (item w)
  let identity := BundleResponse.decode C (fieldOf body 0 header 0)
  let signedKey := BundleResponse.decode C (field 3)
  let oneTimeKey := BundleResponse.decode C (field 6)
  let kyberKey := BundleResponse.decode C (field (6 + shift))
  [literals C body 0 header, literals C body start (item w),
      ReceiveFirst.expect C body (start - 1) (RelayEncoding.literal C (if start = firstItem then "[" else ",")),
      ReceiveFirst.expect C body stop (RelayEncoding.literal C (if stop + 2 = total then "]}" else ",")),
      ReceiveFirst.expect C body (total - 2) (RelayEncoding.literal C "]}"),
      BundleResponse.decodeValid C (fieldOf body 0 header 0),
      ByteAuth.eqMask C (OpenResult.get C identity 0) (ByteAuth.concrete.const 5),
      BundleSlots.slotValid C 7 (width 0) (field 0), BundleSlots.slotValid C 32 (width 1) (field 1),
      BundleSlots.slotValid C 32 (width 2) (field 2),
      BundleResponse.decodeValid C (field 3), ByteAuth.eqMask C (OpenResult.get C signedKey 0) (ByteAuth.concrete.const 5),
      BundleResponse.decodeValid C (field 4),
      BundleSlots.slotValid C 32 (width 4) (field (5 + shift)), BundleResponse.decodeValid C (field (6 + shift)),
      ByteAuth.eqMask C (OpenResult.get C kyberKey 0) (ByteAuth.concrete.const 8),
      BundleResponse.decodeValid C (field (7 + shift))] ++
    BundleResponse.optional (w.oneTime != 0) [BundleSlots.slotValid C 32 (width 3) (field 5),
      BundleResponse.decodeValid C (field 6), ByteAuth.eqMask C (OpenResult.get C oneTimeKey 0) (ByteAuth.concrete.const 5)]

theorem deviceSlots_valid (total start : Nat) (oneTime : Bool) (widths body : List Byte) :
    (BundleSlots.deviceSlots C total start oneTime widths body).getD 0 [] =
      [ReceiveFirst.all C (okListSlots total start oneTime widths body)] := rfl

theorem mask_either {x y : Byte} (hx : IsMask x) (hy : IsMask y) : IsMask (ReceiveFirst.either C x y) :=
  mask_not (mask_and (mask_not hx) (mask_not hy))

theorem mask_any (xs : List Byte) (h : ∀ x ∈ xs, IsMask x) : IsMask (ReceiveFirst.any C xs) := by
  have gen : ∀ (ys : List Byte) (init : Byte), IsMask init → (∀ x ∈ ys, IsMask x) →
      IsMask (ys.foldl (ReceiveFirst.either C) init) := by
    intro ys
    induction ys with
    | nil => intro _ hi _; exact hi
    | cons y ys ih =>
        intro init hi hy
        exact ih _ (mask_either hi (hy y (by simp))) (fun x hx => hy x (by simp [hx]))
  exact gen xs _ (Or.inl rfl) h

theorem mask_numberBits (cs : List Byte) : ∀ b ∈ numberBits C cs, IsMask b := by
  intro b hb
  obtain ⟨R, e, _, _⟩ := numberBits_value cs
  rw [e] at hb
  simp only [List.mem_map] at hb
  obtain ⟨bit, _, rfl⟩ := hb
  cases bit
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem mask_slotValid (L : Nat) (v : Byte) (chars : List Byte) : IsMask (BundleSlots.slotValid C L v chars) := by
  simp only [BundleSlots.slotValid]
  apply mask_all
  intro x hx
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
  have hpad : ∀ j, IsMask (ReceiveFirst.any C ((List.range (chars.length - j)).map
      (fun k => ByteAuth.eqMask C v (ByteAuth.concrete.const k)))) := by
    intro j
    apply mask_any
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨k, _, rfl⟩ := hy
    exact mask_eqMask _ _
  rcases hx with (((rfl | ⟨j, _, rfl⟩) | ⟨j, _, rfl⟩) | ⟨b, hb, rfl⟩)
  · apply mask_any
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨k, _, rfl⟩ := hy
    exact mask_eqMask _ _
  · apply mask_either (mask_and (hpad j) (mask_eqMask _ _))
    apply mask_and (mask_not (hpad j))
    rw [TlsMpc.BundleKernel.digitValid_value]; exact mask_ite _
  · exact mask_not (mask_and (mask_eqMask _ _) (mask_eqMask _ _))
  · exact mask_not (mask_numberBits chars b (List.mem_of_mem_drop hb))

/-- **The former counterexample, now refused for every width byte.** The device id `05` (refused by
`numberValid`, hence by `device`, whatever the digit count), spliced with its two digits into the
3-byte slot (filler, `0`, `5`), is refused by the slot check whatever the width byte says
(`slotValid_width`: only the width 2 could pass, and there the check is `numberValid` of `05`). -/
theorem inconsistent_width_refused :
    (∀ v : Byte, BundleSlots.slotValid C 7 v (List.replicate (3 - 2) 0 ++ [48, 53]) = 0) ∧
      numberValid C 7 [48, 53] = 0 := by
  have hn : numberValid C 7 [48, 53] = 0 := by decide
  refine ⟨fun v => ?_, hn⟩
  rcases mask_slotValid 7 v (List.replicate (3 - 2) 0 ++ [48, 53]) with h | h
  · exact h
  · exfalso
    have hv := slotValid_width 7 [48, 53] 3 v (by decide) (by decide) (by decide) (by decide) h
    have hp : BundleSlots.slotValid C 7 (BitVec.ofNat 8 [48, 53].length) (List.replicate (3 - 2) 0 ++ [48, 53]) =
        numberValid C 7 [48, 53] := slotValid_pad 7 [48, 53] 3 (by decide) (by decide) (by decide)
    rw [hv] at h
    have e := h.symm.trans hp
    rw [hn] at e
    exact absurd e (by decide)

/-- `deviceSlots`'s validity byte is always 0 or 255, whatever the `widths` input. -/
theorem deviceSlots_valid_mask (total start : Nat) (oneTime : Bool) (widths body : List Byte) :
    IsMask (ReceiveFirst.all C (okListSlots total start oneTime widths body)) := by
  apply mask_all
  intro x hx
  simp only [okListSlots] at hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | with_reducible exact mask_literals _ _ _
      | with_reducible exact mask_expect _ _ _
      | with_reducible exact mask_decodeValid _
      | with_reducible exact mask_eqMask _ _
      | with_reducible exact mask_slotValid _ _ _
  · unfold BundleResponse.optional at hx
    split at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact mask_slotValid _ _ _
      · exact mask_decodeValid _
      · exact mask_eqMask _ _
    · simp at hx

/-- **The `widths` input either is the digit counts or nothing is released.** The item spliced
with its digit counts `w` (no field of it starting with the filler byte 0; whether or not `device`
accepts it), whatever the five `widths` bytes `V`: `deviceSlots` with `V` is `deviceSlots` with
the true counts (every byte it reads agrees), or its validity byte is 0. (With
`bundleSlot_any_widths` this covers the `widths` mutations of `check_bundle_slots.py`: a count
one too small or too large, 0, beyond the slot.) Before the emitter batch this needed `device` to
accept the item. -/
theorem deviceSlots_any_widths (w : Widths) (ok : w.ok = true) (pre I post : List Byte)
    (hI : I.length = size (item w))
    (lead : ∀ k, 1 ≤ (fieldOf (pre ++ I ++ post) pre.length (item w) k).length →
      OpenResult.get C (fieldOf (pre ++ I ++ post) pre.length (item w) k) 0 ≠ 0) (V : List Byte) :
    BundleSlots.deviceSlots C
        (pre ++ applyRuns 0 (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) I ++ post).length
        pre.length (w.oneTime != 0) V
        (pre ++ applyRuns 0 (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) I ++ post) =
      BundleSlots.deviceSlots C
        (pre ++ applyRuns 0 (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) I ++ post).length
        pre.length (w.oneTime != 0) (widthBytes w)
        (pre ++ applyRuns 0 (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) I ++ post) ∨
    (BundleSlots.deviceSlots C
        (pre ++ applyRuns 0 (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) I ++ post).length
        pre.length (w.oneTime != 0) V
        (pre ++ applyRuns 0 (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) I ++ post)).getD 0 []
      = [0] := by
  obtain ⟨hd1, hd, hr1, hr, hs1, hs, hp, hk1, hk⟩ := ok_bounds w ok
  have fits := fits_item w ok
  generalize ho : (w.oneTime != 0) = o at fits ⊢
  generalize hS : applyRuns 0 (BundleSlots.runs (item w) (item (BundleSlots.slots o))) I = S
  rcases deviceSlots_valid_mask (pre ++ S ++ post).length pre.length o V (pre ++ S ++ post) with h | h
  · right; rw [deviceSlots_valid, h]
  left
  have hall := all_mem_255 _ h
  have hSl : S.length = size (item (BundleSlots.slots o)) := by
    rw [← hS]; exact applyRuns_length 0 _ _ fits I hI
  have hYS : part (pre ++ S ++ post) pre.length (size (item (BundleSlots.slots o))) = S := by
    rw [← hSl]; exact part_mid pre S post
  have hXI : part (pre ++ I ++ post) pre.length (size (item w)) = I := by
    rw [← hI]; exact part_mid pre I post
  have hXl : pre.length + size (item w) ≤ (pre ++ I ++ post).length := by simp; omega
  obtain ⟨_, hfield⟩ := splice_pieces C (0 : Byte) _ _ fits (pre ++ I ++ post) (pre ++ S ++ post)
    pre.length pre.length hXl (by rw [hYS, hXI, hS])
  have fl := fun k => fieldOf_length (item w) (pre ++ I ++ post) pre.length k hXl
  have slotw : ∀ (k m L i : Nat), fieldSize (item (BundleSlots.slots o)) k = m → 1 ≤ fieldSize (item w) k →
      fieldSize (item w) k ≤ m → m < 256 →
      BundleSlots.slotValid C L (OpenResult.get C V i) (fieldOf (pre ++ S ++ post) pre.length (item (BundleSlots.slots o)) k)
        = 255 →
      OpenResult.get C V i = BitVec.ofNat 8 (fieldSize (item w) k) := by
    intro k m L i hq h1 h2 h3 hsv
    rw [hfield k, hq, ← fl k] at hsv
    have := slotValid_width L _ m _ (by rw [fl k]; exact h1) (by rw [fl k]; exact h2) h3
      (lead k (by rw [fl k]; exact h1)) hsv
    rw [this, fl k]
  have g0 : OpenResult.get C (widthBytes w) 0 = BitVec.ofNat 8 w.device := rfl
  have g1 : OpenResult.get C (widthBytes w) 1 = BitVec.ofNat 8 w.registration := rfl
  have g2 : OpenResult.get C (widthBytes w) 2 = BitVec.ofNat 8 w.signed := rfl
  have g3 : OpenResult.get C (widthBytes w) 3 = BitVec.ofNat 8 w.oneTime := rfl
  have g4 : OpenResult.get C (widthBytes w) 4 = BitVec.ofNat 8 w.kyber := rfl
  have v0 : OpenResult.get C V 0 = BitVec.ofNat 8 w.device :=
    slotw 0 3 7 0 rfl hd1 hd (by decide) (hall _ (by simp [okListSlots]))
  have v1 : OpenResult.get C V 1 = BitVec.ofNat 8 w.registration :=
    slotw 1 5 32 1 rfl hr1 hr (by decide) (hall _ (by simp [okListSlots]))
  have v2 : OpenResult.get C V 2 = BitVec.ofNat 8 w.signed :=
    slotw 2 10 32 2 rfl hs1 hs (by decide) (hall _ (by simp [okListSlots]))
  cases o with
  | false =>
      have hz : w.oneTime = 0 := by simpa using ho
      have fp5 : fieldSize (item w) 5 = w.kyber := by rw [item_null w hz]; rfl
      have v4 : OpenResult.get C V 4 = BitVec.ofNat 8 w.kyber := by
        rw [← fp5]
        exact slotw 5 10 32 4 rfl (by rw [fp5]; exact hk1) (by rw [fp5]; exact hk) (by decide)
          (hall _ (by simp [okListSlots, BundleSlots.slots]))
      have q : (BundleSlots.slots false).oneTime = 0 := rfl
      simp only [BundleSlots.deviceSlots, q, v0, v1, v2, v4, g0, g1, g2, g4, ↓reduceIte, Nat.add_zero,
        BundleResponse.optional, bne_self_eq_false, Bool.false_eq_true]
  | true =>
      have hz : w.oneTime ≠ 0 := by simpa using ho
      have fp5 : fieldSize (item w) 5 = w.oneTime := by rw [item_one w hz]; rfl
      have fp7 : fieldSize (item w) 7 = w.kyber := by rw [item_one w hz]; rfl
      have v3 : OpenResult.get C V 3 = BitVec.ofNat 8 w.oneTime := by
        rw [← fp5]
        exact slotw 5 10 32 3 rfl (by rw [fp5]; omega) (by rw [fp5]; exact hp) (by decide)
          (hall _ (by simp [okListSlots, BundleSlots.slots, BundleResponse.optional]))
      have v4 : OpenResult.get C V 4 = BitVec.ofNat 8 w.kyber := by
        rw [← fp7]
        exact slotw 7 10 32 4 rfl (by rw [fp7]; exact hk1) (by rw [fp7]; exact hk) (by decide)
          (hall _ (by simp [okListSlots, BundleSlots.slots]))
      have q : (BundleSlots.slots true).oneTime = 10 := rfl
      have t10 : ((10 : Nat) = 0) = False := by simp
      have b10 : ((10 : Nat) != 0) = true := rfl
      simp only [BundleSlots.deviceSlots, q, t10, b10, v0, v1, v2, v3, v4, g0, g1, g2, g3, g4, ↓reduceIte,
        Nat.reduceAdd, BundleResponse.optional]

open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-slot` on an item the server wrote, whatever the `widths` input.** If the runtime
splices the item at `start` of `X` with digit counts `w` (and no field of the item starts with a
NUL byte, the filler), then for ANY five bytes as `widths` the kernel either gives exactly
`device`'s outputs with `w` (those of `bundle-item`; all zero if `device` refuses the item) or
releases nothing at all. Before the emitter batch this needed `device` to accept the item (a
canonical body): a non-canonical number (`05`) with a `widths` byte that disagreed with the splice
was accepted (`zero_padding_ambiguous`, `inconsistent_width_refused`). -/
theorem bundleSlot_any_widths (first last : Bool) (w : Widths) (ok : w.ok = true) (assign : BVExpr.Assignment)
    (X : List Byte) (start : Nat) (placed : BundleItemWhole.Placed X.length first last start (size (item w)))
    (inputs : let get := fun name =>
        (lookup (BundleSlotKernel.slotInputs first last (w.oneTime != 0)) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) ++
          BundleSlots.spliced w (part X start (size (item w))) 0 ++
          (if last then [] else part X (start + size (item w)) 1) ++ part X (X.length - 2) 2)
    (lead : ∀ k, 1 ≤ (fieldOf X start (item w) k).length → OpenResult.get C (fieldOf X start (item w) k) 0 ≠ 0) :
    (let out := BundleResponse.device C X.length start w X;
      values (BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) assign =
        [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
          out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
        (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []])) ∨
    (∀ field ∈ values (BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) assign, ∀ byte ∈ field, byte = 0) := by
  have placed' := placed
  obtain ⟨hh, hfit, hfirst, hlast⟩ := placed'
  have fi : firstItem = 73 := rfl
  rw [BundleSlotKernel.bundleSlot_spec]
  dsimp only at inputs ⊢
  rw [inputs, spliced_eq]
  have hI : (part X start (size (item w))).length = size (item w) := BundleItemWhole.part_length X _ _ (by omega)
  generalize (lookup (BundleSlotKernel.slotInputs first last (w.oneTime != 0)) "widths").map (BVExpr.eval assign) = V
  generalize hA : part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) = pre
  generalize hC : (if last then [] else part X (start + size (item w)) 1) = af
  generalize hD : part X (X.length - 2) 2 = en
  have hpre : pre.length = firstItem + (if first then 0 else 1) := by
    rw [← hA, List.length_append, BundleItemWhole.part_length X 0 firstItem (by omega)]
    cases first
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [BundleItemWhole.part_length X _ 1 (by omega)]
    · rfl
  have hpost : 2 ≤ (af ++ en).length := by
    rw [List.length_append, ← hD, BundleItemWhole.part_length X _ 2 (by omega)]; omega
  have hcut : pre ++ part X start (size (item w)) ++ (af ++ en) =
      BundleItemWhole.cut X first last start (size (item w)) := by
    rw [← hA, ← hC, ← hD]; simp only [BundleItemWhole.cut, List.append_assoc]
  have hagree : BundleItemWhole.Agree (pre ++ part X start (size (item w)) ++ (af ++ en)) X pre.length start
      (size (item w)) := by
    intro x c hxc
    rw [List.append_assoc, BundleItemWhole.part_append_right,
      BundleItemWhole.part_append_left _ _ _ _ (by rw [hI]; exact hxc),
      BundleItemWhole.part_part X start _ x c hxc]
  have lead' : ∀ k, 1 ≤ (fieldOf (pre ++ part X start (size (item w)) ++ (af ++ en)) pre.length (item w) k).length →
      OpenResult.get C (fieldOf (pre ++ part X start (size (item w)) ++ (af ++ en)) pre.length (item w) k) 0 ≠ 0 := by
    intro k
    have e := BundleItemWhole.fieldOf_agree _ X pre.length start (size (item w)) hagree (item w) 0 k (by omega)
    rw [Nat.add_zero, Nat.add_zero] at e
    rw [e]
    exact lead k
  rw [List.append_assoc _ af en, ← hpre]
  rcases deviceSlots_any_widths w ok pre _ (af ++ en) hI lead' V with e | e
  · left
    rw [e, deviceSlots_splice w ok pre _ (af ++ en) hI (by omega) hpost, hcut, hpre,
      show firstItem + (if first then 0 else 1) = BundleItemWhole.cutStart first from rfl,
      BundleItemWhole.device_cut C X first last start w placed]
    by_cases hz : w.oneTime = 0 <;> simp [hz]
  · right
    have zero := TlsMpc.BundleSlotKernel.slot_rejects _ _ _ _ _ e
    intro field hf
    rw [List.mem_append] at hf
    rcases hf with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact getD_zero _ zero _
    · split at h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> exact getD_zero _ zero _
      · simp at h

#print axioms numberBits_value
#print axioms numberBits_decimal
#print axioms numberBits_zeros
#print axioms numberBytes_zeros
#print axioms slotValid_pad
#print axioms spliced_eq
#print axioms splice_pieces
#print axioms spliced_layout
#print axioms deviceSlots_splice
#print axioms bundleSlot_device
#print axioms bundleSlot_eq_bundleItem
#print axioms device_valid_mask
#print axioms deviceSlots_valid_mask
#print axioms device_unique
#print axioms bundleSlot_wrong_counts
#print axioms bundleSlot_parses_or_refuses
#print axioms slotValid_width
#print axioms inconsistent_width_refused
#print axioms zero_padding_ambiguous
#print axioms deviceSlots_any_widths
#print axioms bundleSlot_any_widths

end TlsMpc.KernelSpecs.BundleSlotWhole
