import TlsMpcProofs.EdwardsBasePoint
import TlsMpcProofs.MontgomeryLadder

/-!
# The main package's scalar-multiple chains are scalar multiples in the Edwards group

Every individual addition of these programs is already the group law (`affine_pointAddValue`,
`extRep_extAddValue`); here the chains built from them are identified with `n • P`.

* **Windows** (`EdwardsHinted.windowValue`, the step of `EdwardsAffine.window`): for a curve point
  `P`, its eight entries are `P, 2P, …, 8P` and its next base is `16P` (`window_spec`); the whole
  table `chain windowValue r n` has entry `8w + j` equal to `((j+1)·16^w)·P` (`windowChain_spec`);
  `EdwardsAffine.bitEntry` reads `2^i·P` from it (`bitEntry_spec`), in particular from
  `prepareHinted`'s table once every link holds (`prepareHinted_bitEntry`).
* **Doublings** (`EdwardsHinted.doublingsValue`, the step of `bitTable`): entries `P, 2P, 4P, 8P`
  (extended coordinates), next base `16P` (`doublings_spec`); `chain doublingsValue r n` has entry
  `i` equal to `2^i·P` (`doublingsChain_spec`), in particular `bitTable` once every link holds
  (`bitTable_entry`).
* **Signed base-16 recoding** (`recode`, exactly the rule of `edwards_points.h`'s `step`:
  `digit = nibble + carry; carry = digit > 8; digit -= 16·carry`): the digits encode the number
  (`recode_value`), lie in `−8 … 8` (`recode_bound`), and 64 windows leave no carry for an offset
  below `2²⁵²` (`recode_carry_zero`, `recode64_value`). A signed table entry is the signed multiple
  (`signed_entry`); a list of signed multiples sums to the multiple by the digits' value
  (`sum_digits_smul`); hence `EdwardsAffine.offsetSum`, fed by that rule, outputs the Montgomery
  coordinate of `I + n·P` (`offsetSum_value`, `offsetSum_recoded`).
* **XEdDSA `doubleScalar`** (`Signal.XEdDsaField`): its addition is the group law
  (`xrep_add`), `mulBits`/`mul` is double-and-add (`xrep_mulBits`), and
  `doubleScalar concrete x y h s` is the affine point `[s]B − [h]A` for `A = (x, y)` and Boolean
  bit lists (`doubleScalar_spec`); `run concrete false input` with the bits of `h < 2²⁵⁶` and
  `s < 2²⁵³` computes `s·B − h·A` (`run_doubleScalar_spec`).
-/

namespace TlsMpcProofs.Ed25519
open TlsMpc Edwards
open FieldDag (F ofNat)

theorem getD_eq_getElem' {α : Type*} (l : List α) {i : ℕ} (d : α) (h : i < l.length) :
    l.getD i d = l[i] :=
  (List.getElem_eq_getD d).symm

theorem getD_append_left' {α : Type*} (l₁ l₂ : List α) {i : ℕ} (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {α : Type*} (l₁ l₂ : List α) {i : ℕ} (d : α) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_map' {α β : Type*} (f : α → β) (l : List α) (i : ℕ) (d : α) :
    (l.map f).getD i (f d) = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

/-! ### Windows -/

section Windows
open EdwardsAffine EdwardsHinted

/-- The step of `windowValue`'s fold. -/
def wstep (b : Value) (acc : List Value) (i : ℕ) : List Value :=
  acc ++ [pointAddValue (acc.getD ((i + 2 + 1) / 2 - 1) b) (acc.getD ((i + 2) / 2 - 1) b)]

theorem windowValue_eq (b : Value) :
    windowValue b = ((List.range 7).foldl (wstep b) [b],
      pointAddValue (((List.range 7).foldl (wstep b) [b]).getD 7 b)
        (((List.range 7).foldl (wstep b) [b]).getD 7 b)) := rfl

/-- The list holds `P, 2P, 3P, …`. -/
def Multiples (l : List Value) (P : Curve) : Prop :=
  ∀ k (hk : k < l.length), Affine l[k] ((k + 1) • P)

theorem fold_wstep {b : Value} {P : Curve} (hb : Affine b P) : ∀ n : ℕ,
    ((List.range n).foldl (wstep b) [b]).length = n + 1 ∧
      Multiples ((List.range n).foldl (wstep b) [b]) P
  | 0 => by
    refine ⟨rfl, ?_⟩
    intro k hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simpa using hb
  | n + 1 => by
    obtain ⟨hl, hm⟩ := fold_wstep hb n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (wstep b) [b] = acc at hl hm
    have ha : (n + 2 + 1) / 2 - 1 < acc.length := by omega
    have hc : (n + 2) / 2 - 1 < acc.length := by omega
    refine ⟨by simp [wstep, hl], ?_⟩
    intro k hk
    simp only [wstep, List.length_append, List.length_singleton] at hk ⊢
    by_cases hkn : k < acc.length
    · rw [List.getElem_append_left hkn]
      exact hm k hkn
    · have hk1 : k = acc.length := by omega
      subst hk1
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      rw [getD_eq_getElem' _ _ ha, getD_eq_getElem' _ _ hc]
      have e : (acc.length + 1) • P =
          ((n + 2 + 1) / 2 - 1 + 1) • P + ((n + 2) / 2 - 1 + 1) • P := by
        rw [← add_nsmul]
        congr 1
        omega
      rw [e]
      exact affine_pointAddValue (hm _ ha) (hm _ hc)

/-- **One window:** for a curve point `P`, `windowValue` gives `P, 2P, …, 8P` and the next base
`16P`. -/
theorem window_spec {b : Value} {P : Curve} (hb : Affine b P) :
    (windowValue b).1.length = 8 ∧ Multiples (windowValue b).1 P ∧
      Affine (windowValue b).2 (16 • P) := by
  rw [windowValue_eq]
  obtain ⟨hl, hm⟩ := fold_wstep hb 7
  generalize (List.range 7).foldl (wstep b) [b] = acc at hl hm
  refine ⟨hl, hm, ?_⟩
  have h7 : 7 < acc.length := by omega
  rw [getD_eq_getElem' _ _ h7]
  have e : (16 : ℕ) • P = (7 + 1) • P + (7 + 1) • P := by rw [← add_nsmul]
  rw [e]
  exact affine_pointAddValue (hm 7 h7) (hm 7 h7)

/-- **A chain of steps** (`EdwardsHinted.chain`): if each step maps a curve point `P` to `m`
entries related to `f j • P` and a next base `M • P`, entry `m·w + j` of the chain is
`(f j · M^w) • P`. -/
theorem chain_spec {β : Type} (Rel : β → Curve → Prop) (stepV : Value → List β × Value)
    (m M : ℕ) (f : ℕ → ℕ) (dflt : β)
    (hstep : ∀ (r : Value) (P : Curve), Affine r P → (stepV r).1.length = m ∧
      (∀ j < m, Rel ((stepV r).1.getD j dflt) (f j • P)) ∧ Affine (stepV r).2 (M • P)) :
    ∀ (n : ℕ) (r : Value) (P : Curve), Affine r P →
      (chain stepV r n).length = m * n ∧
        ∀ w < n, ∀ j < m, Rel ((chain stepV r n).getD (m * w + j) dflt) ((f j * M ^ w) • P)
  | 0, r, P, _ => ⟨rfl, fun w hw => absurd hw (Nat.not_lt_zero w)⟩
  | n + 1, r, P, hr => by
    obtain ⟨hl, he, hn⟩ := hstep r P hr
    obtain ⟨il, ie⟩ := chain_spec Rel stepV m M f dflt hstep n _ _ hn
    show ((stepV r).1 ++ chain stepV (stepV r).2 n).length = m * (n + 1) ∧
      ∀ w < n + 1, ∀ j < m,
        Rel (((stepV r).1 ++ chain stepV (stepV r).2 n).getD (m * w + j) dflt) ((f j * M ^ w) • P)
    refine ⟨by rw [List.length_append, hl, il]; ring, ?_⟩
    intro w hw j hj
    cases w with
    | zero =>
      rw [getD_append_left' _ _ _ (by omega)]
      simpa using he j hj
    | succ w =>
      rw [getD_append_right' _ _ _ (by rw [hl]; nlinarith)]
      have e : m * (w + 1) + j - (stepV r).1.length = m * w + j := by
        rw [hl, mul_add, mul_one]; omega
      rw [e]
      have h := ie w (by omega) j hj
      rw [smul_smul] at h
      rwa [pow_succ, ← mul_assoc]

/-- **The window table:** entry `8w + j` of `chain windowValue r n` is `((j+1)·16^w)·P`. -/
theorem windowChain_spec {r : Value} {P : Curve} (hr : Affine r P) (n : ℕ) :
    (chain windowValue r n).length = 8 * n ∧
      ∀ w < n, ∀ j < 8,
        Affine ((chain windowValue r n).getD (8 * w + j) (ofNat 0, ofNat 1)) (((j + 1) * 16 ^ w) • P) :=
  chain_spec Affine windowValue 8 16 (fun j => j + 1) (ofNat 0, ofNat 1)
    (fun r P hr => by
      obtain ⟨hl, hm, hn⟩ := window_spec hr
      refine ⟨hl, fun j hj => ?_, hn⟩
      rw [getD_eq_getElem' _ _ (by omega)]
      exact hm j (by omega)) n r P hr

/-- **`bitEntry` reads `2^i·P`** from the window table (`i < 4n`). -/
theorem bitEntry_spec {r : Value} {P : Curve} (hr : Affine r P) (n i : ℕ) (hi : i < 4 * n) :
    Affine ((chain windowValue r n).getD (digits * (i / 4) + (2 ^ (i % 4) - 1)) (ofNat 0, ofNat 1))
      (2 ^ i • P) := by
  have h4 : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hp : 1 ≤ 2 ^ (i % 4) := Nat.one_le_two_pow
  have hp8 : 2 ^ (i % 4) ≤ 8 := by
    calc 2 ^ (i % 4) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 8 := by norm_num
  have h := (windowChain_spec hr n).2 (i / 4) (by omega) (2 ^ (i % 4) - 1) (by omega)
  have e : (2 ^ (i % 4) - 1 + 1) * 16 ^ (i / 4) = 2 ^ i := by
    rw [Nat.sub_add_cancel hp, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [e] at h
  exact h

/-- **`prepareHinted`'s table entry for bit `i` is `2^i·P`** once every link holds (`P` the curve
point at inputs 0, 1; `i < 256`). -/
theorem prepareHinted_bitEntry (input : ℕ → F) {P : Curve} (hP : Affine (input 0, input 1) P)
    (h : LinkedFrom (evalPoint input) window (inputPoint 0)
      ((List.range (windows - 1)).map (fun i => hinted (prepareHints + 4 * i))))
    (i : ℕ) (hi : i < 256) :
    Affine (evalPoint input (bitEntry (entries window (prepareBases ())) i)) (2 ^ i • P) := by
  have hs := prepareTable_sound input h
  unfold bitEntry
  rw [← getD_map' (evalPoint input), hs]
  exact bitEntry_spec hP windows i (by simp [windows]; omega)

/-! ### Doublings -/

/-- **One doubling window:** `doublingsValue` gives `P, 2P, 4P, 8P` (extended coordinates) and
the next base `16P`. -/
theorem doublings_spec {b : Value} {P : Curve} (hb : Affine b P) :
    (doublingsValue b).1.length = 4 ∧
      (∀ j < 4, ExtRep ((doublingsValue b).1.getD j neutralValue) (2 ^ j • P)) ∧
      Affine (doublingsValue b).2 (16 • P) := by
  have e1 := extRep_ofAffineValue hb
  have e2 := extRep_extAddValue e1 e1
  have e4 := extRep_extAddValue e2 e2
  have e8 := extRep_extAddValue e4 e4
  have e16 := affine_toAffineValue (extRep_extAddValue e8 e8)
  have d2 : P + P = 2 ^ 1 • P := by rw [pow_one, two_nsmul]
  have d4 : 2 ^ 1 • P + 2 ^ 1 • P = 2 ^ 2 • P := by rw [← add_nsmul]; norm_num
  have d8 : 2 ^ 2 • P + 2 ^ 2 • P = 2 ^ 3 • P := by rw [← add_nsmul]; norm_num
  have d16 : 2 ^ 3 • P + 2 ^ 3 • P = 16 • P := by rw [← add_nsmul]; norm_num
  rw [d2] at e2
  rw [d2, d4] at e4
  rw [d2, d4, d8] at e8
  rw [d2, d4, d8, d16] at e16
  refine ⟨rfl, ?_, e16⟩
  intro j hj
  interval_cases j
  · rw [pow_zero, one_nsmul]; exact e1
  · exact e2
  · exact e4
  · exact e8

/-- **The doubling table:** entry `i` of `chain doublingsValue r n` is `2^i·P` (`i < 4n`). -/
theorem doublingsChain_spec {r : Value} {P : Curve} (hr : Affine r P) (n : ℕ) :
    (chain doublingsValue r n).length = 4 * n ∧
      ∀ i < 4 * n, ExtRep ((chain doublingsValue r n).getD i neutralValue) (2 ^ i • P) := by
  obtain ⟨hl, he⟩ := chain_spec ExtRep doublingsValue 4 16 (fun j => 2 ^ j) neutralValue
    (fun r P hr => doublings_spec hr) n r P hr
  refine ⟨hl, fun i hi => ?_⟩
  have h := he (i / 4) (by omega) (i % 4) (Nat.mod_lt _ (by norm_num))
  have e1 : 4 * (i / 4) + i % 4 = i := Nat.div_add_mod i 4
  have e2 : 2 ^ (i % 4) * 16 ^ (i / 4) = 2 ^ i := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [e1, e2] at h
  exact h

/-- **`bitTable`'s entry `i` is `2^i·P`** once every link holds (`P` the curve point at inputs
0, 1; `i < 256`). -/
theorem bitTable_entry (input : ℕ → F) {P : Curve} (hP : Affine (input 0, input 1) P)
    (h : LinkedFrom (evalPoint input) doublings (inputPoint 0)
      ((List.range (windows - 1)).map (fun i => hinted (2 + 4 * i))))
    (i : ℕ) (hi : i < 256) :
    ExtRep (((entries doublings (bitTableBases ())).map (evalExt input)).getD i neutralValue)
      (2 ^ i • P) := by
  rw [bitTable_sound input h]
  exact (doublingsChain_spec hP windows).2 i (by simp [windows]; omega)

end Windows

/-! ### Signed base-16 recoding (the C++ `step`) -/

section Recoding

/-- The signed base-16 recoding of `edwards_points.h` (`step`, `step_inputs`): from carry `c`,
the nibbles of `n` (least significant first) for `k` windows; returns the digits and the final
carry. Per window: `digit = nibble + carry; carry = digit > 8; digit -= 16·carry`. -/
def recode : ℕ → ℕ → ℕ → List ℤ × ℕ
  | c, _, 0 => ([], c)
  | c, n, k + 1 =>
    ((((n % 16 + c : ℕ) : ℤ) - 16 * ((if 8 < n % 16 + c then 1 else 0 : ℕ) : ℤ)) ::
        (recode (if 8 < n % 16 + c then 1 else 0) (n / 16) k).1,
      (recode (if 8 < n % 16 + c then 1 else 0) (n / 16) k).2)

/-- The value of base-16 digits, least significant first. -/
def digitsValue : List ℤ → ℤ
  | [] => 0
  | d :: rest => d + 16 * digitsValue rest

theorem recode_length (c n k : ℕ) : (recode c n k).1.length = k := by
  induction k generalizing c n with
  | zero => rfl
  | succ k ih => simp [recode, ih]

/-- **The digits encode the number:** `Σ dᵢ·16^i + 16^k·carry = (n mod 16^k) + c`. -/
theorem recode_value (c n k : ℕ) :
    digitsValue (recode c n k).1 + 16 ^ k * ((recode c n k).2 : ℤ) = ((n % 16 ^ k : ℕ) : ℤ) + c := by
  induction k generalizing c n with
  | zero => simp [recode, digitsValue, Nat.mod_one]
  | succ k ih =>
    have h := ih (if 8 < n % 16 + c then 1 else 0) (n / 16)
    have hm : n % 16 ^ (k + 1) = n % 16 + 16 * (n / 16 % 16 ^ k) := by
      rw [pow_succ', Nat.mod_mul]
    simp only [recode, digitsValue]
    rw [hm]
    push_cast at h ⊢
    linear_combination 16 * h

/-- **Digits lie in `−8 … 8`** (in fact `−7 … 8`), and the carry is `0` or `1`, for a carry-in
`c ≤ 1`. -/
theorem recode_bound (c n k : ℕ) (hc : c ≤ 1) :
    (∀ d ∈ (recode c n k).1, -8 ≤ d ∧ d ≤ 8) ∧ (recode c n k).2 ≤ 1 := by
  induction k generalizing c n with
  | zero => simpa [recode] using hc
  | succ k ih =>
    have hc' : (if 8 < n % 16 + c then 1 else 0) ≤ 1 := by split_ifs <;> norm_num
    obtain ⟨h1, h2⟩ := ih (if 8 < n % 16 + c then 1 else 0) (n / 16) hc'
    refine ⟨?_, h2⟩
    intro d hd
    simp only [recode, List.mem_cons] at hd
    rcases hd with rfl | hd
    · have h16 : n % 16 < 16 := Nat.mod_lt _ (by norm_num)
      split_ifs with h <;> push_cast <;> omega
    · exact h1 d hd

/-- **No final carry** when `n < 8·16^k` and `k + 1` windows are used (carry-in `≤ 1`). -/
theorem recode_carry_zero (c n k : ℕ) (hc : c ≤ 1) (hn : n < 8 * 16 ^ k) :
    (recode c n (k + 1)).2 = 0 := by
  induction k generalizing c n with
  | zero =>
    simp only [recode]
    have : ¬ 8 < n % 16 + c := by omega
    simp [this]
  | succ k ih =>
    show (recode (if 8 < n % 16 + c then 1 else 0) (n / 16) (k + 1)).2 = 0
    apply ih
    · split_ifs <;> norm_num
    · rw [pow_succ] at hn
      omega

/-- **64 windows, an offset below `2²⁵²`:** the digits encode exactly `n`, no carry is left, and
each digit is in `−8 … 8` (the C++ check `need(!carry, "offset recoding")` never fails). -/
theorem recode64_value (n : ℕ) (hn : n < 2 ^ 252) :
    digitsValue (recode 0 n 64).1 = n ∧ (recode 0 n 64).2 = 0 ∧
      (recode 0 n 64).1.length = 64 ∧ ∀ d ∈ (recode 0 n 64).1, -8 ≤ d ∧ d ≤ 8 := by
  have hz : (recode 0 n 64).2 = 0 :=
    recode_carry_zero 0 n 63 (by norm_num) (by
      calc n < 2 ^ 252 := hn
        _ ≤ 8 * 16 ^ 63 := by norm_num)
  have hv := recode_value 0 n 64
  rw [hz, Nat.mod_eq_of_lt (by calc n < 2 ^ 252 := hn
    _ ≤ 16 ^ 64 := by norm_num)] at hv
  refine ⟨by simpa using hv, hz, recode_length 0 n 64, (recode_bound 0 n 64 (by norm_num)).1⟩

/-- The digits' value as a sum over window indices. -/
theorem digitsValue_eq_sum (l : List ℤ) :
    digitsValue l = ((List.range l.length).map (fun w => l.getD w 0 * 16 ^ w)).sum := by
  induction l with
  | nil => rfl
  | cons d rest ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
    simp only [digitsValue, List.getD_cons_zero, pow_zero, mul_one, Function.comp_def,
      Nat.succ_eq_add_one, List.getD_cons_succ, pow_succ]
    rw [ih, ← List.sum_map_mul_left]
    congr 2
    apply List.map_congr_left
    intro w _
    ring

/-- **Signed multiples sum to the multiple by the sum** (any commutative group). -/
theorem sum_map_zsmul {G : Type*} [AddCommGroup G] (P : G) (g : ℕ → ℤ) (L : List ℕ) :
    (L.map (fun w => g w • P)).sum = (L.map g).sum • P := by
  induction L with
  | nil => simp
  | cons a rest ih => simp [ih, add_zsmul]

/-- **A signed table entry is the signed multiple:** if `(x, y)` is `|d|·Q` and the sign input is
`−1` for `d < 0`, `1` otherwise (the C++ rule; `d = 0` uses the neutral entry `(0, 1)`), then
`(s·x, y)` is `d·Q`. -/
theorem signed_entry {x y s : F} {Q : Curve} {d : ℤ} (h : Affine (x, y) (d.natAbs • Q))
    (hs : toZMod s = if d < 0 then -1 else 1) : Affine (s * x, y) (d • Q) := by
  obtain ⟨hx, hy⟩ := h
  by_cases hd : d < 0
  · rw [if_pos hd] at hs
    have e : d • Q = -(d.natAbs • Q) := by
      rw [← natCast_zsmul, ← neg_zsmul]
      congr 1
      omega
    rw [e]
    refine ⟨?_, hy⟩
    show toZMod (s * x) = -(d.natAbs • Q).x
    rw [toZMod_mul, hs, ← hx]
    ring
  · rw [if_neg hd] at hs
    have e : d • Q = d.natAbs • Q := by
      rw [← natCast_zsmul]
      congr 1
      omega
    rw [e]
    refine ⟨?_, hy⟩
    show toZMod (s * x) = (d.natAbs • Q).x
    rw [toZMod_mul, hs, ← hx, one_mul]

open EdwardsAffine in
/-- **`EdwardsAffine.offsetSum` computes `u(I + n·P)`:** if inputs 0, 1 are the curve point `I`
and window `w`'s signed entry is `(dg w · 16^w)·P`, the output is the Montgomery coordinate of
`I + (Σ_w dg w·16^w)·P`. -/
theorem offsetSum_value (input : ℕ → F) {I P : Curve} (dg : ℕ → ℤ)
    (hI : Affine (input 0, input 1) I)
    (hw : ∀ w < windows, Affine (input (2 + 3 * w + 2) * input (2 + 3 * w), input (2 + 3 * w + 1))
      ((dg w * 16 ^ w) • P)) :
    ∃ o : F, offsetSum.map (FieldDag.Expr.eval input) = [o] ∧
      toZMod o = montU (I + ((List.range windows).map (fun w => dg w * 16 ^ w)).sum • P) := by
  rw [offsetSum_eval]
  refine ⟨_, rfl, ?_⟩
  let l : List (Value × Curve) := ((input 0, input 1), I) :: (List.range windows).map
    (fun w => ((input (2 + 3 * w + 2) * input (2 + 3 * w), input (2 + 3 * w + 1)),
      (dg w * 16 ^ w) • P))
  have hl : ∀ a ∈ l, Affine a.1 a.2 := by
    intro a ha
    simp only [l, List.mem_cons, List.mem_map, List.mem_range] at ha
    rcases ha with rfl | ⟨w, hw', rfl⟩
    · exact hI
    · exact hw w hw'
  have hs := affine_sumTreeValue l hl
  have e1 : l.map Prod.fst = (input 0, input 1) :: (List.range windows).map
      (fun w => (input (2 + 3 * w + 2) * input (2 + 3 * w), input (2 + 3 * w + 1))) := by
    simp only [l, List.map_cons, List.map_map]
    rfl
  have e2 : (l.map Prod.snd).sum =
      I + ((List.range windows).map (fun w => dg w * 16 ^ w)).sum • P := by
    simp only [l, List.map_cons, List.map_map, List.sum_cons]
    rw [← sum_map_zsmul]
    rfl
  rw [e1, e2] at hs
  generalize sumTreeValue _ = v at hs
  rw [montU, ← hs.2, toZMod_mul, toZMod_inverse, toZMod_add, toZMod_sub, toZMod_ofNat_one,
    div_eq_mul_inv]

open EdwardsAffine in
/-- **`offsetSum` with the C++ recoding:** for an offset `n < 2²⁵²`, digits `recode 0 n 64`, and
window inputs as `step_inputs` builds them (the table entry for `|d|`, i.e. `(|d|·16^w)·P`, and
the sign `−1` for a negative digit), the output is the Montgomery coordinate of `I + n·P`. -/
theorem offsetSum_recoded (input : ℕ → F) {I P : Curve} (n : ℕ) (hn : n < 2 ^ 252)
    (hI : Affine (input 0, input 1) I)
    (hw : ∀ w < windows,
      Affine (input (2 + 3 * w), input (2 + 3 * w + 1))
        ((((recode 0 n 64).1.getD w 0).natAbs * 16 ^ w) • P) ∧
      toZMod (input (2 + 3 * w + 2)) = if (recode 0 n 64).1.getD w 0 < 0 then -1 else 1) :
    ∃ o : F, offsetSum.map (FieldDag.Expr.eval input) = [o] ∧ toZMod o = montU (I + n • P) := by
  obtain ⟨hv, -, hlen, -⟩ := recode64_value n hn
  obtain ⟨o, ho, hu⟩ := offsetSum_value input (fun w => (recode 0 n 64).1.getD w 0) hI (by
    intro w hwl
    obtain ⟨ha, hs⟩ := hw w hwl
    have e : ((recode 0 n 64).1.getD w 0 * 16 ^ w) • P =
        (recode 0 n 64).1.getD w 0 • ((16 ^ w : ℕ) • P) := by
      rw [← natCast_zsmul, smul_smul]
      push_cast
      rfl
    rw [e]
    refine signed_entry ?_ hs
    rw [smul_smul]
    exact ha)
  refine ⟨o, ho, ?_⟩
  rw [hu]
  congr 2
  have h := digitsValue_eq_sum (recode 0 n 64).1
  rw [hlen, hv] at h
  rw [← natCast_zsmul, h]
  rfl

end Recoding

/-! ### XEdDSA `doubleScalar` -/

section DoubleScalar
open Signal.XEdDsaField

/-- The four coordinates of an XEdDSA point, in `ZMod p`. -/
def tupX (p : Signal.XEdDsaField.Point F) : K × K × K × K :=
  (toZMod p.x, toZMod p.y, toZMod p.z, toZMod p.t)

/-- The XEdDSA extended point `p` represents the curve point `P`. -/
def XRep (p : Signal.XEdDsaField.Point F) (P : Curve) : Prop := Rep4 (tupX p) P

theorem toZMod_twoD : toZMod (ofNat ((2 * d) % FieldDag.modulus)) = 2 * dK := by
  rw [toZMod_ofNat, ZMod.natCast_mod, Nat.cast_mul, dK_eq_natCast, dNat_eq, Nat.cast_ofNat]

theorem tupX_add (p q : Signal.XEdDsaField.Point F) :
    tupX (add X25519.concrete p q) = Edwards.extAdd 1 (-dK) (tupX p) (tupX q) := by
  simp only [tupX, Signal.XEdDsaField.add, concrete_add, concrete_sub, concrete_mul, concrete_const,
    toZMod_mul, toZMod_add, toZMod_sub, toZMod_twoD]
  simp only [Edwards.extAdd, toZMod_ofNat, Nat.cast_ofNat, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- **`XEdDsaField.add` is the group law** (the unscaled extended addition, `k = 2d`). -/
theorem xrep_add {p q : Signal.XEdDsaField.Point F} {P Q : Curve} (hp : XRep p P) (hq : XRep q Q) :
    XRep (add X25519.concrete p q) (P + Q) := by
  unfold XRep
  rw [tupX_add]
  exact rep4_add one_ne_zero (by ring) hp hq

theorem xrep_identity : XRep (identity X25519.concrete) (0 : Curve) := by
  unfold XRep tupX Signal.XEdDsaField.identity
  simp only [concrete_const, toZMod_ofNat_zero, toZMod_ofNat_one]
  exact rep4_zero

theorem xrep_affine {x y : F} {P : Curve} (h : Affine (x, y) P) :
    XRep (affine X25519.concrete x y) P := by
  obtain ⟨hx, hy⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [tupX, Signal.XEdDsaField.affine, concrete_mul, concrete_const, toZMod_mul,
      toZMod_ofNat_one, hx, hy]

theorem xrep_base : XRep (base X25519.concrete) B :=
  xrep_affine (x := ofNat baseX) (y := ofNat baseY) ⟨toZMod_ofNat _, toZMod_ofNat _⟩

theorem choose_bit (b : Bool) (yes no : Signal.XEdDsaField.Point F) :
    choose X25519.concrete (X25519.bitValue b) yes no = if b then yes else no := by
  cases b <;> simp [Signal.XEdDsaField.choose, X25519.select_value]

/-- **`mulBits` is double-and-add:** from a representative of `n·P` and Boolean bits it ends at a
representative of `(big-endian value of the bits appended to n)·P`. -/
theorem xrep_mulBits {p : Signal.XEdDsaField.Point F} {P : Curve} (hp : XRep p P) :
    ∀ (bits : List Bool) (acc : Signal.XEdDsaField.Point F) (n : ℕ), XRep acc (n • P) →
      XRep (mulBits X25519.concrete p acc (bits.map X25519.bitValue)) (bitsValue n bits • P)
  | [], _, _, h => h
  | b :: rest, acc, n, h => by
    show XRep (mulBits X25519.concrete p (choose X25519.concrete (X25519.bitValue b)
      (add X25519.concrete (add X25519.concrete acc acc) p) (add X25519.concrete acc acc))
      (rest.map X25519.bitValue)) (bitsValue (2 * n + b.toNat) rest • P)
    apply xrep_mulBits hp rest
    rw [choose_bit]
    have hd := xrep_add h h
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, add_zero]
      rw [two_mul, add_nsmul]
      exact hd
    · simp only [↓reduceIte, Bool.toNat_true]
      rw [two_mul, add_nsmul, add_nsmul, one_nsmul]
      exact xrep_add hd hp

theorem xrep_mul {p : Signal.XEdDsaField.Point F} {P : Curve} (hp : XRep p P) (bits : List Bool) :
    XRep (mul X25519.concrete p (bits.map X25519.bitValue)) (bitsValue 0 bits • P) :=
  xrep_mulBits hp bits _ 0 (by rw [zero_nsmul]; exact xrep_identity)

theorem normalize_spec {p : Signal.XEdDsaField.Point F} {P : Curve} (hp : XRep p P) :
    ∃ v : EdwardsAffine.Value, normalize X25519.concrete p = [v.1, v.2] ∧ Affine v P := by
  refine ⟨(p.x * FieldDag.inverse p.z, p.y * FieldDag.inverse p.z), ?_, ?_⟩
  · simp only [Signal.XEdDsaField.normalize, x25519_inverse_eq, concrete_mul]
  · exact affine_toAffineValue (e := ⟨p.x, p.y, p.z, p.t⟩) hp

/-- **`XEdDsaField.doubleScalar` computes `[s]B − [h]A`:** for `A = (x, y)` a curve point and
Boolean bit lists `h`, `s` (big-endian), the output is the affine point
`(value of s)·B − (value of h)·A`. -/
theorem doubleScalar_spec {x y : F} {A : Curve} (hA : Affine (x, y) A) (h s : List Bool) :
    ∃ v : EdwardsAffine.Value,
      doubleScalar X25519.concrete x y (h.map X25519.bitValue) (s.map X25519.bitValue) = [v.1, v.2] ∧
        Affine v (bitsValue 0 s • B - bitsValue 0 h • A) := by
  have hnA : XRep (affine X25519.concrete (X25519.concrete.sub (X25519.concrete.const 0) x) y) (-A) :=
    xrep_affine (by
      refine ⟨?_, hA.2⟩
      show toZMod (ofNat 0 - x) = -A.x
      rw [toZMod_sub, toZMod_ofNat_zero, zero_sub, hA.1])
  have hsum := xrep_add (xrep_mul hnA h) (xrep_mul xrep_base s)
  rw [smul_neg, neg_add_eq_sub] at hsum
  exact normalize_spec hsum

/-- **The `xeddsa` field program (`run concrete false`) computes `s·B − h·A`** when its bit inputs
are the bits of `h < 2²⁵⁶` (inputs 2 … 257, bit `i` at `2 + i`) and of `s < 2²⁵³` (inputs
258 … 510) and inputs 0, 1 are the curve point `A`. -/
theorem run_doubleScalar_spec (input : ℕ → F) {A : Curve} (hA : Affine (input 0, input 1) A)
    (hh sc : ℕ) (hlt : hh < 2 ^ 256) (slt : sc < 2 ^ 253)
    (hbits : ∀ i < 256, input (2 + i) = X25519.bitValue (hh.testBit i))
    (sbits : ∀ i < 253, input (258 + i) = X25519.bitValue (sc.testBit i)) :
    ∃ v : EdwardsAffine.Value, run X25519.concrete false input = [v.1, v.2] ∧
      Affine v (sc • B - hh • A) := by
  have e1 : (List.range 256).reverse.map (fun i => input (2 + i)) =
      ((List.range 256).reverse.map hh.testBit).map X25519.bitValue := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact hbits i (List.mem_range.mp (List.mem_reverse.mp hi))
  have e2 : (List.range 253).reverse.map (fun i => input (258 + i)) =
      ((List.range 253).reverse.map sc.testBit).map X25519.bitValue := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact sbits i (List.mem_range.mp (List.mem_reverse.mp hi))
  have hv1 : bitsValue 0 ((List.range 256).reverse.map hh.testBit) = hh := by
    rw [bitsValue_testBits, Nat.mod_eq_of_lt hlt]
  have hv2 : bitsValue 0 ((List.range 253).reverse.map sc.testBit) = sc := by
    rw [bitsValue_testBits, Nat.mod_eq_of_lt slt]
  obtain ⟨v, hv, ha⟩ := doubleScalar_spec hA ((List.range 256).reverse.map hh.testBit)
    ((List.range 253).reverse.map sc.testBit)
  rw [hv1, hv2] at ha
  refine ⟨v, ?_, ha⟩
  simp only [run, Bool.false_eq_true, ↓reduceIte, e1, e2]
  exact hv

end DoubleScalar

end TlsMpcProofs.Ed25519
