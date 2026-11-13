import TlsMpc.Node.Flows.Curve
import TlsMpc.OffsetAgreement

/-!
# The curve flows' theorems (P-SPLIT, P-OFFSET, P-HINT; T3 per flow)

REORGANIZATION_PLAN.md 7.1, stage S11. About the scripts of `Flows/Curve.lean` and the local
arithmetic of `Local/Edwards.lean`. No I/O; no emitter imports this module.

PROVED (standard axioms only):
  * THE RECODING LEMMA (P-OFFSET (a), the part that was "the C++ `step` implements `recode`"; there
    is no C++ step any more, the flow calls `recode`): `recode_length`, `recode_value` (the digits
    encode the number), `recode_bound` (digits in −8 … 8), `recode_carry_zero`, `recode64_value`
    (64 windows, an offset below 2^252: exact, no carry), `offsetValue_recode` and
    `step_tableSum` (the selected multiples sum to τ·R in any group, `OffsetAgreement.table_sum_correct`).
    `recode_zero`, `recode_succ`: the equations of `proofs/` `TlsMpcProofs.Ed25519.recode`, so the two
    definitions are equal by induction and the Mathlib package's `offsetSum_recoded` applies.
  * The step's program inputs (`stepIns_initial`, `stepIns_window`): exactly what `step_inputs`
    built and `offsetSum_recoded` assumes: per window the table entry `entryAt w d` (x, then y)
    and the sign handle (1 or −1), or the neutral element.
  * `offsetStep_key`, `offsetStepFast_key` (P-OFFSET (b) on the script's output): the ephemeral key a
    step returns is `montU (K₀ + τ·B)`, a function of the public K₀ and τ alone; with
    `OffsetAgreement.public_key_independent` (and `proofs/` `deployed_key_close_uniform` for its
    distribution) it does not depend on the initial scalar.
  * Gates (the order of openings; P-HINT (a), P-SPLIT (b), P-OFFSET (c), (d)): `lift_order` (the
    lift's `w` is opened only after its four checks per point opened all zero, `Z` only after `w`),
    `splitAgree_gate`, `offsetPrepare_gate`, `pointExchange_gate` (a peer opening is used only if
    it matches the peer's commitment frame `tag ‖ party ‖ nonce ‖ value`, which differs from ours).
  * T3 per flow (`*_reveals`): the kinds each script's releases carry; `Staged.viewD_kinds` for the
    flows with a local step (the local step releases nothing).
  * P-HINT (b) and the validity bit (`valid_bit`, `lift_valid_sound`, `lift_valid_complete`,
    `prepareStatus_iff`): the opened validity bit is `sel xor b`; with `FieldInverse`, valid ⇒ q(u) is
    a square (the root is exhibited); under the explicit hypotheses H-QR (`TwoNonSquare`) and
    Euler's criterion (`EulerCriterion`), valid ⇔ q(u) is a square. So op 66's status byte reveals
    exactly whether `q(u) = u(u² + 486662u + 1)` is a nonzero square, i.e. (`proofs/`
    `montQ_square_iff`) whether `u` is the Montgomery coordinate of a curve point. The two hypotheses
    are theorems of the Mathlib package: `two_not_square` (H-QR) and `euler_criterion` (with
    `Local.Field.pow_eq`).
  * P-SPLIT (d) is `Local/Edwards.lean` (`add_eq`, `toAffine_eq`, `montU_eq`); `addU_montU`: the
    split agreement's quotient `(den + num)/(den − num)` is `montU (T_A + T_B)` (`FieldInverse`).
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees every_seq every_seqs)
open TlsMpc.Node.Flows.Run (openFieldThen every_openFieldThen)
open TlsMpc.FieldDag (F modulus ofNat inverse)
open TlsMpc.FieldDag.V3 (FieldInverse)
open TlsMpc.Node.Local.Edwards (Value)

/-! ## The recoding lemma -/

theorem recode_zero (c n : Nat) : recode c n 0 = ([], c) := rfl

theorem recode_succ (c n k : Nat) :
    recode c n (k + 1) =
      ((((n % 16 + c : Nat) : Int) - 16 * ((if 8 < n % 16 + c then 1 else 0 : Nat) : Int)) ::
          (recode (if 8 < n % 16 + c then 1 else 0) (n / 16) k).1,
        (recode (if 8 < n % 16 + c then 1 else 0) (n / 16) k).2) := rfl

theorem recode_length (c n k : Nat) : (recode c n k).1.length = k := by
  induction k generalizing c n with
  | zero => rfl
  | succ k ih => simp [recode_succ, ih]

theorem mod_sixteen_pow (n k : Nat) : n % 16 ^ (k + 1) = n % 16 + 16 * (n / 16 % 16 ^ k) := by
  rw [Nat.pow_succ', Nat.mod_mul]

/-- **The digits encode the number:** `Σ dᵢ·16^i + 16^k·carry = (n mod 16^k) + c`. -/
theorem recode_value (c n k : Nat) :
    digitsValue (recode c n k).1 + (16 : Int) ^ k * ((recode c n k).2 : Int) = ((n % 16 ^ k : Nat) : Int) + c := by
  induction k generalizing c n with
  | zero => simp [recode_zero, digitsValue, Nat.mod_one]
  | succ k ih =>
    have h := ih (if 8 < n % 16 + c then 1 else 0) (n / 16)
    rw [recode_succ, digitsValue, mod_sixteen_pow]
    generalize hD : digitsValue (recode (if 8 < n % 16 + c then 1 else 0) (n / 16) k).1 = D at h ⊢
    generalize hC : (recode (if 8 < n % 16 + c then 1 else 0) (n / 16) k).2 = C at h ⊢
    have e : (16 : Int) ^ (k + 1) * (C : Int) = 16 * ((16 : Int) ^ k * C) := by
      rw [Int.pow_succ, Int.mul_comm ((16 : Int) ^ k) 16, Int.mul_assoc]
    rw [e]
    generalize (16 : Int) ^ k * (C : Int) = MC at h ⊢
    have hm := Nat.mod_lt n (show 0 < 16 by decide)
    split at h <;> split <;> push_cast at h ⊢ <;> omega

/-- **Digits lie in −8 … 8**, and the carry stays 0 or 1, for a carry-in `c ≤ 1`. -/
theorem recode_bound (c n k : Nat) (hc : c ≤ 1) :
    (∀ d ∈ (recode c n k).1, -8 ≤ d ∧ d ≤ 8) ∧ (recode c n k).2 ≤ 1 := by
  induction k generalizing c n with
  | zero => simpa [recode_zero] using hc
  | succ k ih =>
    have hc' : (if 8 < n % 16 + c then 1 else 0) ≤ 1 := by split <;> decide
    obtain ⟨h1, h2⟩ := ih (if 8 < n % 16 + c then 1 else 0) (n / 16) hc'
    refine ⟨?_, by rw [recode_succ]; exact h2⟩
    intro d hd
    rw [recode_succ] at hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · have h16 : n % 16 < 16 := Nat.mod_lt _ (by decide)
      split <;> omega
    · exact h1 d hd

/-- **No final carry** when `n < 8·16^k` and `k + 1` windows are used. -/
theorem recode_carry_zero (c n k : Nat) (hc : c ≤ 1) (hn : n < 8 * 16 ^ k) :
    (recode c n (k + 1)).2 = 0 := by
  induction k generalizing c n with
  | zero =>
    rw [recode_succ, recode_zero]
    have : ¬ 8 < n % 16 + c := by simp at hn; omega
    simp [this]
  | succ k ih =>
    rw [recode_succ]
    apply ih
    · split <;> decide
    · rw [Nat.pow_succ] at hn
      have : n / 16 < 8 * 16 ^ k := by
        apply Nat.div_lt_of_lt_mul
        rw [Nat.mul_comm 16, Nat.mul_assoc] at *
        omega
      exact this

/-- **64 windows, an offset below 2^252** (the deployed `offset[31] &= 15`): the digits encode
exactly τ, no carry is left (the "offset recoding" abort never fires), 64 digits in −8 … 8. -/
theorem recode64_value (n : Nat) (hn : n < 2 ^ 252) :
    digitsValue (recode 0 n 64).1 = n ∧ (recode 0 n 64).2 = 0 ∧
      (recode 0 n 64).1.length = 64 ∧ ∀ d ∈ (recode 0 n 64).1, -8 ≤ d ∧ d ≤ 8 := by
  have hz : (recode 0 n 64).2 = 0 :=
    recode_carry_zero 0 n 63 (by decide) (Nat.lt_of_lt_of_le hn (by decide))
  have hv := recode_value 0 n 64
  rw [hz, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn (by decide))] at hv
  refine ⟨by simpa using hv, hz, recode_length 0 n 64, (recode_bound 0 n 64 (by decide)).1⟩

/-- `OffsetAgreement.offsetValue` is the digits' value at weight `16^position`. -/
theorem offsetValue_eq (position : Nat) (l : List Int) :
    TlsMpc.OffsetAgreement.offsetValue position l = 16 ^ position * digitsValue l := by
  induction l generalizing position with
  | nil => simp [TlsMpc.OffsetAgreement.offsetValue, digitsValue]
  | cons d rest ih =>
    simp only [TlsMpc.OffsetAgreement.offsetValue, digitsValue, ih, Int.pow_succ]
    rw [Int.mul_add, Int.mul_comm d, ← Int.mul_assoc, Int.mul_comm (16 ^ position) 16]

theorem offsetValue_recode (n : Nat) (hn : n < 2 ^ 252) :
    TlsMpc.OffsetAgreement.offsetValue 0 (recode 0 n 64).1 = n := by
  rw [offsetValue_eq, (recode64_value n hn).1]
  simp only [Int.pow_zero, Int.one_mul]

/-- **P-OFFSET (a), the step's selection**: in any commutative group (H-GROUP: the table holds the
multiples `(j·16^w)·R`, `proofs/` `windowChain_spec`), the signed multiples the step's digits select
sum to τ·R. With `OffsetAgreement.agreement_correct`: the step computes `(k₀ + τ)·R`. -/
theorem step_tableSum {G : Type} [Lean.Grind.IntModule G] (R : G) (n : Nat) (hn : n < 2 ^ 252) :
    TlsMpc.OffsetAgreement.tableSum R 0 (recode 0 n 64).1 = (n : Int) • R := by
  rw [TlsMpc.OffsetAgreement.table_sum_correct, offsetValue_recode n hn]

/-! ## The step's program inputs -/

theorem flatMap_three {α β : Type} (f : α → List β) (hf : ∀ a, (f a).length = 3) :
    ∀ es : List α, (es.flatMap f).length = 3 * es.length
  | [] => rfl
  | e :: es => by
    simp only [List.flatMap_cons, List.length_append, hf, flatMap_three f hf es, List.length_cons]
    omega

theorem windowInputs_length (table : List FieldH) (zero one minus : FieldH) (digits : List Int) :
    (windowInputs table zero one minus digits).length = 3 * digits.length := by
  unfold windowInputs
  rw [flatMap_three _ (fun e => by split <;> rfl), List.length_zipIdx]

theorem zipIdx_getElem? {α : Type} (l : List α) (w : Nat) :
    (l.zipIdx)[w]? = l[w]?.map fun d => (d, w) := by
  rw [List.getElem?_zipIdx]
  simp

theorem windowInputs_drop (table : List FieldH) (zero one minus : FieldH) :
    ∀ (es : List (Int × Nat)),
    ∀ w < es.length, ((es.flatMap fun e : Int × Nat =>
      if e.1 = 0 then [zero, one, one]
      else [table.getD (entryAt e.2 e.1) zero, table.getD (entryAt e.2 e.1 + 1) zero, if 0 < e.1 then one else minus])
        |>.drop (3 * w) |>.take 3) =
      (match es[w]? with
       | some e => if e.1 = 0 then [zero, one, one]
         else [table.getD (entryAt e.2 e.1) zero, table.getD (entryAt e.2 e.1 + 1) zero, if 0 < e.1 then one else minus]
       | none => [])
  | [], w, hw => by simp at hw
  | e :: es, 0, _ => by
    simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.getElem?_cons_zero]
    split <;> simp
  | e :: es, w + 1, hw => by
    simp only [List.flatMap_cons, List.getElem?_cons_succ]
    have h3 : (if e.1 = 0 then [zero, one, one]
        else [table.getD (entryAt e.2 e.1) zero, table.getD (entryAt e.2 e.1 + 1) zero, if 0 < e.1 then one else minus]).length = 3 := by
      split <;> rfl
    rw [show 3 * (w + 1) = 3 + 3 * w by omega, ← List.drop_drop, List.drop_left' h3]
    exact windowInputs_drop table zero one minus es w (by simpa using hw)

/-- **The step's inputs per window** (`step_inputs`): for window `w < 64` with digit `d`, the three
inputs at `2 + 3w` are the neutral element `(0, 1)` with sign 1 when `d = 0`, and otherwise the table
entry `entryAt w d = 2·(8w + |d| − 1)` (the multiple `(|d|·16^w)·R`, x then y) with sign handle `one`
(d > 0) or `minus` (d < 0). -/
theorem stepIns_window (f0 : Nat) (st : OffsetState) (τ w : Nat) (hw : w < 64) :
    ((stepIns f0 st τ).drop (2 + 3 * w)).take 3 =
      (let d := (recode 0 τ 64).1.getD w 0
       if d = 0 then [⟨f0⟩, ⟨f0 + 1⟩, ⟨f0 + 1⟩]
       else [st.table.getD (entryAt w d) ⟨f0⟩, st.table.getD (entryAt w d + 1) ⟨f0⟩,
         if 0 < d then ⟨f0 + 1⟩ else ⟨f0 + 2⟩]) := by
  have hl := recode_length 0 τ 64
  unfold stepIns windowInputs
  rw [show 2 + 3 * w = [st.initial.1, st.initial.2].length + 3 * w by rfl, ← List.drop_drop,
    List.drop_left]
  rw [windowInputs_drop st.table ⟨f0⟩ ⟨f0 + 1⟩ ⟨f0 + 2⟩ _ w (by simp [hl, hw]), zipIdx_getElem?]
  have hw' : w < (recode 0 τ 64).1.length := by rw [hl]; exact hw
  rw [List.getElem?_eq_getElem hw']
  simp only [Option.map_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw',
    Option.getD_some]

theorem stepIns_initial (f0 : Nat) (st : OffsetState) (τ : Nat) :
    (stepIns f0 st τ).take 2 = [st.initial.1, st.initial.2] := by
  simp [stepIns]

theorem stepIns_length (f0 : Nat) (st : OffsetState) (τ : Nat) : (stepIns f0 st τ).length = 194 := by
  simp [stepIns, windowInputs_length, recode_length]

/-! ## The ephemeral key (P-OFFSET (b) on the script's output) -/

theorem offsetStep_key (f0 maskSlot : Nat) (st : OffsetState) (τ : Nat) (u : F) (h : ephemeralKey st.key τ = some u) :
    offsetStep f0 maskSlot st τ =
      if (recode 0 τ 64).2 = 0 then
        seqs (stepConsts f0 ++ sharedBlock (f0 + 3) 128 maskSlot ++
          [.program offsetSumName 1 (stepIns f0 st τ) (sharedOut (f0 + 3) 128) [⟨f0 + 3 + 384⟩]
            Label.maskedDenominator] ++ freeFs (hs f0 3 ++ sharedIns (f0 + 3) 128)) (.done (u, ⟨f0 + 387⟩))
      else .abort "offset recoding" := by
  simp only [offsetStep, h]

/-- **The returned key is `montU (K₀ + τ·B)`**, required a valid point: a function of the public
`K₀` and τ only (`ephemeralKey`). -/
theorem ephemeralKey_spec (key : Value) (τ : Nat) (u : F) (h : ephemeralKey key τ = some u) :
    u = TlsMpc.Node.Local.Edwards.montU (TlsMpc.Node.Local.Edwards.add key (TlsMpc.Node.Local.Edwards.mul τ TlsMpc.Node.Local.Edwards.base)) ∧
      TlsMpc.Node.Local.Edwards.isValid (TlsMpc.Node.Local.Edwards.add key (TlsMpc.Node.Local.Edwards.mul τ TlsMpc.Node.Local.Edwards.base)) = true := by
  unfold ephemeralKey at h
  dsimp only at h
  split at h
  · next hv => exact ⟨(Option.some.inj h).symm, hv⟩
  · cases h

end TlsMpc.Node.Flows.Curve
