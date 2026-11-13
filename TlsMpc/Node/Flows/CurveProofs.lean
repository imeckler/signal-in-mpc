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

/-! ## T3 per flow: the kinds each script releases under -/

open TlsMpc.Node (RevealKind)

/-- Every instruction of a block is not a release or carries a label of `ks`. -/
def LabelsOk (ks : List RevealKind) (is : List Instr) : Prop := ∀ i ∈ is, LabelIn ks i

theorem LabelsOk.append {ks : List RevealKind} {a b : List Instr} (h1 : LabelsOk ks a) (h2 : LabelsOk ks b) :
    LabelsOk ks (a ++ b) := fun i hi => by
  rcases List.mem_append.mp hi with h | h
  · exact h1 i h
  · exact h2 i h

theorem LabelsOk.cons {ks : List RevealKind} {i : Instr} {l : List Instr} (h : LabelIn ks i) (h2 : LabelsOk ks l) :
    LabelsOk ks (i :: l) := fun j hj => by
  rcases List.mem_cons.mp hj with rfl | hj
  · exact h
  · exact h2 j hj

theorem LabelsOk.nil {ks : List RevealKind} : LabelsOk ks [] := fun _ h => by cases h

theorem LabelsOk.none {ks : List RevealKind} {l : List Instr} (h : ∀ i ∈ l, i.label? = none) : LabelsOk ks l :=
  fun i hi => LabelIn.of_none (h i hi)

theorem shared_ok {ks : List RevealKind} (f k slot : Nat) : LabelsOk ks (sharedBlock f k slot) := by
  refine LabelsOk.none fun i hi => ?_
  simp only [sharedBlock, List.mem_cons, List.mem_map] at hi
  rcases hi with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem frees_ok {ks : List RevealKind} (l : List FieldH) : LabelsOk ks (freeFs l) := by
  refine LabelsOk.none fun i hi => ?_
  simp only [freeFs, List.mem_map] at hi
  obtain ⟨_, _, rfl⟩ := hi
  rfl

theorem publics_ok {ks : List RevealKind} (f : Nat) (vs : List F) : LabelsOk ks (publics f vs) := by
  refine LabelsOk.none fun i hi => ?_
  simp only [publics, List.mem_map] at hi
  obtain ⟨_, _, rfl⟩ := hi
  rfl

theorem kind_ok {ks : List RevealKind} {k : RevealKind} (hk : k ∈ ks) {i : Instr}
    (h : i.label? = some (Label.ofKind k)) : LabelIn ks i := LabelIn.of_mem hk h

theorem block_reveals {ks : List RevealKind} {α : Type} {s : Script α} {is : List Instr} (h : LabelsOk ks is)
    (hs : Reveals ks s) : Reveals ks (seqs is s) := every_seqs hs is h

theorem openField_reveals {ks : List RevealKind} {α : Type} {hs' : List FieldH} {k : RevealKind} (hk : k ∈ ks)
    {K : List F → Script α} (hK : ∀ v, Reveals ks (K v)) :
    Reveals ks (openFieldThen hs' (Label.ofKind k) K) :=
  every_openFieldThen (kind_ok hk rfl) hK

theorem quotientMany_reveals {ks : List RevealKind} (hk : RevealKind.maskedDenominator ∈ ks) (f slot : Nat)
    (pairs : List (FieldH × FieldH)) : Reveals ks (quotientMany f slot pairs) := by
  unfold quotientMany
  dsimp only
  split
  · exact Every.done _
  · refine block_reveals ((shared_ok _ _ _).append (LabelsOk.cons (kind_ok hk rfl) LabelsOk.nil))
      (openField_reveals hk fun fl => ?_)
    split
    · exact block_reveals ((frees_ok _).append (frees_ok _)) (Every.done _)
    · exact Every.abort _

theorem pointExchange_reveals {ks : List RevealKind} (h1 : RevealKind.commitment ∈ ks)
    (h2 : RevealKind.ownPublicPoint ∈ ks) (hash : Bytes → Bytes) (me : Party) (tag : Bytes) (nonce points count : Nat) :
    Reveals ks (pointExchange hash me tag nonce points count) := by
  unfold pointExchange
  simp only [Script.bind_eq, Script.pure_eq]
  refine Every.bind (Every.exchange (kind_ok h1 rfl)) fun p => ?_
  refine Every.bind (Every.exchange (kind_ok h2 rfl)) fun q => ?_
  refine Every.bind (Every.ensure _ _) fun _ => ?_
  repeat' split
  all_goals first | exact Every.done _ | exact Every.abort _

def splitKinds : List RevealKind := [.commitment, .ownPublicPoint, .curveChecks, .maskedDenominator]

theorem splitBegin_reveals (hash : Bytes → Bytes) (me : Party) (nonce share : Nat) :
    Reveals splitKinds (splitBegin hash me nonce share) := by
  unfold splitBegin
  refine Every.bind (pointExchange_reveals (by decide) (by decide) _ _ _ _ _ _) fun sums => ?_
  split
  · exact Every.done _
  · exact Every.abort _

theorem splitAgree_reveals (f0 tSlot maskSlot : Nat) : Reveals splitKinds (splitAgree f0 tSlot maskSlot) := by
  unfold splitAgree
  refine block_reveals (LabelsOk.cons (LabelIn.of_none rfl) (LabelsOk.cons (LabelIn.of_none rfl)
    (LabelsOk.cons (kind_ok (k := .curveChecks) (by decide) rfl) LabelsOk.nil)))
    (openField_reveals (k := .curveChecks) (by decide) fun z => ?_)
  split
  · refine block_reveals (LabelsOk.cons (kind_ok (k := .curveChecks) (by decide) rfl) (frees_ok _)) ?_
    exact Reveals.mono (Inversion.quotient_reveals _ _ _ _) (by decide)
  · exact Every.abort _

def agreeKinds : List RevealKind := [.curveChecks, .maskedDenominator]

theorem agree_reveals (f0 slot : Nat) (jobs : List (List FieldH × FieldH)) : Reveals agreeKinds (agree f0 slot jobs) := by
  unfold agree
  dsimp only
  split
  · exact Every.done _
  · split
    · exact block_reveals (LabelsOk.cons (LabelIn.of_none rfl) (LabelsOk.cons (kind_ok (k := .curveChecks) (by decide) rfl)
        (LabelsOk.cons (LabelIn.of_none rfl) LabelsOk.nil))) (quotientMany_reveals (by decide) _ _ _)
    · exact Every.abort _

def offsetKinds : List RevealKind := [.commitment, .ownPublicPoint, .curveChecks, .maskedDenominator]

theorem offsetPrepare_reveals (hash : Bytes → Bytes) (me : Party) (f0 : Nat) (s : OffsetSlots) (u : FieldH) :
    Reveals offsetKinds (offsetPrepare hash me f0 s u) := by
  unfold offsetPrepare prepBlock
  refine block_reveals (((shared_ok _ _ _).append (LabelsOk.cons (LabelIn.of_none rfl) (LabelsOk.cons (LabelIn.of_none rfl)
      LabelsOk.nil))).append ((shared_ok _ _ _).append (LabelsOk.cons (kind_ok (k := .maskedDenominator) (by decide) rfl)
      LabelsOk.nil))) (openField_reveals (k := .curveChecks) (by decide) fun z => ?_)
  split
  · refine block_reveals (frees_ok _) (Every.bind (pointExchange_reveals (by decide) (by decide) _ _ _ _ _ _) fun keys => ?_)
    split
    · exact Every.done _
    · exact Every.abort _
  · exact Every.abort _

theorem offsetStep_reveals (f0 maskSlot : Nat) (st : OffsetState) (τ : Nat) :
    Reveals offsetKinds (offsetStep f0 maskSlot st τ) := by
  unfold offsetStep
  split
  · exact Every.abort _
  · split
    · exact block_reveals ((((publics_ok _ _).append (shared_ok _ _ _)).append
        (LabelsOk.cons (kind_ok (k := .maskedDenominator) (by decide) rfl) LabelsOk.nil)).append (frees_ok _)) (Every.done _)
    · exact Every.abort _

theorem offsetStepFast_reveals (f0 slot : Nat) (st : OffsetState) (τ : Nat) :
    Reveals offsetKinds (offsetStepFast f0 slot st τ) := by
  unfold offsetStepFast
  split
  · exact Every.abort _
  · split
    · refine block_reveals (((publics_ok _ _).append (LabelsOk.cons (kind_ok (k := .curveChecks) (by decide) rfl)
        LabelsOk.nil)).append (frees_ok _)) (Every.bind (quotientMany_reveals (by decide) _ _ _) fun r => ?_)
      split
      · split
        · exact Every.abort _
        · exact Every.done _
      · exact Every.abort _
    · exact Every.abort _

def liftKinds : List RevealKind := [.curveChecks, .liftW, .liftZ, .maskedDenominator]

theorem liftBlock_ok (f0 : Nat) (s : LiftSlots) (us : List FieldH) : LabelsOk liftKinds (liftBlock f0 s us) :=
  (LabelsOk.cons (LabelIn.of_none rfl) (LabelsOk.cons (LabelIn.of_none rfl) LabelsOk.nil)).append
    ((shared_ok _ _ _).append (LabelsOk.cons (LabelIn.of_none rfl)
      (LabelsOk.cons (kind_ok (k := .curveChecks) (by decide) rfl) LabelsOk.nil)))

theorem pointBlock_ok (f0 : Nat) (s : LiftSlots) (us : List FieldH) (rs : List (F × F × Bool)) :
    LabelsOk liftKinds (pointBlock f0 s us rs) :=
  ((publics_ok _ _).append (shared_ok _ _ _)).append
    (LabelsOk.cons (kind_ok (k := .maskedDenominator) (by decide) rfl) LabelsOk.nil)

theorem liftFrees_ok (f0 n : Nat) : LabelsOk liftKinds (liftFrees f0 n) := frees_ok _

theorem lift_reveals (f0 : Nat) (s : LiftSlots) (us : List FieldH) : Reveals liftKinds (lift f0 s us) := by
  unfold lift
  split
  · exact Every.done _
  · refine block_reveals (liftBlock_ok _ _ _) (openField_reveals (k := .curveChecks) (by decide) fun z => ?_)
    unfold liftAfterChecks
    split
    · refine openField_reveals (k := .liftW) (by decide) fun ws => ?_
      unfold liftAfterW
      split
      · split
        · exact Every.abort _
        · refine block_reveals (pointBlock_ok _ _ _ _) (openField_reveals (k := .liftZ) (by decide) fun zv => ?_)
          unfold liftAfterZ
          split
          · exact block_reveals (liftFrees_ok _ _) (Every.done _)
          · exact Every.abort _
      · exact Every.abort _
    · exact Every.abort _

def tableKinds : List RevealKind := [.linkChecks, .maskedDenominator]

theorem tables_reveals (f0 : Nat) (s : TableSlots) (pts : List Lifted) : Reveals tableKinds (tables f0 s pts) := by
  unfold tables
  dsimp only
  split
  · exact Every.done _
  · refine block_reveals ((((LabelsOk.cons (LabelIn.of_none rfl) LabelsOk.nil).append (shared_ok _ _ _)).append
      (shared_ok _ _ _)).append (LabelsOk.cons (LabelIn.of_none rfl)
        (LabelsOk.cons (kind_ok (k := .maskedDenominator) (by decide) rfl) LabelsOk.nil)))
      (openField_reveals (k := .linkChecks) (by decide) fun z => ?_)
    split
    · exact block_reveals (frees_ok _) (Every.done _)
    · exact Every.abort _

theorem agreeHinted_reveals (f0 rho qslot : Nat) (jobs : List HintedJob) :
    Reveals agreeKinds (agreeHinted f0 rho qslot jobs) := by
  unfold agreeHinted
  dsimp only
  split
  · refine block_reveals (LabelsOk.cons (LabelIn.of_none rfl) LabelsOk.nil) ?_
    split
    · exact Every.done _
    · exact block_reveals (((shared_ok _ _ _).append (LabelsOk.cons (kind_ok (k := .curveChecks) (by decide) rfl)
        LabelsOk.nil)).append (frees_ok _)) (Every.bind (quotientMany_reveals (by decide) _ _ _) fun _ => Every.done _)
  · exact Every.abort _

theorem agreeAffine_reveals (f0 rho qslot : Nat) (jobs : List (List FieldH × List FieldH)) :
    Reveals agreeKinds (agreeAffine f0 rho qslot jobs) := by
  unfold agreeAffine
  dsimp only
  split
  · exact Every.done _
  · split
    · exact block_reveals ((((LabelsOk.cons (LabelIn.of_none rfl) LabelsOk.nil).append (shared_ok _ _ _)).append
        (LabelsOk.cons (kind_ok (k := .curveChecks) (by decide) rfl) LabelsOk.nil)).append (frees_ok _))
        (quotientMany_reveals (by decide) _ _ _)
    · exact Every.abort _

def signatureKinds : List RevealKind := [.maskedDenominator]

theorem signatures_reveals (f0 maskSlot : Nat) (baseT : List FieldH) (jobs : List (List FieldH × List FieldH)) :
    Reveals signatureKinds (signatures f0 maskSlot baseT jobs) := by
  unfold signatures
  dsimp only
  split
  · exact Every.done _
  · split
    · exact block_reveals (((shared_ok _ _ _).append (LabelsOk.cons (kind_ok (k := .maskedDenominator) (by decide) rfl)
        LabelsOk.nil)).append (frees_ok _)) (Every.done _)
    · exact Every.abort _

theorem torsion_reveals (f0 hintSlot rSlot maskSlot : Nat) (pts : List Lifted) :
    Reveals signatureKinds (torsion f0 hintSlot rSlot maskSlot pts) := by
  unfold torsion
  dsimp only
  split
  · exact Every.done _
  · exact block_reveals (((((LabelsOk.cons (LabelIn.of_none rfl) LabelsOk.nil).append (shared_ok _ _ _)).append
      (shared_ok _ _ _)).append (LabelsOk.cons (LabelIn.of_none rfl)
        (LabelsOk.cons (kind_ok (k := .maskedDenominator) (by decide) rfl) LabelsOk.nil))).append (frees_ok _)) (Every.done _)

theorem sharedBits_reveals (f0 slot : Nat) : Reveals Convert.bitsKinds (sharedBits f0 slot) :=
  Convert.bits_reveals f0 251 slot

def prepareKinds : List RevealKind :=
  [.curveChecks, .liftW, .liftZ, .maskedDenominator, .pointValid, .linkChecks, .commitment, .ownPublicPoint]

theorem prepareFirst_reveals (f0 : Nat) (s : LiftSlots) (us : List FieldH) :
    Reveals prepareKinds (prepareFirst f0 s us) := by
  unfold prepareFirst
  refine Every.bind (Reveals.mono (lift_reveals f0 s us) (by decide)) fun ls => ?_
  split
  · exact Every.done _
  · refine openField_reveals (k := .pointValid) (by decide) fun v => ?_
    split
    · exact Every.done _
    · exact Every.abort _

theorem prepareSecond_reveals (hash : Bytes → Bytes) (me : Party) (f0 : Nat) (s : PrepareSlots) (live : List Lifted) :
    Reveals prepareKinds (prepareSecond hash me f0 s live) := by
  unfold prepareSecond
  dsimp only
  split
  · exact Every.done _
  · refine block_reveals ((((LabelsOk.cons (LabelIn.of_none rfl) LabelsOk.nil).append (shared_ok _ _ _)).append
      (shared_ok _ _ _)).append (LabelsOk.cons (LabelIn.of_none rfl) (LabelsOk.cons (LabelIn.of_none rfl)
        (LabelsOk.cons (kind_ok (k := .maskedDenominator) (by decide) rfl) LabelsOk.nil))))
      (openField_reveals (k := .linkChecks) (by decide) fun z => ?_)
    split
    · refine block_reveals (frees_ok _) (Every.bind (pointExchange_reveals (by decide) (by decide) _ _ _ _ _ _) fun keys => ?_)
      split
      · exact Every.done _
      · exact Every.abort _
    · exact Every.abort _

theorem prepareContacts_second_reveals (hash : Bytes → Bytes) (me : Party) (f0 : Nat) (s : PrepareSlots)
    (us identityBits : List FieldH) (r : List Lifted × List Bool) :
    Reveals prepareKinds ((prepareContacts hash me f0 s us identityBits).second r) := by
  show Reveals prepareKinds ((prepareSecond hash me _ s _).bind _)
  refine Every.bind (prepareSecond_reveals _ _ _ _ _) fun sts => ?_
  exact Every.bind (Reveals.mono (agreeAffine_reveals _ _ _ _) (by decide)) fun _ => Every.done _

/-- **A staged flow releases only what its two scripts declare**: the local step releases nothing
(it only changes this party's store), so against any adversary every release the adversary
receives carries a label of `ks`. -/
theorem Staged.viewD_kinds (E : Env) (me : Party) (adv : Adversary) {α β : Type} (s : Staged α β)
    (ks : List RevealKind) (h1 : Reveals ks s.first) (h2 : ∀ a, Reveals ks (s.second a)) (σ : Store) (I : Ideal)
    (vD : List Release) : ∀ r ∈ (s.withAdv E me adv σ I vD).viewD, ∃ k ∈ ks, r.label = Label.ofKind k := by
  intro r hr
  unfold Staged.withAdv at hr
  dsimp only at hr
  split at hr
  · exact TlsMpc.Node.Engine.viewD_kinds E me adv ks s.first h1 σ I vD r hr
  · next a ha =>
    split at hr
    · exact TlsMpc.Node.Engine.viewD_kinds E me adv ks s.first h1 σ I vD r hr
    · next σ' hσ =>
      simp only [Outcome.then, List.mem_append] at hr
      rcases hr with hr | hr
      · exact TlsMpc.Node.Engine.viewD_kinds E me adv ks s.first h1 σ I vD r hr
      · exact TlsMpc.Node.Engine.viewD_kinds E me adv ks _ (h2 a) _ _ _ r hr

/-- **T3 for op 66**: every release of `prepareContacts`, against any adversary, carries one of the
kinds `prepareKinds`; the validity bits are released under `pointValid` only here. -/
theorem prepareContacts_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (hash : Bytes → Bytes) (f0 : Nat)
    (s : PrepareSlots) (us identityBits : List FieldH) (σ : Store) (I : Ideal) (vD : List Release) :
    ∀ r ∈ ((prepareContacts hash me f0 s us identityBits).withAdv E me adv σ I vD).viewD,
      ∃ k ∈ prepareKinds, r.label = Label.ofKind k :=
  Staged.viewD_kinds E me adv _ prepareKinds (prepareFirst_reveals _ _ _)
    (prepareContacts_second_reveals hash me f0 s us identityBits) σ I vD

/-! ## The order of openings (P-HINT (a), P-SPLIT (b), P-OFFSET (c), (d)) -/

/-- **P-HINT (a): the checks before `w`, `w` before `Z`.** For a nonempty lift, the script is the
input block (whose only release is the empty one of `lift-open`, which has no `D` row), then the
opening of the 4n checks; it aborts unless they are all zero, and only then opens the `w`s; after
the `w`s it computes the public roots and only then runs `lift-point` and opens the `Z`s. -/
theorem lift_order (f0 : Nat) (s : LiftSlots) (us : List FieldH) (hn : us.length ≠ 0) :
    lift f0 s us = seqs (liftBlock f0 s us) (openFieldThen (liftChecks f0 us.length) Label.curveChecks
      (liftAfterChecks f0 s us)) ∧
    (∀ z, ¬ (z.length = 4 * us.length ∧ allZero z = true) → ∃ r, liftAfterChecks f0 s us z = .abort r) ∧
    (∀ z, z.length = 4 * us.length ∧ allZero z = true →
      liftAfterChecks f0 s us z = openFieldThen (liftWs f0 us.length) Label.liftW (liftAfterW f0 s us)) ∧
    (∀ ws rs, ws.length = us.length → roots ws = some rs →
      liftAfterW f0 s us ws = seqs (pointBlock f0 s us rs)
        (openFieldThen (liftZs f0 us.length) Label.liftZ (liftAfterZ f0 us.length rs))) := by
  refine ⟨by unfold lift; rw [if_neg hn], fun z hz => ⟨_, if_neg hz⟩, fun z hz => if_pos hz,
    fun ws rs hl hr => ?_⟩
  unfold liftAfterW
  rw [if_pos hl, hr]

/-- The lift's input block releases nothing but `lift-open`'s (empty) openings: no `w`, no `Z`. -/
theorem liftBlock_labels (f0 : Nat) (s : LiftSlots) (us : List FieldH) :
    ∀ i ∈ liftBlock f0 s us, i.label? = none ∨ i.label? = some Label.curveChecks := by
  intro i hi
  unfold liftBlock at hi
  rcases List.mem_append.mp hi with h | h
  · rcases List.mem_append.mp h with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp [InstrP.label?]
    · left
      simp only [sharedBlock, List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp [InstrP.label?]

/-- **P-SPLIT (b), the gate**: the agreement is computed only after both parties' curve checks
opened to zero; the checks are `curveValue` of each party's input point (`edwards-on-curve`, two
copies), which is zero exactly on curve points (`Local.Edwards.onCurve`, `onCurve_iff`). -/
theorem splitAgree_gate (f0 tSlot maskSlot : Nat) :
    splitAgree f0 tSlot maskSlot =
      seqs (splitBlock f0 tSlot) (openFieldThen (hs (f0 + 4) 2) Label.curveChecks fun z =>
        if z.length = 2 ∧ allZero z = true then
          seqs (splitTail f0) (Inversion.quotientScript (f0 + 8) maskSlot ⟨f0 + 6⟩ ⟨f0 + 7⟩)
        else .abort "agreement share is not a curve point") := rfl

/-- **P-OFFSET (c), the gate**: the table and K₀ are used only after the program's 505 checks
(the masked curve check of the recipient and the 504 bit checks) opened to zero. -/
theorem offsetPrepare_gate (hash : Bytes → Bytes) (me : Party) (f0 : Nat) (s : OffsetSlots) (u : FieldH) :
    ∃ K, offsetPrepare hash me f0 s u =
      seqs (prepBlock f0 s u) (openFieldThen (hs (prepOuts f0) 505) Label.curveChecks K) ∧
      ∀ z, ¬ (z.length = 505 ∧ allZero z = true) → ∃ r, K z = .abort r :=
  ⟨_, rfl, fun _ hz => ⟨_, if_neg hz⟩⟩

/-- **P-OFFSET (d), P-SPLIT (c): the point commitments.** The peer's opened points are used only
when its opening matches its commitment under the frame `tag ‖ peer ‖ nonce ‖ value`
(`Engine.commitFrame`, as `split_ecdh.h` / `edwards_points.h`, and as `Random.joint`) and its
commitment differs from ours; otherwise the flow aborts. -/
theorem pointExchange_gate (hash : Bytes → Bytes) (me : Party) (tag : Bytes)
    (c c' o' : Bytes) (h : (hash (commitFrame tag me.other (o'.take 32) (o'.drop 32)) == c' && c' != c) = false) :
    Script.ensure (hash (commitFrame tag me.other (o'.take 32) (o'.drop 32)) == c' && c' != c) "point commitment" =
      .abort "point commitment" := by
  simp [Script.ensure, h]

/-! ## The validity bit (P-HINT (b); the op 66 status) -/

open TlsMpc.X25519 (bitValue)

/-- H-QR: 2 is not a square mod p (`proofs/` `two_not_square`). -/
def TwoNonSquare : Prop := ¬ ∃ r : F, r * r = ofNat 2

/-- Euler's criterion for p (`proofs/` `euler_criterion`, with `Local.Field.pow_eq`). -/
def EulerCriterion : Prop := ∀ x : F, x ≠ 0 → ((∃ r, r * r = x) ↔ TlsMpc.Node.Local.Field.euler x = ofNat 1)

/-- `lift-point`'s validity output (`liftPoint_eval`: `sel + b − 2·sel·b`) is the bit `sel xor b`. -/
theorem valid_bit (sel b : Bool) :
    bitValue sel + bitValue b - ofNat 2 * (bitValue sel * bitValue b) = bitValue (sel ^^ b) := by
  cases sel <;> cases b <;> decide

theorem root_sel (w : F) (sel : Bool) (c : F) (h : TlsMpc.Node.Local.Edwards.root w = some (sel, c)) :
    sel = (TlsMpc.Node.Local.Field.euler w == ofNat 1) := by
  unfold TlsMpc.Node.Local.Edwards.root at h
  dsimp only at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm

theorem inv_cancel (hinv : FieldInverse) (x : F) (hx : x ≠ 0) : x * inverse x = 1 := hinv x hx

theorem two_ne_zero : (ofNat 2 : F) ≠ 0 := by decide

theorem ring_sq (a b : F) : a * b * (a * b) = a * a * (b * b) := by grind
theorem ring_swap (m k im : F) : m * m * k * (im * im) = (m * im) * (m * im) * k := by grind
theorem ring_one_one : (1 : F) * 1 * (1 + 1) = 1 + 1 := by grind

/-- **Soundness of the validity bit**: with the honest `w = q·r²·(1 + b)` (`liftOpen_eval`, `r ≠ 0`)
and the public root, valid (`sel xor b`) implies `q` is a square: the root `s/r` is exhibited. -/
theorem lift_valid_sound (hinv : FieldInverse) (q r w : F) (b sel : Bool) (c : F)
    (hw : w = q * r * r * (ofNat 1 + bitValue b)) (hr : r ≠ 0)
    (hroot : TlsMpc.Node.Local.Edwards.root w = some (sel, c)) (hvalid : (sel ^^ b) = true) :
    ∃ v, v * v = q := by
  obtain ⟨s, hs, -⟩ := TlsMpc.Node.Local.Edwards.root_spec w sel c hroot
  have hri := hinv r hr
  have h2 := hinv (ofNat 2) two_ne_zero
  refine ⟨s * inverse r, ?_⟩
  generalize inverse r = ir at hri ⊢
  cases sel <;> cases b <;> simp at hvalid
  · -- sel = false, b = true: s² = w/2 = q r²
    simp only [Bool.false_eq_true, if_false] at hs
    rw [hw] at hs
    have e : (ofNat 1 + bitValue true : F) = ofNat 2 := by decide
    rw [e] at hs
    generalize ofNat 2 = t at hs h2
    generalize inverse t = it at hs h2
    grind
  · -- sel = true, b = false: s² = w = q r²
    simp only [if_true] at hs
    rw [hw] at hs
    have e : (ofNat 1 + bitValue false : F) = 1 := by decide
    rw [e] at hs
    grind

/-- **Completeness of the validity bit** (H-QR and Euler's criterion as hypotheses): for `q ≠ 0` a
square, the bit is 1 whatever the random bit `b`. -/
theorem lift_valid_complete (hinv : FieldInverse) (hE : EulerCriterion) (hQR : TwoNonSquare) (q r w : F) (b sel : Bool)
    (c : F) (hw : w = q * r * r * (ofNat 1 + bitValue b)) (hr : r ≠ 0) (hq : q ≠ 0) (hsq : ∃ v, v * v = q)
    (hroot : TlsMpc.Node.Local.Edwards.root w = some (sel, c)) : (sel ^^ b) = true := by
  have hs := root_sel w sel c hroot
  obtain ⟨v, hv⟩ := hsq
  have h1 : (ofNat 1 : F) = 1 := rfl
  have hv0 : v ≠ 0 := by intro h; apply hq; rw [← hv, h]; grind
  have hvr : v * r ≠ 0 := TlsMpc.FieldDag.V3.mul_ne_zero hinv hv0 hr
  cases b
  · have e : bitValue false = 0 := rfl
    rw [e, h1] at hw
    have hw' : w = (v * r) * (v * r) := by rw [hw, ← hv]; grind
    have hw0 : w ≠ 0 := by rw [hw']; exact TlsMpc.FieldDag.V3.mul_ne_zero hinv hvr hvr
    have := (hE w hw0).mp ⟨v * r, hw'.symm⟩
    simp [hs, this]
  · have e : bitValue true = 1 := rfl
    rw [e, h1] at hw
    have hw0 : w ≠ 0 := by
      rw [hw]
      have : (1 : F) + 1 = ofNat 2 := by decide
      rw [this]
      exact TlsMpc.FieldDag.V3.mul_ne_zero hinv (TlsMpc.FieldDag.V3.mul_ne_zero hinv
        (TlsMpc.FieldDag.V3.mul_ne_zero hinv hq hr) hr) two_ne_zero
    have hns : ¬ ∃ t, t * t = w := by
      rintro ⟨t, ht⟩
      apply hQR
      have hi := hinv _ hvr
      refine ⟨t * inverse (v * r), ?_⟩
      have h2 : (ofNat 2 : F) = 1 + 1 := by decide
      rw [h2]
      have htt : t * t = (v * r) * (v * r) * (1 + 1) := by rw [ht, hw, ← hv]; grind
      generalize inverse (v * r) = im at hi ⊢
      generalize v * r = m at hi htt
      rw [ring_sq t im, htt, ring_swap m (1 + 1) im, hi]
      exact ring_one_one
    have : TlsMpc.Node.Local.Field.euler w ≠ ofNat 1 := fun h => hns ((hE w hw0).mpr h)
    simp [hs, this]

/-- **What op 66's status reveals** (`prepareFirst`: a contact is prepared iff its opened validity
bit is 1 and its `w` is nonzero). For the honest lift of `u` (`w = q(u)·r²·(1 + b)`,
`q(u) = u(u² + 486662u + 1)`, `r ≠ 0`; the public root of a nonzero `w`), under H-QR and Euler's
criterion: the status is 255 exactly when `q(u)` is a nonzero square. With `proofs/`
`montQ_square_iff` (`IsSquare (montQ u) ↔ ∃ P, P.y ≠ 1 ∧ montU P = u`, and `u² + 486662u + 1 ≠ 0`):
exactly when `u ≠ 0` is the Montgomery coordinate of a curve point. Nothing else about `u`, `r` or
`b` is in the status. -/
theorem prepareStatus_iff (hinv : FieldInverse) (hE : EulerCriterion) (hQR : TwoNonSquare) (u r w : F) (b sel : Bool)
    (c : F) (hw : w = u * (u * u + ofNat 486662 * u + ofNat 1) * r * r * (ofNat 1 + bitValue b)) (hr : r ≠ 0)
    (hroot : w ≠ 0 → TlsMpc.Node.Local.Edwards.root w = some (sel, c)) :
    (bitValue (sel ^^ b) == ofNat 1 && !(w == 0)) = true ↔
      (u * (u * u + ofNat 486662 * u + ofNat 1) ≠ 0 ∧ ∃ v, v * v = u * (u * u + ofNat 486662 * u + ofNat 1)) := by
  have h1 : (ofNat 1 : F) = 1 := rfl
  have hb1 : (ofNat 1 + bitValue b : F) ≠ 0 := by cases b <;> decide
  have hwq : w = 0 ↔ u * (u * u + ofNat 486662 * u + ofNat 1) = 0 := by
    constructor
    · intro h0
      apply Classical.byContradiction
      intro hq
      exact TlsMpc.FieldDag.V3.mul_ne_zero hinv (TlsMpc.FieldDag.V3.mul_ne_zero hinv
        (TlsMpc.FieldDag.V3.mul_ne_zero hinv hq hr) hr) hb1 (by rw [← hw]; exact h0)
    · intro h0
      rw [hw, h0]
      grind
  have hbit : (bitValue (sel ^^ b) == ofNat 1) = (sel ^^ b) := by
    cases (sel ^^ b) <;> decide
  rw [hbit]
  constructor
  · intro h
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
    have hq : u * (u * u + ofNat 486662 * u + ofNat 1) ≠ 0 := fun h0 => h.2 (hwq.mpr h0)
    refine ⟨hq, lift_valid_sound hinv _ r w b sel c (by rw [hw]) hr (hroot h.2) h.1⟩
  · rintro ⟨hq, hsq⟩
    have hw0 : w ≠ 0 := fun h0 => hq (hwq.mp h0)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
    exact ⟨lift_valid_complete hinv hE hQR _ r w b sel c (by rw [hw]) hr hq hsq (hroot hw0), hw0⟩

/-! ## P-SPLIT: the agreement's quotient is the Montgomery coordinate of the sum -/

theorem power_mul (a b : F) (k : Nat) : TlsMpc.FieldDag.power (a * b) k = TlsMpc.FieldDag.power a k * TlsMpc.FieldDag.power b k := by
  induction k with
  | zero =>
    show TlsMpc.FieldDag.ofNat 1 = TlsMpc.FieldDag.ofNat 1 * TlsMpc.FieldDag.ofNat 1
    decide
  | succ k ih =>
    show a * b * TlsMpc.FieldDag.power (a * b) k = (a * TlsMpc.FieldDag.power a k) * (b * TlsMpc.FieldDag.power b k)
    rw [ih]
    grind

theorem inverse_mul (a b : F) : inverse (a * b) = inverse a * inverse b := power_mul a b _

/-- **P-SPLIT (a), algebraic part**: the split agreement's quotient `(den + num)/(den − num)` of
`edwards-add-u` (`EdwardsShare.addU_eval`) is the Montgomery coordinate `(1 + y)/(1 − y)` of the
affine sum `Local.Edwards.add T_A T_B` (= `pointAddValue`), when `den ≠ 0` (true for curve points by
completeness, `proofs/`). With H-GROUP (`proofs/` R7) the sum is `(k_A + k_B)·S`. -/
theorem addU_montU (hinv : FieldInverse) (x1 y1 x2 y2 : F)
    (hden : ofNat 121666 + ofNat 121665 * (x1 * x2 * (y1 * y2)) ≠ 0) :
    (ofNat 121666 + ofNat 121665 * (x1 * x2 * (y1 * y2)) + ofNat 121666 * (x1 * x2 + y1 * y2)) *
      inverse (ofNat 121666 + ofNat 121665 * (x1 * x2 * (y1 * y2)) - ofNat 121666 * (x1 * x2 + y1 * y2)) =
    TlsMpc.Node.Local.Edwards.montU (TlsMpc.Node.Local.Edwards.add (x1, y1) (x2, y2)) := by
  rw [TlsMpc.Node.Local.Edwards.montU_eq, TlsMpc.Node.Local.Edwards.add_eq]
  simp only [TlsMpc.EdwardsAffine.pointAddValue]
  generalize hd : ofNat 121666 + ofNat 121665 * (x1 * x2 * (y1 * y2)) = d at hden ⊢
  generalize hn : ofNat 121666 * (x1 * x2 + y1 * y2) = n
  have hn' : ofNat 121666 * (y1 * y2 + x1 * x2) = n := by rw [← hn]; grind
  rw [hn']
  have h1 := hinv d hden
  have hdi : inverse d ≠ 0 := by intro h; rw [h] at h1; grind
  have h2 := hinv (inverse d) hdi
  have h1' : (ofNat 1 : F) = 1 := rfl
  have e1 : ofNat 1 - n * inverse d = (d - n) * inverse d := by rw [h1']; grind
  have e2 : ofNat 1 + n * inverse d = (d + n) * inverse d := by rw [h1']; grind
  rw [e1, e2, inverse_mul]
  generalize inverse (inverse d) = iid at h2 ⊢
  generalize inverse d = id at h1 h2 ⊢
  generalize inverse (d - n) = idn
  grind

/-! ## P-SPLIT (a): two honest parties, through `jointRun` -/

open TlsMpc.Node.Flows.Run (jointRun_locals jointRun_program jointRun_openFieldThen runLocal localStep)

/-- A program without masks that computes `f` (`Conv.Computes`) runs `copies` instances. -/
theorem runProgram_computes (p : TlsMpc.FieldDag.V3.Program) (k : Nat) (marks : List TlsMpc.FieldDag.V3.OMark)
    (f : (Nat → F) → List F) (hc : Conv.Computes p k marks f) (copies : Nat) (vi : List F)
    (hl : vi.length = copies * k) :
    runProgram p copies vi [] = some (((List.range copies).map fun j => f (instanceAt vi k j)).flatten, []) := by
  obtain ⟨hi, hm, -, he⟩ := hc
  unfold runProgram
  rw [if_pos ⟨by rw [hi]; exact hl, by rw [hm]; simp⟩]
  rw [TlsMpc.Node.Flows.Run.mapM_some (fun j => (f (instanceAt vi p.inputs j), ([] : List F))) _
    (fun j => he _ _)]
  simp [hi, List.map_map, Function.comp_def]

/-- **P-SPLIT (a), run level.** Two honest parties whose store slots hold their points `T_A`,
`T_B` (curve points: the opened checks are 0) and nonzero-summing mask contributions, with the
programs loaded (`edwards-on-curve`, `edwards-add-u` computing their expressions, `field-quotient`),
both return the handle `f0 + 11` and the zero flag; it holds `(den + num)/(den − num)` of
`edwards-add-u` on `T_A, T_B`, which `addU_montU` identifies with `montU (T_A + T_B)` (and H-GROUP,
`proofs/` R7, with `u((k_A + k_B)·S)`). -/
theorem splitAgree_honest (hinv : FieldInverse) (E : Env) (pOn pAdd : TlsMpc.FieldDag.V3.Program)
    (hOn : E.programs onCurveName = some pOn) (hAdd : E.programs addUName = some pAdd)
    (hOnC : Conv.Computes pOn 2 [.pub] (fun i => [TlsMpc.EdwardsShare.onCurve.eval i]))
    (hAddC : Conv.Computes pAdd 4 [.never, .never] (fun i => TlsMpc.EdwardsShare.addU.map (TlsMpc.FieldDag.Expr.eval i)))
    (hq : E.programs Inversion.quotientName = some TlsMpc.FieldDag.V3.quotient)
    (σA σB : Store) (I : Ideal) (f0 tSlot maskSlot : Nat) (xA yA xB yB mA mB : F)
    (hA : σA.elems tSlot = [xA, yA]) (hB : σB.elems tSlot = [xB, yB])
    (hmA : σA.elems maskSlot = [mA]) (hmB : σB.elems maskSlot = [mB]) (hm : mA + mB ≠ 0)
    (hcA : TlsMpc.Node.Local.Edwards.curveValue (xA, yA) = 0) (hcB : TlsMpc.Node.Local.Edwards.curveValue (xB, yB) = 0) :
    let den := ofNat 121666 + ofNat 121665 * (xA * xB * (yA * yB))
    let num := ofNat 121666 * (xA * xB + yA * yB)
    (jointRun E (splitAgree f0 tSlot maskSlot) (splitAgree f0 tSlot maskSlot) σA σB I).result =
      some ((⟨f0 + 11⟩, decide (den - num = 0)), (⟨f0 + 11⟩, decide (den - num = 0))) ∧
    (jointRun E (splitAgree f0 tSlot maskSlot) (splitAgree f0 tSlot maskSlot) σA σB I).ideal.fields (f0 + 11) =
      some ((den + num) * inverse (den - num)) := by
  intro den num
  -- the inputs
  have hI1 : idealStep E .a (.fieldInput (hs f0 2) (hs (f0 + 2) 2) .elements false [xA, yA]) { elems := [xB, yB] } I =
      some (((I.setFields (hs f0 2) [xA, yA]).setFields (hs (f0 + 2) 2) [xB, yB]), none, none) := by
    simp [idealStep, coinsOk, hs]
  let I1 := (I.setFields (hs f0 2) [xA, yA]).setFields (hs (f0 + 2) 2) [xB, yB]
  obtain ⟨r1, i1⟩ := TlsMpc.Node.Flows.Contacts.jointRun_seq E
    (.fieldInput (hs f0 2) (hs (f0 + 2) 2) .elements false tSlot) (.fieldInput (hs f0 2) (hs (f0 + 2) 2) .elements false tSlot)
    _ _ σA σB I I1 (.fieldInput (hs f0 2) (hs (f0 + 2) 2) .elements false [xA, yA])
    (.fieldInput (hs f0 2) (hs (f0 + 2) 2) .elements false [xB, yB]) rfl
    (by simp [fill, hA, coinsOk, hs]) (by simp [fill, hB, coinsOk, hs]) (by simpa [Wire.part] using hI1)
  have n3 : f0 ≠ f0 + 2 + 1 := by omega
  have n5 : f0 ≠ f0 + 4 + 1 := by omega
  have hv : (hs f0 4).mapM (fun h => I1.fields h.id) = some [xA, yA, xB, yB] := by
    simp [I1, hs, Ideal.setFields, Ideal.setField, List.range_succ, n3]
  -- the check
  have hck : runLocal E [.fieldCheck] I1 = some I1 := by
    simp [runLocal, localStep, idealStep, TlsMpc.Node.Flows.Contacts.blankWire, InstrP.map]
  -- the on-curve program
  have hrun1 : runProgram pOn 2 [xA, yA, xB, yB] [] = some ([0, 0], []) := by
    rw [runProgram_computes pOn 2 [.pub] _ hOnC 2 _ rfl]
    have e1 := hcA
    have e2 := hcB
    simp only [TlsMpc.Node.Local.Edwards.curveValue] at e1 e2
    simp [TlsMpc.EdwardsShare.onCurve_eval, instanceAt, List.range_succ, e1, e2]
  have hrun2 : runProgram pAdd 1 [xA, yA, xB, yB] [] = some ([den + num, den - num], []) := by
    rw [runProgram_computes pAdd 4 [.never, .never] _ hAddC 1 _ rfl]
    simp [TlsMpc.EdwardsShare.addU_eval, instanceAt, den, num]
  unfold splitAgree splitBlock
  simp only [seqs, List.foldr]
  rw [r1, i1]
  obtain ⟨r2, i2⟩ := jointRun_locals E _ _ σA σB [.fieldCheck] (by simp [TlsMpc.Node.Flows.Run.isLocal]) I1 I1 hck
  simp only [seqs, List.foldr] at r2 i2
  rw [r2, i2]
  obtain ⟨r3, i3⟩ := jointRun_program E onCurveName 2 (hs f0 4) [] (hs (f0 + 4) 2) Label.curveChecks _ _ σA σB I1
    pOn [xA, yA, xB, yB] [] [0, 0] [] hOn hv rfl hrun1 (by simp [hs])
  rw [r3, i3]
  let I2 := I1.setFields (hs (f0 + 4) 2) [0, 0]
  obtain ⟨r4, i4⟩ := jointRun_openFieldThen E (hs (f0 + 4) 2) Label.curveChecks _ _ σA σB I2 [0, 0]
    (by simp [I2, hs, Ideal.setFields, Ideal.setField, List.range_succ])
  rw [r4, i4]
  have hok : ([0, 0] : List F).length = 2 ∧ allZero [0, 0] = true := ⟨rfl, by decide⟩
  simp only [if_pos hok]
  -- add-u and the frees
  have hv2 : (hs f0 4).mapM (fun h => I2.fields h.id) = some [xA, yA, xB, yB] := by
    simp [I2, I1, hs, Ideal.setFields, Ideal.setField, List.range_succ, n3, n5]
  unfold splitTail
  simp only [List.foldr]
  obtain ⟨r5, i5⟩ := jointRun_program E addUName 1 (hs f0 4) [] (hs (f0 + 6) 2) Label.curveChecks _ _ σA σB I2
    pAdd [xA, yA, xB, yB] [] [den + num, den - num] [] hAdd hv2 rfl hrun2 (by simp [hs])
  rw [r5, i5]
  let I3 := I2.setFields (hs (f0 + 6) 2) [den + num, den - num]
  have hfr : ∀ i ∈ freeFs (hs f0 6), TlsMpc.Node.Flows.Run.isLocal i = true := by
    intro i hi
    simp only [freeFs, List.mem_map] at hi
    obtain ⟨_, _, rfl⟩ := hi
    rfl
  obtain ⟨I4, hI4⟩ : ∃ I4, runLocal E (freeFs (hs f0 6)) I3 = some I4 ∧
      I4.fields (f0 + 6) = some (den + num) ∧ I4.fields (f0 + 7) = some (den - num) := by
    refine ⟨_, rfl, ?_, ?_⟩ <;>
      simp [freeFs, hs, List.range_succ, runLocal, localStep, idealStep, TlsMpc.Node.Flows.Contacts.blankWire,
        InstrP.map, Ideal.dropField, I3, Ideal.setFields, Ideal.setField]
  obtain ⟨r6, i6⟩ := jointRun_locals E (Inversion.quotientScript (f0 + 8) maskSlot ⟨f0 + 6⟩ ⟨f0 + 7⟩)
    (Inversion.quotientScript (f0 + 8) maskSlot ⟨f0 + 6⟩ ⟨f0 + 7⟩) σA σB (freeFs (hs f0 6)) hfr I3 I4 hI4.1
  simp only [seqs] at r6 i6
  rw [r6, i6]
  have hQ := Inversion.quotient_honest hinv E hq σA σB I4 (f0 + 8) maskSlot ⟨f0 + 6⟩ ⟨f0 + 7⟩ (den + num) (den - num)
    mA mB hI4.2.1 hI4.2.2 (by simp) (by simp) hmA hmB hm
  exact ⟨by rw [hQ.1], hQ.2⟩

end TlsMpc.Node.Flows.Curve
