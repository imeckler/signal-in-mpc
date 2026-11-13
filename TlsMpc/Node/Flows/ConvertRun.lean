import TlsMpc.Node.Flows.MasksHonest
import TlsMpc.Node.Flows.Convert

/-!
# P-BITS at run level: `Convert.sharedBits` in the model

REORGANIZATION_PLAN.md 7.1 P-BITS; stage S10. `Convert.lean` has the protocol layer
(`bits_checks_zero_iff`, `bits_xor`, `bits_honest_checks`). This file runs the script in the model
of `Engine/Model.lean`, through its `program` instructions:

  * `sharedBits_sound` (P-BITS (a), (b), against ANY adversary; with `FieldInverse`): if the run
    returns, it returns the handles `bitsOuts`; EVERY input of BOTH parties, as the engines hold
    them, is 0 or 1 (the adversary's too: the bit checks opened to 0); and output handle `i` holds
    the field XOR `a_i + b_i − 2·a_i·b_i` of the two parties' inputs — for bits, the bit
    `a_i ⊕ b_i` (`Conv.bitXorValue_bits`).
  * `sharedBits_honest` (P-BITS (b), two honest parties, `jointRun`): with local bits `as`, `bs` as
    0/1 coins in their stores, both return `bitsOuts`, their stores are unchanged, and output
    handle `i` holds the field bit of `as_i ⊕ bs_i`.
With `X25519SwapBits.swapBit_shares` (the local bits are the swap bits of each share, `top` set for
party A only), the outputs are the swap bits of the XORed scalar.

Not done here: P-B2F (a) through `jointRun` for the whole bundle (`b2f_value` is per bit).
-/

namespace TlsMpc.Node.Flows.Convert

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Conv
open TlsMpc.Node.Flows.Masks (setFields_block mapM_block mapM_append_vals mapM_flatMap_vals runProgram_chunks
  flatten_singletons flatten_map_singleton' flatten_map' getD_map_range coinsOk_bits getD_map_lt)
open TlsMpc.FieldDag (F modulus ofNat)
open TlsMpc.FieldDag.V3 (FieldInverse)

/-- A bit check's value. -/
def chk (c : F) : F := c * (c - ofNat 1)

theorem mapM_one {α β : Type} (look : α → Option β) (a : α) (v : β) (h : look a = some v) :
    [a].mapM look = some [v] := by
  simp [List.mapM_cons, h]

/-- The engines after both parties' inputs: A's are `va`, B's are `vb`. -/
theorem bits_in (f0 n : Nat) (I : Ideal) (va vb : List F) (hla : va.length = n) (hlb : vb.length = n) :
    (∀ i, i < n → ((I.setFields (bitsA f0 n) va).setFields (bitsB f0 n) vb).fields (f0 + i) = some (va.getD i 0)) ∧
    (∀ i, i < n → ((I.setFields (bitsA f0 n) va).setFields (bitsB f0 n) vb).fields (f0 + n + i) =
      some (vb.getD i 0)) := by
  obtain ⟨-, a2, a3⟩ := setFields_block I (fun i => (⟨f0 + i⟩ : FieldH)) f0 n va (fun _ _ => rfl) hla
  obtain ⟨-, c2, c3⟩ := setFields_block (I.setFields (bitsA f0 n) va) (fun i => (⟨f0 + n + i⟩ : FieldH)) (f0 + n) n vb
    (fun _ _ => rfl) hlb
  exact ⟨fun i hi => by
    show ((I.setFields (bitsA f0 n) va).setFields ((List.range n).map fun i => (⟨f0 + n + i⟩ : FieldH)) vb).fields _ = _
    rw [c2 _ (Or.inl (by omega))]
    exact a3 i hi, fun i hi => c3 i hi⟩

/-- **The two program steps of `sharedBits`**: with A's inputs `va` and B's `vb` in the engines,
the bit-check step succeeds, opens nothing itself, and the check handles hold `chk` of every
input; the XOR step succeeds and output `i` holds `bitXorValue va_i vb_i`. -/
theorem bits_programs (E : Env) (hP : ProgsLoaded E) (f0 n : Nat) (J : Ideal) (va vb : List F)
    (hla : va.length = n) (hlb : vb.length = n)
    (hA : ∀ i, i < n → J.fields (f0 + i) = some (va.getD i 0))
    (hB : ∀ i, i < n → J.fields (f0 + n + i) = some (vb.getD i 0)) :
    ∃ pc px xin xo,
      E.programs bitCheckName = some pc ∧
      (bitsA f0 n ++ bitsB f0 n).mapM (fun g => J.fields g.id) = some (va ++ vb) ∧
      runProgram pc (2 * n) (va ++ vb) [] = some ((va ++ vb).map chk, []) ∧
      ((va ++ vb).map chk).length = (bitsChk f0 n).length ∧
      (bitsChk f0 n).mapM (fun g => (J.setFields (bitsChk f0 n) ((va ++ vb).map chk)).fields g.id) =
        some ((va ++ vb).map chk) ∧
      E.programs bitXorName = some px ∧
      (bitsPairs f0 n).mapM (fun g => (J.setFields (bitsChk f0 n) ((va ++ vb).map chk)).fields g.id) = some xin ∧
      runProgram px n xin [] = some (xo, []) ∧ xo.length = (bitsOuts f0 n).length ∧
      ∀ i, i < n → ((J.setFields (bitsChk f0 n) ((va ++ vb).map chk)).setFields (bitsOuts f0 n) xo).fields
        (f0 + 4 * n + i) = some (bitXorValue (va.getD i 0) (vb.getD i 0)) := by
  obtain ⟨pc, hpc, hcc⟩ := hP.bitCheck
  obtain ⟨px, hpx, hcx⟩ := hP.bitXor
  have hlen : (va ++ vb).length = 2 * n := by rw [List.length_append, hla, hlb, Nat.two_mul]
  -- the check
  have hins : (bitsA f0 n ++ bitsB f0 n).mapM (fun g => J.fields g.id) = some (va ++ vb) :=
    mapM_append_vals _ _ _ _ _ (mapM_block J (fun i => (⟨f0 + i⟩ : FieldH)) f0 n va (fun _ _ => rfl) hla hA)
      (mapM_block J (fun i => (⟨f0 + n + i⟩ : FieldH)) (f0 + n) n vb (fun _ _ => rfl) hlb hB)
  have hrun := runProgram_chunks pc 1 [.pub] _ hcc ((va ++ vb).map fun a => [a]) (by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨a, -, rfl⟩ := hc
    rfl)
  rw [List.length_map, hlen, flatten_singletons, List.map_map] at hrun
  have hvo : ((va ++ vb).map ((fun c : List F => [c.getD 0 0 * (c.getD 0 0 - ofNat 1)]) ∘ fun a => [a])).flatten =
      (va ++ vb).map chk := flatten_map_singleton' chk (va ++ vb)
  rw [hvo] at hrun
  have hclen : ((va ++ vb).map chk).length = 2 * n := by rw [List.length_map, hlen]
  obtain ⟨-, k2, k3⟩ := setFields_block J (fun i => (⟨f0 + 2 * n + i⟩ : FieldH)) (f0 + 2 * n) (2 * n)
    ((va ++ vb).map chk) (fun _ _ => rfl) hclen
  -- the XOR
  have hxin : (bitsPairs f0 n).mapM (fun g => (J.setFields (bitsChk f0 n) ((va ++ vb).map chk)).fields g.id) =
      some ((List.range n).map fun i => [va.getD i 0, vb.getD i 0]).flatten := by
    unfold bitsPairs
    rw [flatten_map']
    apply mapM_flatMap_vals
    intro i hi
    have hi' := List.mem_range.mp hi
    have e1 := k2 (f0 + i) (Or.inl (by omega))
    have e2 := k2 (f0 + n + i) (Or.inl (by omega))
    exact mapM_append_vals _ [_] [_] [va.getD i 0] [vb.getD i 0]
      (mapM_one _ _ _ (by
        show (J.setFields ((List.range (2 * n)).map fun i => (⟨f0 + 2 * n + i⟩ : FieldH)) _).fields (f0 + i) = _
        rw [e1]
        exact hA i hi'))
      (mapM_one _ _ _ (by
        show (J.setFields ((List.range (2 * n)).map fun i => (⟨f0 + 2 * n + i⟩ : FieldH)) _).fields (f0 + n + i) = _
        rw [e2]
        exact hB i hi'))
  have hrunx := runProgram_chunks px 2 [.never] _ hcx ((List.range n).map fun i => [va.getD i 0, vb.getD i 0]) (by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨i, -, rfl⟩ := hc
    rfl)
  rw [List.length_map, List.length_range, List.map_map] at hrunx
  have hxo : ((List.range n).map ((fun c : List F => [bitXorValue (c.getD 0 0) (c.getD 1 0)]) ∘
      fun i => [va.getD i 0, vb.getD i 0])).flatten =
      (List.range n).map (fun i => bitXorValue (va.getD i 0) (vb.getD i 0)) :=
    flatten_map_singleton' (fun i => bitXorValue (va.getD i 0) (vb.getD i 0)) (List.range n)
  rw [hxo] at hrunx
  have hxlen : ((List.range n).map (fun i => bitXorValue (va.getD i 0) (vb.getD i 0))).length = n := by
    rw [List.length_map, List.length_range]
  obtain ⟨-, -, x3⟩ := setFields_block (J.setFields (bitsChk f0 n) ((va ++ vb).map chk))
    (fun i => (⟨f0 + 4 * n + i⟩ : FieldH)) (f0 + 4 * n) n
    ((List.range n).map (fun i => bitXorValue (va.getD i 0) (vb.getD i 0))) (fun _ _ => rfl) hxlen
  refine ⟨pc, px, _, _, hpc, hins, hrun, ?_, ?_, hpx, hxin, hrunx, ?_, fun i hi => ?_⟩
  · rw [hclen, bitsChk, List.length_map, List.length_range]
  · exact mapM_block _ (fun i => (⟨f0 + 2 * n + i⟩ : FieldH)) (f0 + 2 * n) (2 * n) _ (fun _ _ => rfl) hclen k3
  · rw [hxlen, bitsOuts, List.length_map, List.length_range]
  · have := x3 i hi
    rw [getD_map_range _ _ _ _ hi] at this
    exact this

section Runs

variable (E : Env)

/-- **P-BITS (a), (b) at run level, against any adversary** (with `FieldInverse`). If `sharedBits`
returns: it returns `bitsOuts`; every input of both parties in the engines is 0 or 1; and output
`i` holds the field XOR of the two parties' inputs `i`. (`mine`: the honest party's inputs, from
its store; `pe`: the adversary's.) -/
theorem sharedBits_sound (hinv : FieldInverse) (hP : ProgsLoaded E) (me : Party) (adv : Adversary)
    (f0 n slot : Nat) (σ : Store) (I : Ideal) (vD : List Release) (outs : List FieldH)
    (hres : (withAdv E me adv (sharedBits f0 n slot) σ I vD).result = some outs) :
    outs = bitsOuts f0 n ∧ ∃ pe : List F, pe.length = n ∧ (σ.elems slot).length = n ∧
      (∀ c ∈ σ.elems slot ++ pe, c = 0 ∨ c = ofNat 1) ∧
      ∀ i, i < n → (withAdv E me adv (sharedBits f0 n slot) σ I vD).ideal.fields (f0 + 4 * n + i) =
        some (bitXorValue ((if me = .a then σ.elems slot else pe).getD i 0)
          ((if me = .a then pe else σ.elems slot).getD i 0)) := by
  have hret : Ret (withAdv E me adv (sharedBits f0 n slot) σ I vD) outs
      (withAdv E me adv (sharedBits f0 n slot) σ I vD).ideal := ⟨hres, rfl⟩
  generalize (withAdv E me adv (sharedBits f0 n slot) σ I vD).ideal = J at hret ⊢
  unfold sharedBits at hret
  obtain ⟨pe, hpe, hl, r1⟩ := ret_fieldInput E me adv _ _ _ _ _ _ σ I vD outs J
    (by rw [bitsA, bitsB, List.length_map, List.length_map]) hret
  have hpe' : pe.length = n := by rw [hpe, bitsA, List.length_map, List.length_range]
  have hl' : (σ.elems slot).length = n := by rw [hl, bitsA, List.length_map, List.length_range]
  have hla : (if me = Party.a then σ.elems slot else pe).length = n := by split <;> assumption
  have hlb : (if me = Party.a then pe else σ.elems slot).length = n := by split <;> assumption
  obtain ⟨hA, hB⟩ := bits_in f0 n I _ _ hla hlb
  obtain ⟨pc, px, xin, xo, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ := bits_programs E hP f0 n _ _ _ hla hlb hA hB
  unfold bothFields at r1
  obtain ⟨pc', vi, vm, vo, op, vD1, e1, e2, e3, e4, r2⟩ := ret_program E me adv _ _ _ _ _ _ _ σ _ _ outs J r1
  have epc : pc' = pc := Option.some.inj (e1.symm.trans q1)
  have evi : vi = _ := Option.some.inj (e2.symm.trans q2)
  have evm : vm = [] := by simpa using e3.symm
  subst epc evi evm
  have evo : vo = _ := (Prod.mk.inj (Option.some.inj (e4.symm.trans q3))).1
  subst evo
  obtain ⟨z, vD2, ez, r3⟩ := ret_openFieldThen E me adv _ _ _ σ _ _ outs J r2
  have hz : z = _ := Option.some.inj (ez.symm.trans q5)
  obtain ⟨hall, r4⟩ := ret_ite E me adv _ _ _ σ _ _ outs J r3
  obtain ⟨px', wi, wm, wo, op2, vD3, e5, e6, e7, e8, r5⟩ := ret_program E me adv _ _ _ _ _ _ _ σ _ _ outs J r4
  have epx : px' = px := Option.some.inj (e5.symm.trans q6)
  have ewi : wi = xin := Option.some.inj (e6.symm.trans q7)
  have ewm : wm = [] := by simpa using e7.symm
  subst epx ewi ewm
  have ewo : wo = xo := (Prod.mk.inj (Option.some.inj (e8.symm.trans q8))).1
  subst ewo
  obtain ⟨ho, hJ⟩ := ret_done E me adv _ σ _ _ outs J r5
  refine ⟨ho, pe, hpe', hl', fun c hc => ?_, fun i hi => ?_⟩
  · have hc' : c ∈ (if me = Party.a then σ.elems slot else pe) ++ (if me = Party.a then pe else σ.elems slot) := by
      rw [List.mem_append] at hc ⊢
      cases me
      · exact hc
      · exact hc.symm
    rw [hz] at hall
    have h0 := List.all_eq_true.mp hall (chk c) (List.mem_map.mpr ⟨c, hc', rfl⟩)
    exact (TlsMpc.Node.Flows.Masks.bitCheck_zero_iff hinv c).mp (by simpa [chk] using h0)
  · rw [hJ]
    exact q10 i hi

/-- **P-BITS (b) for two honest parties** (`jointRun`): with local bits `as`, `bs` (as 0/1 coins in
their stores), both return `bitsOuts`, their stores are unchanged, and output `i` holds the field
bit of `as_i ⊕ bs_i`. -/
theorem sharedBits_honest (hP : ProgsLoaded E) (f0 n slotA slotB : Nat) (σA σB : Store) (I : Ideal)
    (as bs : Bits) (hla : as.length = n) (hlb : bs.length = n)
    (hA : σA.elems slotA = as.map X25519.bitValue) (hB : σB.elems slotB = bs.map X25519.bitValue) :
    ∃ J, JRet (jointRun E (sharedBits f0 n slotA) (sharedBits f0 n slotB) σA σB I) (bitsOuts f0 n) (bitsOuts f0 n)
        J σA σB ∧
      ∀ i, i < n → J.fields (f0 + 4 * n + i) = some (X25519.bitValue (as.getD i false ^^ bs.getD i false)) := by
  have hva : (σA.elems slotA).length = n := by rw [hA, List.length_map, hla]
  have hvb : (σB.elems slotB).length = n := by rw [hB, List.length_map, hlb]
  obtain ⟨fA, fB⟩ := bits_in f0 n I _ _ hva hvb
  obtain ⟨pc, px, xin, xo, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ := bits_programs E hP f0 n _ _ _ hva hvb fA fB
  have hzero : ((σA.elems slotA ++ σB.elems slotB).map chk).all (· == 0) = true := by
    rw [List.all_eq_true]
    intro z hz
    simp only [List.mem_map, List.mem_append] at hz
    obtain ⟨c, hc, rfl⟩ := hz
    have hbit : ∃ x : Bool, c = X25519.bitValue x := by
      rcases hc with hc | hc
      · rw [hA] at hc
        obtain ⟨x, -, rfl⟩ := List.mem_map.mp hc
        exact ⟨x, rfl⟩
      · rw [hB] at hc
        obtain ⟨x, -, rfl⟩ := List.mem_map.mp hc
        exact ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := hbit
    have := TlsMpc.Node.Flows.Masks.bitValue_check x
    simpa [chk] using this
  refine ⟨(((I.setFields (bitsA f0 n) (σA.elems slotA)).setFields (bitsB f0 n) (σB.elems slotB)).setFields
    (bitsChk f0 n) ((σA.elems slotA ++ σB.elems slotB).map chk)).setFields (bitsOuts f0 n) xo, ?_, fun i hi => ?_⟩
  · unfold sharedBits
    refine jret_fieldInput E _ _ _ _ _ _ _ _ σA σB I _ _ _ σA σB
      (by rw [bitsA, bitsB, List.length_map, List.length_map])
      (by rw [hva, bitsA, List.length_map, List.length_range]) (by rw [hA]; exact coinsOk_bits _)
      (by rw [hvb, bitsA, List.length_map, List.length_range]) (by rw [hB]; exact coinsOk_bits _) ?_
    refine jret_program E _ _ _ _ _ _ _ _ σA σB _ pc _ [] _ [] _ _ _ σA σB q1 q2 rfl q3 q4 ?_
    refine jret_openFieldThen E _ _ _ _ σA σB _ _ _ _ _ σA σB q5 ?_
    simp only [hzero, if_true]
    refine jret_program E _ _ _ _ _ _ _ _ σA σB _ px xin [] xo [] _ _ _ σA σB q6 q7 rfl q8 q9 ?_
    exact jret_done E _ _ σA σB _
  · have := q10 i hi
    rw [this, hA, hB, getD_map_lt _ _ _ false _ (by rw [hla]; exact hi),
      getD_map_lt _ _ _ false _ (by rw [hlb]; exact hi), bitXorValue_bits]

end Runs

/-! ## P-B2F (a) through `jointRun`: the whole bundle -/

theorem localStep_sub (E : Env) (out a b : FieldH) (I : Ideal) :
    localStep E (.fieldSub out a b) I =
      match I.fields a.id, I.fields b.id with
      | some x, some y => some (I.setField out (x - y))
      | _, _ => none := by
  simp only [localStep, idealStep, TlsMpc.Node.Flows.Contacts.blankWire, InstrP.map]
  cases I.fields a.id <;> cases I.fields b.id <;> rfl

/-- A block of field subtractions with distinct outputs that are none of the operands, every
operand defined: each output holds the difference of its operands' values before the block. -/
theorem runLocal_subs (E : Env) : ∀ (ts : List (FieldH × FieldH × FieldH)) (I : Ideal),
    (ts.map (·.1.id)).Nodup → (∀ t ∈ ts, ∀ t' ∈ ts, t.1.id ≠ t'.2.1.id ∧ t.1.id ≠ t'.2.2.id) →
    (∀ t ∈ ts, (I.fields t.2.1.id).isSome ∧ (I.fields t.2.2.id).isSome) →
    ∃ I', runLocal E (ts.map fun t => .fieldSub t.1 t.2.1 t.2.2) I = some I' ∧ I'.bools = I.bools ∧
      (∀ t ∈ ts, I'.fields t.1.id = some ((I.fields t.2.1.id).getD 0 - (I.fields t.2.2.id).getD 0)) ∧
      (∀ j, (∀ t ∈ ts, t.1.id ≠ j) → I'.fields j = I.fields j)
  | [], I, _, _, _ => ⟨I, rfl, rfl, by simp, fun _ _ => rfl⟩
  | t :: ts, I, hn, hd, hs => by
    obtain ⟨out, a, b⟩ := t
    have hsa := (hs (out, a, b) (by simp)).1
    have hsb := (hs (out, a, b) (by simp)).2
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsa
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsb
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    have hd' : ∀ t ∈ ts, ∀ t' ∈ ts, t.1.id ≠ t'.2.1.id ∧ t.1.id ≠ t'.2.2.id :=
      fun t ht t' ht' => hd t (by simp [ht]) t' (by simp [ht'])
    have hfr : ∀ t ∈ ts, out.id ≠ t.2.1.id ∧ out.id ≠ t.2.2.id :=
      fun t ht => hd (out, a, b) (by simp) t (by simp [ht])
    have hs' : ∀ t ∈ ts, ((I.setField out (x - y)).fields t.2.1.id).isSome ∧
        ((I.setField out (x - y)).fields t.2.2.id).isSome := by
      intro t ht
      have h1 := hfr t ht
      have h2 := hs t (by simp [ht])
      simp only [Ideal.setField]
      rw [if_neg (Ne.symm h1.1), if_neg (Ne.symm h1.2)]
      exact h2
    obtain ⟨I', h1, h2, h3, h4⟩ := runLocal_subs E ts (I.setField out (x - y)) hn.2 hd' hs'
    refine ⟨I', ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, runLocal, localStep_sub, hx, hy]
      exact h1
    · rw [h2]
      rfl
    · intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · have hne : ∀ t ∈ ts, t.1.id ≠ out.id := fun t ht e => hn.1 ⟨t, ht, e⟩
        rw [h4 _ hne]
        simp [Ideal.setField, hx, hy]
      · rw [h3 t ht]
        have h1' := hfr t ht
        simp only [Ideal.setField]
        rw [if_neg (Ne.symm h1'.1), if_neg (Ne.symm h1'.2)]
    · intro j hj
      rw [h4 j (fun t ht => hj t (by simp [ht]))]
      simp only [Ideal.setField]
      rw [if_neg (Ne.symm (hj (out, a, b) (by simp)))]

theorem runLocal_freeFields (E : Env) : ∀ (hs : List FieldH) (I : Ideal),
    ∃ I', runLocal E (hs.map fun h => (.freeField h : Instr)) I = some I' ∧
      ∀ j, (∀ h ∈ hs, h.id ≠ j) → I'.fields j = I.fields j
  | [], I => ⟨I, rfl, fun _ _ => rfl⟩
  | h :: hs, I => by
    obtain ⟨I', h1, h2⟩ := runLocal_freeFields E hs (I.dropField h)
    refine ⟨I', ?_, fun j hj => ?_⟩
    · have e : localStep E (.freeField h) I = some (I.dropField h) := by
        simp [localStep, idealStep, TlsMpc.Node.Flows.Contacts.blankWire, InstrP.map]
      simp only [List.map_cons, runLocal, e]
      exact h1
    · rw [h2 j (fun g hg => hj g (by simp [hg]))]
      simp only [Ideal.dropField]
      rw [if_neg (Ne.symm (hj h (by simp)))]

theorem mem_zipIdx' {α : Type} (d : α) : ∀ (l : List α) (k : Nat) (e : α × Nat), e ∈ l.zipIdx k →
    k ≤ e.2 ∧ e.2 < k + l.length ∧ l.getD (e.2 - k) d = e.1
  | [], k, e, h => by simp at h
  | a :: l, k, e, h => by
    rw [List.zipIdx_cons] at h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨h1, h2, h3⟩ := mem_zipIdx' d l (k + 1) e h
      refine ⟨by omega, by rw [List.length_cons]; omega, ?_⟩
      have : e.2 - k = (e.2 - (k + 1)) + 1 := by omega
      rw [this, List.getD_cons_succ]
      exact h3

theorem zipIdx_mem' {α : Type} (d : α) : ∀ (l : List α) (k i : Nat), i < l.length →
    (l.getD i d, k + i) ∈ l.zipIdx k
  | [], k, i, h => by simp at h
  | a :: l, k, 0, _ => by
    rw [List.zipIdx_cons]
    simp
  | a :: l, k, i + 1, h => by
    rw [List.zipIdx_cons, List.getD_cons_succ]
    have := zipIdx_mem' d l (k + 1) i (by simpa using h)
    rw [show k + (i + 1) = k + 1 + i by omega]
    exact List.mem_cons_of_mem _ this

theorem interleave_map (xb ρ : Bits) (n : Nat) (hx : xb.length = n) :
    (interleave n).map ((xb ++ ρ).getD · false) =
      ((List.range n).map fun i => [xb.getD i false, ρ.getD i false]).flatten := by
  unfold interleave
  rw [List.map_flatMap, flatten_map']
  apply TlsMpc.Node.Flows.Masks.flatMap_congr'
  intro i hi
  have hi' := List.mem_range.mp hi
  show [(xb ++ ρ).getD i false, (xb ++ ρ).getD (n + i) false] = _
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega), hx, Nat.add_sub_cancel_left]

section B2F

variable (E : Env)

/-- **P-B2F (a) through `jointRun`, the whole bundle.** Two honest parties convert the bits `xb`
behind `x` with consistent pairs (pair `i`: the Boolean bit `ρ_i` and the field bit of `ρ_i`):
both return the handles `b2fOuts`, their stores are unchanged, and output `i` holds the field bit
of `xb_i`. (The pairs' field handles are not the script's own handles `f0`, `f0 + 1`,
`f0 + 2 + j`; `x` is not the script's handle `n0`.) -/
theorem b2f_honest (hW : WordLoaded E) (n0 f0 : Nat) (x : BoolH) (ps : List BitPair) (σA σB : Store) (I : Ideal)
    (xb ρ : Bits) (hx : I.bools x.id = some xb) (hxl : xb.length = ps.length) (hρl : ρ.length = ps.length)
    (hbits : (ps.map (·.bit)).mapM (fun h => I.bools h.id) = some (ρ.map fun r => [r]))
    (hflds : ∀ i, i < ps.length →
      I.fields (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field.id = some (X25519.bitValue (ρ.getD i false)))
    (hx0 : x.id ≠ n0)
    (hfid : ∀ i, i < ps.length → (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field.id ≠ f0 ∧ (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field.id ≠ f0 + 1 ∧
      ∀ j, j < ps.length → (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field.id ≠ f0 + 2 + j) :
    ∃ J, JRet (jointRun E (bitsToField n0 f0 x ps) (bitsToField n0 f0 x ps) σA σB I) (b2fOuts f0 ps.length)
        (b2fOuts f0 ps.length) J σA σB ∧
      ∀ i, i < ps.length → J.fields (f0 + 2 + i) = some (X25519.bitValue (xb.getD i false)) := by
  -- the Boolean block
  have s1 := TlsMpc.Node.Flows.Masks.localStep_concat E ⟨n0⟩ _ I _ hbits
  rw [flatten_singletons] at s1
  have s2 := TlsMpc.Node.Flows.Masks.localStep_concat E ⟨n0 + 1⟩ [x, ⟨n0⟩] (I.setBool ⟨n0⟩ ρ) [xb, ρ]
    (by simp [List.mapM_cons, Ideal.setBool, hx, hx0])
  have e2 : [xb, ρ].flatten = xb ++ ρ := by simp
  rw [e2] at s2
  have hidx : (interleave ps.length).all (· < (xb ++ ρ).length) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq, interleave, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false, List.length_append, hxl, hρl]
    rintro i ⟨j, hj, rfl | rfl⟩ <;> omega
  have s3 := TlsMpc.Node.Flows.Masks.localStep_pick E ⟨n0 + 2⟩ ⟨n0 + 1⟩ _
    ((I.setBool ⟨n0⟩ ρ).setBool ⟨n0 + 1⟩ (xb ++ ρ)) (xb ++ ρ) (by simp [Ideal.setBool]) hidx
  rw [interleave_map xb ρ ps.length hxl] at s3
  have hL : ∀ y ∈ (List.range ps.length).map (fun i => [xb.getD i false, ρ.getD i false]),
      y.length = xorBitOpenC.inWidth := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨i, -, rfl⟩ := hy
    rfl
  have s4 := TlsMpc.Node.Flows.Masks.localStep_run E ⟨n0 + 3⟩ ⟨n0 + 2⟩ xorBitOpenName ps.length xorBitOpenC
    (((I.setBool ⟨n0⟩ ρ).setBool ⟨n0 + 1⟩ (xb ++ ρ)).setBool ⟨n0 + 2⟩
      ((List.range ps.length).map fun i => [xb.getD i false, ρ.getD i false]).flatten)
    ((List.range ps.length).map fun i => [xb.getD i false, ρ.getD i false]).flatten
    hW.xorBitOpen (by simp [Ideal.setBool])
    (by
      rw [TlsMpc.Node.Flows.Masks.length_flatten_eq 2 _ hL, List.length_map, List.length_range]
      rfl)
  have e4 := TlsMpc.Node.Flows.Masks.runCopies_flatten xorBitOpenC _ hL
  rw [List.length_map, List.length_range] at e4
  have e4' : (((List.range ps.length).map fun i => [xb.getD i false, ρ.getD i false]).map xorBitOpenC.eval).flatten =
      (List.range ps.length).map (fun i => (xb.getD i false ^^ ρ.getD i false)) := by
    rw [List.map_map]
    exact flatten_map_singleton' (fun i => (xb.getD i false ^^ ρ.getD i false)) (List.range ps.length)
  rw [e4, e4'] at s4
  have hblock : runLocal E (b2fBlock n0 x ps) I =
      some ((((I.setBool ⟨n0⟩ ρ).setBool ⟨n0 + 1⟩ (xb ++ ρ)).setBool ⟨n0 + 2⟩
        ((List.range ps.length).map fun i => [xb.getD i false, ρ.getD i false]).flatten).setBool ⟨n0 + 3⟩
        ((List.range ps.length).map (fun i => (xb.getD i false ^^ ρ.getD i false)))) := by
    simp only [b2fBlock, runLocal, s1, s2, s3, s4]
  generalize hI4 : (((I.setBool ⟨n0⟩ ρ).setBool ⟨n0 + 1⟩ (xb ++ ρ)).setBool ⟨n0 + 2⟩
        ((List.range ps.length).map fun i => [xb.getD i false, ρ.getD i false]).flatten).setBool ⟨n0 + 3⟩
        ((List.range ps.length).map (fun i => (xb.getD i false ^^ ρ.getD i false))) = I4 at hblock
  have hI4f : I4.fields = I.fields := by rw [← hI4]; rfl
  have hI4o : I4.bools (n0 + 3) = some ((List.range ps.length).map (fun i => (xb.getD i false ^^ ρ.getD i false))) := by
    rw [← hI4]
    simp [Ideal.setBool]
  -- the tail
  have hA : runLocal E [(.fieldPublic ⟨f0⟩ (ofNat 1) : Instr), .fieldPublic ⟨f0 + 1⟩ (ofNat 0)] I4 =
      some ((I4.setField ⟨f0⟩ (ofNat 1)).setField ⟨f0 + 1⟩ (ofNat 0)) := by
    simp [runLocal, localStep, idealStep, TlsMpc.Node.Flows.Contacts.blankWire, InstrP.map]
  have hI5 : ∀ j, j ≠ f0 → j ≠ f0 + 1 →
      ((I4.setField ⟨f0⟩ (ofNat 1)).setField ⟨f0 + 1⟩ (ofNat 0)).fields j = I.fields j := by
    intro j h0 h1
    simp only [Ideal.setField]
    rw [if_neg h1, if_neg h0, hI4f]
  have hI5a : ((I4.setField ⟨f0⟩ (ofNat 1)).setField ⟨f0 + 1⟩ (ofNat 0)).fields f0 = some (ofNat 1) := by
    simp [Ideal.setField]
  have hI5b : ((I4.setField ⟨f0⟩ (ofNat 1)).setField ⟨f0 + 1⟩ (ofNat 0)).fields (f0 + 1) = some (ofNat 0) := by
    simp [Ideal.setField]
  -- the subtractions as triples
  have hS : (ps.zipIdx.map fun e =>
      if ((List.range ps.length).map (fun i => (xb.getD i false ^^ ρ.getD i false))).getD e.2 false then
        (.fieldSub ⟨f0 + 2 + e.2⟩ ⟨f0⟩ e.1.field : Instr)
      else .fieldSub ⟨f0 + 2 + e.2⟩ e.1.field ⟨f0 + 1⟩) =
      (ps.zipIdx.map fun e =>
        if ((List.range ps.length).map (fun i => (xb.getD i false ^^ ρ.getD i false))).getD e.2 false then
          ((⟨f0 + 2 + e.2⟩, ⟨f0⟩, e.1.field) : FieldH × FieldH × FieldH)
        else (⟨f0 + 2 + e.2⟩, e.1.field, ⟨f0 + 1⟩)).map fun t => (.fieldSub t.1 t.2.1 t.2.2 : Instr) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro e _
    simp only [Function.comp_apply]
    split <;> rfl
  have hmemT : ∀ t ∈ (ps.zipIdx.map fun e =>
        if ((List.range ps.length).map (fun i => (xb.getD i false ^^ ρ.getD i false))).getD e.2 false then
          ((⟨f0 + 2 + e.2⟩, ⟨f0⟩, e.1.field) : FieldH × FieldH × FieldH)
        else (⟨f0 + 2 + e.2⟩, e.1.field, ⟨f0 + 1⟩)),
      ∃ i, i < ps.length ∧ t.1.id = f0 + 2 + i ∧
        ((t.2.1.id = f0 ∧ t.2.2.id = (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field.id) ∨
          (t.2.1.id = (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field.id ∧ t.2.2.id = f0 + 1)) := by
    intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨e, he, rfl⟩ := ht
    obtain ⟨-, h2, h3⟩ := mem_zipIdx' (⟨⟨0⟩, ⟨0⟩⟩ : BitPair) ps 0 e he
    rw [Nat.sub_zero] at h3
    refine ⟨e.2, by omega, ?_, ?_⟩
    · split <;> rfl
    · rw [h3]
      split
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
  obtain ⟨I6, g1, g2, g3, g4⟩ := runLocal_subs E _ ((I4.setField ⟨f0⟩ (ofNat 1)).setField ⟨f0 + 1⟩ (ofNat 0))
    (by
      rw [List.map_map]
      have e : (ps.zipIdx.map ((fun t : FieldH × FieldH × FieldH => t.1.id) ∘ fun e =>
          if ((List.range ps.length).map (fun i => (xb.getD i false ^^ ρ.getD i false))).getD e.2 false then
            ((⟨f0 + 2 + e.2⟩, ⟨f0⟩, e.1.field) : FieldH × FieldH × FieldH)
          else (⟨f0 + 2 + e.2⟩, e.1.field, ⟨f0 + 1⟩))) = List.range' (f0 + 2) ps.length := by
        have e' : (ps.zipIdx.map ((fun t : FieldH × FieldH × FieldH => t.1.id) ∘ fun e =>
            if ((List.range ps.length).map (fun i => (xb.getD i false ^^ ρ.getD i false))).getD e.2 false then
              ((⟨f0 + 2 + e.2⟩, ⟨f0⟩, e.1.field) : FieldH × FieldH × FieldH)
            else (⟨f0 + 2 + e.2⟩, e.1.field, ⟨f0 + 1⟩))) = ps.zipIdx.map (fun e => f0 + 2 + e.2) := by
          apply List.map_congr_left
          intro e _
          simp only [Function.comp_apply]
          split <;> rfl
        rw [e', List.zipIdx_eq_zip_range']
        apply List.ext_getElem <;> simp
      rw [e]
      exact List.nodup_range')
    (fun t ht t' ht' => by
      obtain ⟨i, hi, e1, -⟩ := hmemT t ht
      obtain ⟨j, hj, -, e2⟩ := hmemT t' ht'
      obtain ⟨n1, n2, n3⟩ := hfid j hj
      have := n3 i hi
      rcases e2 with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · rw [e1, a1, a2]
        exact ⟨by omega, fun h => this h.symm⟩
      · rw [e1, a1, a2]
        exact ⟨fun h => this h.symm, by omega⟩)
    (fun t ht => by
      obtain ⟨i, hi, -, e2⟩ := hmemT t ht
      obtain ⟨n1, n2, -⟩ := hfid i hi
      have hp : ((I4.setField ⟨f0⟩ (ofNat 1)).setField ⟨f0 + 1⟩ (ofNat 0)).fields
          (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field.id = some (X25519.bitValue (ρ.getD i false)) := by
        rw [hI5 _ n1 n2]
        exact hflds i hi
      rcases e2 with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · rw [a1, a2, hI5a, hp]
        exact ⟨rfl, rfl⟩
      · rw [a1, a2, hI5b, hp]
        exact ⟨rfl, rfl⟩)
  -- the frees
  obtain ⟨I7, k1, k2, -⟩ := TlsMpc.Node.Flows.Masks.runLocal_frees E
    ([⟨n0⟩, ⟨n0 + 1⟩, ⟨n0 + 2⟩, ⟨n0 + 3⟩] ++ ps.map (·.bit)) I6
  obtain ⟨I8, m1, m2⟩ := runLocal_freeFields E (ps.map (·.field)) I7
  obtain ⟨I9, r1, r2⟩ := runLocal_freeFields E [⟨f0⟩, ⟨f0 + 1⟩] I8
  have htail : runLocal E (b2fTail n0 f0 ((List.range ps.length).map (fun i => (xb.getD i false ^^ ρ.getD i false))) ps)
      I4 = some I9 := by
    have hFF : ps.map (fun q => (.freeField q.field : Instr)) =
        (ps.map (·.field)).map fun h => (.freeField h : Instr) := by
      rw [List.map_map]
      rfl
    rw [b2fTail, runLocal_append, runLocal_append, runLocal_append, runLocal_append, hA]
    simp only [Option.bind_some]
    rw [hS, g1]
    simp only [Option.bind_some]
    rw [k1]
    simp only [Option.bind_some]
    rw [hFF, m1]
    simp only [Option.bind_some]
    exact r1
  refine ⟨I9, ?_, fun i hi => ?_⟩
  · unfold bitsToField
    refine jret_locals E _ _ σA σB _ _ I9 σA σB _ (fun i hi => by
      simp only [b2fBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> rfl) I I4 hblock ?_
    refine jret_openThen E ⟨n0 + 3⟩ _ _ _ σA σB I4 _ _ _ I9 σA σB hI4o ?_
    rw [if_pos (by rw [List.length_map, List.length_range])]
    refine jret_locals E _ _ σA σB _ _ I9 σA σB _ (b2fTail_local n0 f0 _ ps) I4 I9 htail ?_
    exact jret_done E _ _ σA σB I9
  · obtain ⟨n1, n2, n3⟩ := hfid i hi
    have hne : ∀ h ∈ ps.map (·.field), h.id ≠ f0 + 2 + i := by
      intro h hh
      simp only [List.mem_map] at hh
      obtain ⟨q, hq, rfl⟩ := hh
      obtain ⟨j, hj, hqj⟩ : ∃ j, j < ps.length ∧ ps.getD j ⟨⟨0⟩, ⟨0⟩⟩ = q := by
        obtain ⟨j, hj, e⟩ := List.getElem_of_mem hq
        exact ⟨j, hj, by simp [List.getD_eq_getElem?_getD, hj, e]⟩
      rw [← hqj]
      exact (hfid j hj).2.2 i hi
    rw [r2 _ (by
        intro h hh
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        rcases hh with rfl | rfl <;> (dsimp only; omega)),
      m2 _ hne, k2]
    -- the subtraction of pair i
    have hmem := zipIdx_mem' (⟨⟨0⟩, ⟨0⟩⟩ : BitPair) ps 0 i hi
    rw [Nat.zero_add] at hmem
    have ho : ((List.range ps.length).map (fun i => (xb.getD i false ^^ ρ.getD i false))).getD i false =
        (xb.getD i false ^^ ρ.getD i false) := getD_map_range _ _ _ _ hi
    have hp : ((I4.setField ⟨f0⟩ (ofNat 1)).setField ⟨f0 + 1⟩ (ofNat 0)).fields
        (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field.id = some (X25519.bitValue (ρ.getD i false)) := by
      rw [hI5 _ n1 n2]
      exact hflds i hi
    have hval := b2f_value (xb.getD i false) (ρ.getD i false)
    by_cases hc : (xb.getD i false ^^ ρ.getD i false) = true
    · have := g3 (⟨f0 + 2 + i⟩, ⟨f0⟩, (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field) (by
        simp only [List.mem_map]
        exact ⟨(ps.getD i ⟨⟨0⟩, ⟨0⟩⟩, i), hmem, by simp only [ho, hc, if_true]⟩)
      rw [hc, if_pos rfl] at hval
      show I6.fields (f0 + 2 + i) = _
      rw [this, hI5a, hp, ← hval]
      rfl
    · have hc' : (xb.getD i false ^^ ρ.getD i false) = false := by simpa using hc
      have := g3 (⟨f0 + 2 + i⟩, (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field, ⟨f0 + 1⟩) (by
        simp only [List.mem_map]
        exact ⟨(ps.getD i ⟨⟨0⟩, ⟨0⟩⟩, i), hmem, by simp only [ho, hc', Bool.false_eq_true, if_false]⟩)
      rw [hc', if_neg (by simp)] at hval
      show I6.fields (f0 + 2 + i) = _
      rw [this, hp, hI5b, ← hval]
      rfl

end B2F

end TlsMpc.Node.Flows.Convert
