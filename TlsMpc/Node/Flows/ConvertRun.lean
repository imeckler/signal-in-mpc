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

end TlsMpc.Node.Flows.Convert
