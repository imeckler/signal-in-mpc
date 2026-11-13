import TlsMpc.Node.Flows.MasksHiding

/-!
# P-CUT (f), (g) at run level: the flags and the bit blocks, against any adversary

REORGANIZATION_PLAN.md 7.1 P-CUT (f), (g); stage S10. `MasksProofs.lean` has the protocol layer
(`finalizeMask_flag`, `finalizeBits_flag`, `bitBlock_unique`, `bitCheck_zero_iff`); `MasksRun.lean`
has the run level of (d) and (e) (`cutPhase_sound`, `bucketPhase_sound`). This file does the same
for the last phase:

  `finishPhase_sound`: in any run of `finishPhase` against any adversary, from any engine state
  that holds the candidates `x` (`Holds`): IF THE RUN RETURNS a pool, then
    * (f) every kept reference of BOTH owners is canonical, and those of the bit blocks are at
      least 32 (`flags_all`);
    * the pool is `maskList`, `pairList`, and in the final engine state every word mask's Boolean
      handle holds `modAdd` of the two references' words and its field handle the sum of their
      field values;
    * (g) [with `FieldInverse`] for every bit block whose two references have error 0, every bit
      pair's Boolean handle holds the XOR of the two references' bits and its field handle the
      field bit of that XOR.
  `mask_consistent`: so a word mask whose two references have error 0 is CONSISTENT: the value of
  its word is its field value (`val(w) = f`), which is `(val_A + val_B) mod p`.

"Error 0 of the kept references" is what the cut and the buckets establish except with the
counting model's probability (`MasksModel.lean`); for an honest party it is true of its own
references (`honest_ok`).
-/

namespace TlsMpc.Node.Flows.Masks

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees Silent blankWire Leaves seqs_cons seqs_nil)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Conv
open TlsMpc.FieldDag (F modulus)
open TlsMpc.FieldDag.V3 (FieldInverse)

/-! ## (f) What the flags say -/

/-- **P-CUT (f), the flags' meaning for a kept reference**: if every opened flag is set, both
owners' references are canonical, and for a bit block both are at least 32. -/
theorem flags_all {x : Vals} (hx : x.Wide) (p : Params) (π₁ π₂ : List Nat)
    (hall : (flagsOf p π₁ π₂ x).all id = true) (j : Nat) (hj : j < p.N) :
    x.val 0 (refOf p π₁ π₂ j) < P ∧ x.val 1 (refOf p π₁ π₂ j) < P ∧
      (j < p.bits → 32 ≤ x.val 0 (refOf p π₁ π₂ j) ∧ 32 ≤ x.val 1 (refOf p π₁ π₂ j)) := by
  have hmem : (outOf p π₁ π₂ x j).getD 255 false ∈ flagsOf p π₁ π₂ x :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  have ht := (flagsOk_iff _).mp hall _ hmem
  unfold outOf pairOf at ht
  show natOf (x.bits 0 _) < P ∧ natOf (x.bits 1 _) < P ∧ (j < p.bits → 32 ≤ natOf (x.bits 0 _) ∧ 32 ≤ natOf (x.bits 1 _))
  split at ht
  · rw [finalizeBits_flag _ _ (hx 0 _) (hx 1 _)] at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    exact ⟨ht.1.1.1, ht.1.1.2, fun _ => ⟨ht.1.2, ht.2⟩⟩
  · next hb =>
    rw [finalizeMask_flag _ _ (hx 0 _) (hx 1 _)] at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    exact ⟨ht.1, ht.2, fun h => absurd h hb⟩

/-! ## Bits of the bundle -/

theorem finalizeBits_bit (a b : Bits) (ha : a.length = W) (hb : b.length = W) (i : Nat) (hi : i < 255) :
    (finalizeBitsEval (a ++ b)).getD i false = (a.getD i false ^^ b.getD i false) := by
  have h := finalizeBits_word a b ha hb
  have e : (finalizeBitsEval (a ++ b)).getD i false = ((finalizeBitsEval (a ++ b)).take 255).getD i false := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  rw [e, h, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by rw [ha]; exact hi), List.getElem?_eq_getElem (by rw [hb]; exact hi)]
  rfl

theorem drop_take_one {α : Type} (l : List α) (n : Nat) (d : α) (h : n < l.length) :
    (l.drop n).take 1 = [l.getD n d] := by
  apply List.ext_getElem
  · simp
    omega
  · intro i h1 h2
    have hi : i = 0 := by simp at h2; omega
    subst hi
    simp [List.getD_eq_getElem?_getD, h]

theorem isSome_getD {α : Type} (o : Option α) (d : α) (h : o.isSome = true) : o = some (o.getD d) := by
  cases o with
  | none => cases h
  | some a => rfl

theorem bitZ_nil (p : Params) (π₁ π₂ : List Nat) (κ : Nat → Nat → Nat → F) (x : Vals) (hb0 : p.bits = 0) :
    bitZ p π₁ π₂ κ x = [] := by
  unfold bitZ
  rw [hb0, owners_flatMap, owners_flatMap, List.range_zero]
  rfl

/-! ## The coin inputs of one run -/

/-- One run after the coin inputs of the first `k` bit blocks: every coin handle of both owners
holds a value; nothing below the coins changed. -/
structure CoinsIn (p : Params) (f : Nat) (I0 I : Ideal) (k : Nat) : Prop where
  some : ∀ o, o < 2 → ∀ j, j < k → ∀ i, i < W → (I.fields (coinH p f o j i).id).isSome = true
  low : ∀ id, id < coinBase p f → I.fields id = I0.fields id
  bools : I.bools = I0.bools

section Sound

variable (E : Env) (me : Party) (adv : Adversary) (p : Params) (b f : Nat)

theorem coin_inputs_ret {α : Type} (s : Slots) (π₁ π₂ : List Nat) (rest : Script α) (σ : Store) (x : α)
    (J I0 : Ideal) :
    ∀ n, n ≤ p.bits → ∀ (I : Ideal) (vD : List Release), CoinsIn p f I0 I (p.bits - n) →
      Ret (withAdv E me adv (seqs ((List.range' (p.bits - n) n).map fun j =>
        (.fieldInput ((List.range W).map (coinH p f 0 j)) ((List.range W).map (coinH p f 1 j)) .coins false
          (s.coins + member p π₁ π₂ j 0) : Instr)) rest) σ I vD) x J →
      ∃ I' vD', CoinsIn p f I0 I' p.bits ∧ Ret (withAdv E me adv rest σ I' vD') x J
  | 0, _, I, vD, hinv, h => by
    simp only [List.range'_zero, List.map_nil, seqs_nil] at h
    exact ⟨I, vD, by simpa using hinv, h⟩
  | n + 1, hn, I, vD, hinv, h => by
    have e : List.range' (p.bits - (n + 1)) (n + 1) = (p.bits - (n + 1)) :: List.range' (p.bits - n) n := by
      rw [List.range'_succ]
      congr 1
      congr 1
      omega
    rw [e, List.map_cons, seqs_cons] at h
    have hj : p.bits - (n + 1) < p.bits := by omega
    obtain ⟨pe, hpe, hl, hk⟩ := ret_fieldInput E me adv _ _ _ _ _ _ σ I vD x J (by simp) h
    have hpe' : pe.length = W := by simpa using hpe
    have hl' : (σ.elems (s.coins + member p π₁ π₂ (p.bits - (n + 1)) 0)).length = W := by simpa using hl
    obtain ⟨s1, s2, s3, s4⟩ := coin_step p f me I _ hj _ pe hl' hpe'
    refine coin_inputs_ret s π₁ π₂ rest σ x J I0 n (by omega) _ vD ⟨?_, ?_, ?_⟩ hk
    · intro o ho j hjn i hi
      by_cases hjk : j = p.bits - (n + 1)
      · subst hjk
        by_cases ho' : o = own me
        · subst ho'
          rw [s2 i hi]
          rfl
        · have e : o = 1 - own me := by have := own_lt me; omega
          subst e
          rw [s3 i hi]
          rfl
      · rw [s4 _ (coin_frame p f o j _ i ho (by omega) hj hi)]
        exact hinv.some o ho j (by omega) i hi
    · intro id hid
      rw [s4 id (Or.inl (by omega))]
      exact hinv.low id hid
    · rw [s1]
      exact hinv.bools

/-- **The bit-block phase of a run that returned**: there are coins `κ` (what the two parties
input) for which everything the phase opened (`bitZ`) is 0, the bit pairs' Boolean handles are the
one-bit slices of the bundle and their field handles the field XOR of the coins; nothing else
relevant changed. -/
theorem bitPhase_ret (hP : ProgsLoaded E) (s : Slots) (π₁ π₂ : List Nat) (σ : Store) (I5 : Ideal)
    (vD : List Release) (x : Vals) (bundle : Bits) (u : Unit) (J : Ideal)
    (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M)
    (hfld : ∀ o, o < 2 → ∀ c, c < p.M → I5.fields (fOf p f o c).id = some (x.elem o c))
    (hb : I5.bools (b + 10) = some bundle) (hlen : bundle.length = p.N * 256) (hbits : p.bits ≤ p.N)
    (h : Ret (withAdv E me adv (bitPhase p b f s π₁ π₂) σ I5 vD) u J) :
    ∃ κ : Nat → Nat → Nat → F, (∀ z ∈ bitZ p π₁ π₂ κ x, z = 0) ∧
      (∀ id, id < bitBase p b → J.bools id = I5.bools id) ∧
      (∀ id, id < coinBase p f → J.fields id = I5.fields id) ∧
      (∀ j, j < p.bits → ∀ i, i < W →
        J.bools (bitBase p b + j * W + i) = some ((bundle.drop (256 * j + i)).take 1) ∧
        J.fields (xorH p f (j * W + i)).id = some (xorVal κ j i)) := by
  have hml := member_lt p π₁ π₂ hπ₁ hM
  unfold bitPhase at h
  split at h
  · next hb0 =>
    obtain ⟨-, rfl⟩ := ret_done E me adv _ σ I5 vD u J h
    refine ⟨fun _ _ _ => 0, ?_, fun _ _ => rfl, fun _ _ => rfl, fun j hj => absurd hj (by omega)⟩
    intro z hz
    rw [bitZ_nil p π₁ π₂ _ x hb0] at hz
    cases hz
  · unfold coinInputs at h
    rw [List.range_eq_range' (n := p.bits)] at h
    have h' : Ret (withAdv E me adv (seqs ((List.range' (p.bits - p.bits) p.bits).map fun j =>
        (.fieldInput ((List.range W).map (coinH p f 0 j)) ((List.range W).map (coinH p f 1 j)) .coins false
          (s.coins + member p π₁ π₂ j 0) : Instr))
        (seq (.program recomposeName (2 * p.bits) (recIns p f π₁ π₂) [] (recOuts p f) Label.bitBlockChecks) <|
          seq (.program bitCheckName (2 * (p.bits * W)) (allCoins p f) [] (chkOuts p f) Label.bitBlockChecks) <|
          openFieldThen (recOuts p f ++ chkOuts p f) Label.bitBlockChecks fun z =>
          if z.all (· == 0) then
            seq (.program bitXorName (p.bits * W) (xorIns p f) [] (xorOuts p f) Label.bitBlockChecks) <|
            seqs (pairSlices p b) (.done ())
          else .abort "bit block inconsistent with verified reference")) σ I5 vD) u J := by
      rw [Nat.sub_self]
      exact h
    obtain ⟨I6, vD6, hin, r0⟩ := coin_inputs_ret E me adv p f s π₁ π₂ _ σ u J I5 p.bits (Nat.le_refl _) I5 vD
      ⟨fun o _ j hj => absurd hj (by omega), fun _ _ => rfl, rfl⟩ h'
    have hbase : f + 2 * p.M ≤ coinBase p f := by
      unfold coinBase maskBase
      omega
    have hc : CoinsHold p f I6 (fun o j i => (I6.fields (coinH p f o j i).id).getD 0) :=
      fun o ho j hj i hi => isSome_getD _ _ (hin.some o ho j hj i hi)
    obtain ⟨pr, vi, vo, pc, vi2, vo2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
      coins_programs E hP p f π₁ π₂ I6 _ x hc (fun o ho j _ => by
        rw [hin.low _ (by have := fOf_id_lt p f o _ ho (hml j 0); unfold refOf; omega)]
        exact hfld o ho _ (hml j 0))
    -- the recomposition
    obtain ⟨pr', vi', vm', vo', op', vD7, e1, e2, e3, e4, r1⟩ := ret_program E me adv _ _ _ _ _ _ _ σ _ _ u J r0
    have epr : pr' = pr := Option.some.inj (e1.symm.trans q1)
    have evi : vi' = vi := Option.some.inj (e2.symm.trans q2)
    have evm : vm' = [] := by simpa using e3.symm
    subst epr evi evm
    have evo : vo' = vo := (Prod.mk.inj (Option.some.inj (e4.symm.trans q3))).1
    subst evo
    -- the bit checks
    obtain ⟨pc', vi2', vm2', vo2', op2', vD8, e5, e6, e7, e8, r2⟩ := ret_program E me adv _ _ _ _ _ _ _ σ _ _ u J r1
    have epc : pc' = pc := Option.some.inj (e5.symm.trans q5)
    have evi2 : vi2' = vi2 := Option.some.inj (e6.symm.trans q6)
    have evm2 : vm2' = [] := by simpa using e7.symm
    subst epc evi2 evm2
    have evo2 : vo2' = vo2 := (Prod.mk.inj (Option.some.inj (e8.symm.trans q7))).1
    subst evo2
    -- the opening and the check
    obtain ⟨z, vD9, ez, r3⟩ := ret_openFieldThen E me adv _ _ _ σ _ _ u J r2
    have hz : z = bitZ p π₁ π₂ (fun o j i => (I6.fields (coinH p f o j i).id).getD 0) x :=
      Option.some.inj (ez.symm.trans q9)
    obtain ⟨hall, r4⟩ := ret_ite E me adv _ _ _ σ _ _ u J r3
    -- the XOR and the slices
    have hcJ : CoinsHold p f ((I6.setFields (recOuts p f) vo').setFields (chkOuts p f) vo2')
        (fun o j i => (I6.fields (coinH p f o j i).id).getD 0) := by
      intro o ho j hj i hi
      rw [q11 _ (by have := coin_lt p o j i ho hj hi; rw [coin_id]; omega)]
      exact hc o ho j hj i hi
    obtain ⟨px, wi, wo, x1, x2, x3, x4, x5, x6, x7⟩ := coins_xor E hP p f _ _ hcJ
    obtain ⟨px', wi', wm', wo', op3', vD10, e9, e10, e11, e12, r5⟩ :=
      ret_program E me adv _ _ _ _ _ _ _ σ _ _ u J r4
    have epx : px' = px := Option.some.inj (e9.symm.trans x1)
    have ewi : wi' = wi := Option.some.inj (e10.symm.trans x2)
    have ewm : wm' = [] := by simpa using e11.symm
    subst epx ewi ewm
    have ewo : wo' = wo := (Prod.mk.inj (Option.some.inj (e12.symm.trans x3))).1
    subst ewo
    obtain ⟨J', y1, y2, y3, y4⟩ := pairSlices_block E p b
      (((I6.setFields (recOuts p f) vo').setFields (chkOuts p f) vo2').setFields (xorOuts p f) wo') bundle
      (by rw [x5, q10, hin.bools]; exact hb) hlen hbits
    obtain ⟨J'', y1', r6⟩ := ret_locals E me adv _ σ u J _ (pairSlices_local p b) _ _ r5
    have eJ : J'' = J' := Option.some.inj (y1'.symm.trans y1)
    subst eJ
    obtain ⟨-, rfl⟩ := ret_done E me adv _ σ _ _ u J r6
    refine ⟨fun o j i => (I6.fields (coinH p f o j i).id).getD 0, ?_, fun id hid => ?_, fun id hid => ?_,
      fun j hj i hi => ⟨y3 j hj i hi, ?_⟩⟩
    · intro z' hz'
      rw [← hz] at hz'
      have := List.all_eq_true.mp hall z' hz'
      simpa using this
    · rw [y4 id hid, x5, q10, hin.bools]
    · rw [y2, x7 id (by omega), q11 id (by omega), hin.low id hid]
    · rw [y2]
      exact x6 j hj i hi

/-- **P-CUT (f) and (g) at run level.** Against any adversary and from any engine state that holds
the candidates `x`: if `finishPhase` returns a pool, then every kept reference of both owners is
canonical (at least 32 for the bit blocks); the pool is `maskList` / `pairList`; every word mask's
handles hold `modAdd` of the references' words and the sum of their field values; and (with
`FieldInverse`) every bit pair of a bit block whose two references have error 0 holds the XOR of
the two references' bits, in both engines. -/
theorem finishPhase_sound (hinv : FieldInverse) (hW : WordLoaded E) (hP : ProgsLoaded E) (s : Slots)
    (π₁ π₂ : List Nat) (σ : Store) (I : Ideal) (vD : List Release) (v : Bits) (x : Vals) (pool : MaskPool)
    (h : Holds p b f I v x) (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M) (hbits : p.bits ≤ p.N)
    (hres : (withAdv E me adv (finishPhase p b f s π₁ π₂) σ I vD).result = some pool) :
    pool = ⟨maskList p b f, pairList p b f⟩ ∧
    (∀ j, j < p.N → x.val 0 (refOf p π₁ π₂ j) < P ∧ x.val 1 (refOf p π₁ π₂ j) < P ∧
      (j < p.bits → 32 ≤ x.val 0 (refOf p π₁ π₂ j) ∧ 32 ≤ x.val 1 (refOf p π₁ π₂ j))) ∧
    (∀ j, j < p.words →
      (withAdv E me adv (finishPhase p b f s π₁ π₂) σ I vD).ideal.bools (b + 12 + j) =
        some (word (addModSpec (x.val 0 (refOf p π₁ π₂ (p.bits + j))) (x.val 1 (refOf p π₁ π₂ (p.bits + j))))) ∧
      (withAdv E me adv (finishPhase p b f s π₁ π₂) σ I vD).ideal.fields (maskBase p f + j) =
        some (x.elem 0 (refOf p π₁ π₂ (p.bits + j)) + x.elem 1 (refOf p π₁ π₂ (p.bits + j)))) ∧
    (∀ j, j < p.bits → x.err 0 (refOf p π₁ π₂ j) = 0 → x.err 1 (refOf p π₁ π₂ j) = 0 → ∀ i, i < W →
      (withAdv E me adv (finishPhase p b f s π₁ π₂) σ I vD).ideal.bools (bitBase p b + j * W + i) =
        some [(x.bits 0 (refOf p π₁ π₂ j)).getD i false ^^ (x.bits 1 (refOf p π₁ π₂ j)).getD i false] ∧
      (withAdv E me adv (finishPhase p b f s π₁ π₂) σ I vD).ideal.fields (xorH p f (j * W + i)).id =
        some (X25519.bitValue
          ((x.bits 0 (refOf p π₁ π₂ j)).getD i false ^^ (x.bits 1 (refOf p π₁ π₂ j)).getD i false))) := by
  have hml := member_lt p π₁ π₂ hπ₁ hM
  have hwide := h.wide
  have hret : Ret (withAdv E me adv (finishPhase p b f s π₁ π₂) σ I vD) pool
      (withAdv E me adv (finishPhase p b f s π₁ π₂) σ I vD).ideal := ⟨hres, rfl⟩
  generalize (withAdv E me adv (finishPhase p b f s π₁ π₂) σ I vD).ideal = J at hret ⊢
  obtain ⟨I4, f1, f2, f3, f4⟩ := h.final E hW π₁ π₂ hπ₁ hM hbits
  unfold finishPhase at hret
  obtain ⟨I4', e1, r1⟩ := ret_locals E me adv _ σ pool J _ (finalBlock_local p b π₁ π₂) I vD hret
  have eI4 : I4' = I4 := Option.some.inj (e1.symm.trans f1)
  subst eI4
  obtain ⟨fl, vD2, hfl, r2⟩ := ret_openThen E me adv _ _ _ σ _ _ pool J r1
  have efl : fl = flagsOf p π₁ π₂ x := Option.some.inj (hfl.symm.trans f4)
  subst efl
  obtain ⟨hall, r3⟩ := ret_ite E me adv _ _ _ σ _ _ pool J r2
  have hflags := flags_all hwide p π₁ π₂ hall
  have houts := outsOf_length_each hwide p π₁ π₂
  have hoN : (outsOf p π₁ π₂ x).length = p.N := by simp [outsOf]
  have hl : (outsOf p π₁ π₂ x).flatten.length = p.N * 256 := by
    rw [length_flatten_eq 256 _ houts, hoN]
  obtain ⟨I5, m1, m2, m3, m4, m5, m6, m7⟩ := masks_block E p b f π₁ π₂ I4' x _ f3 hl hbits
    (fun o ho c hc => by rw [f2]; exact h.hfld o ho c hc) hπ₁ hM
  obtain ⟨I5', e2, r4⟩ := ret_locals E me adv _ σ pool J _ (maskBlock_local p b f π₁ π₂) _ _ r3
  have eI5 : I5' = I5 := Option.some.inj (e2.symm.trans m1)
  subst eI5
  obtain ⟨u, vD3, hu, r5⟩ := ret_bind E me adv _ _ σ _ _ pool J r4
  obtain ⟨hpool, hJ⟩ := ret_done E me adv _ _ _ _ pool J r5
  have hmb : f + 2 * p.M ≤ maskBase p f := by unfold maskBase; omega
  obtain ⟨κ, k1, k2, k3, k4⟩ := bitPhase_ret E me adv p b f hP s π₁ π₂ σ I5' vD2 x _ u J hπ₁ hM
    (fun o ho c hc => by
      rw [m5 _ (by have := fOf_id_lt p f o c ho hc; omega), f2]
      exact h.hfld o ho c hc)
    m2 hl hbits ⟨hu, hJ.symm⟩
  refine ⟨hpool, hflags, fun j hj => ⟨?_, ?_⟩, fun j hj he0 he1 i hi => ?_⟩
  · -- the word of mask j
    rw [k2 _ (by unfold bitBase; omega), m3 j hj]
    have hjN : p.bits + j < (outsOf p π₁ π₂ x).length := by
      rw [hoN]
      have : p.words = p.N - p.bits := rfl
      omega
    have hch := flatten_drop_take 256 (outsOf p π₁ π₂ x) (p.bits + j) houts hjN
    rw [Nat.mul_comm] at hch
    have e : ((outsOf p π₁ π₂ x).flatten.drop (256 * (p.bits + j))).take 255 =
        (((outsOf p π₁ π₂ x).flatten.drop (256 * (p.bits + j))).take 256).take 255 := by
      rw [List.take_take]
      rfl
    have eo : (outsOf p π₁ π₂ x).getD (p.bits + j) [] = outOf p π₁ π₂ x (p.bits + j) :=
      getD_map_range _ _ _ _ (by rw [← hoN]; exact hjN)
    rw [e, hch, eo]
    unfold outOf
    rw [if_neg (by omega)]
    unfold pairOf
    rw [finalizeMask_word _ _ (hwide 0 _) (hwide 1 _)]
    rfl
  · rw [k3 _ (by unfold coinBase; omega), m4 j hj]
  · -- a bit pair
    have hjN : j < p.N := by omega
    obtain ⟨c0, c1, c32⟩ := hflags j hjN
    obtain ⟨g0, g1⟩ := c32 hj
    have hmc := hml j 0
    -- the coins are the references' bits
    have hκ : ∀ o, o < 2 → x.val o (refOf p π₁ π₂ j) < P → 32 ≤ x.val o (refOf p π₁ π₂ j) →
        x.err o (refOf p π₁ π₂ j) = 0 → κ o j i = X25519.bitValue ((x.bits o (refOf p π₁ π₂ j)).getD i false) := by
      intro o ho hc h32 herr
      have hoo : o ∈ owners := by
        simp only [owners, List.mem_cons, List.not_mem_nil, or_false]
        omega
      have hrec : recVal p π₁ π₂ κ x o j = 0 := k1 _ (by
        unfold bitZ
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨o, hoo, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩))
      have hchk : ∀ c ∈ (List.range 255).map (κ o j), c * (c - TlsMpc.FieldDag.ofNat 1) = 0 := by
        intro c hc'
        simp only [List.mem_map, List.mem_range] at hc'
        obtain ⟨i', hi', rfl⟩ := hc'
        exact k1 _ (by
          unfold bitZ
          exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, hoo, List.mem_flatMap.mpr
            ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨i', List.mem_range.mpr hi', rfl⟩⟩⟩))
      have huniq := bitBlock_unique hinv ((List.range 255).map (κ o j)) (x.bits o (refOf p π₁ π₂ j))
        (x.elem o (refOf p π₁ π₂ j)) (by simp) (hwide o _) hchk hrec
        ((err_zero_iff x o _ hc).mp herr).symm (by have : x.val o (refOf p π₁ π₂ j) = natOf (x.bits o _) := rfl; omega)
        hc
      have e1 : κ o j i = ((List.range 255).map (κ o j)).getD i 0 := (getD_map_range _ _ _ _ hi).symm
      rw [e1, huniq]
      exact getD_map_lt _ _ _ _ _ (by rw [hwide o _]; exact hi)
    obtain ⟨kb, kf⟩ := k4 j hj i hi
    constructor
    · rw [kb, drop_take_one _ _ false (by rw [hl]; have : i < 255 := hi; omega)]
      have hg := flatten_getD 256 (outsOf p π₁ π₂ x) j i false houts (by rw [hoN]; exact hjN)
        (by have : i < 255 := hi; omega)
      rw [Nat.mul_comm] at hg
      have eo : (outsOf p π₁ π₂ x).getD j [] = outOf p π₁ π₂ x j := getD_map_range _ _ _ _ hjN
      rw [hg, eo]
      unfold outOf
      rw [if_pos hj]
      unfold pairOf
      rw [finalizeBits_bit _ _ (hwide 0 _) (hwide 1 _) i hi]
    · rw [kf]
      unfold xorVal
      rw [hκ 0 (by omega) c0 g0 he0, hκ 1 (by omega) c1 g1 he1, bitXorValue_bits]

end Sound

/-- **A word mask from two error-free references is consistent**: with both references canonical
(the flags) and of error 0, the value of the mask's word, `modAdd` of the two words, is the value
of its field element, the sum of the two field values: `val(w) = f = (val_A + val_B) mod p`. -/
theorem mask_consistent (x : Vals) (cA cB : Nat) (hA : x.val 0 cA < P) (hB : x.val 1 cB < P)
    (eA : x.err 0 cA = 0) (eB : x.err 1 cB = 0) :
    natOf (word (addModSpec (x.val 0 cA) (x.val 1 cB))) = (x.elem 0 cA + x.elem 1 cB).val ∧
      (x.elem 0 cA + x.elem 1 cB).val = (x.val 0 cA + x.val 1 cB) % P := by
  have h1 := (err_zero_iff x 0 cA hA).mp eA
  have h2 := (err_zero_iff x 1 cB hB).mp eB
  rw [addModSpec_canonical _ _ hA hB, natOf_word _ (by
    have := Nat.mod_lt (x.val 0 cA + x.val 1 cB) P_pos
    have := P_lt_two_pow
    omega), fadd_val, ← h1, ← h2]
  exact ⟨rfl, rfl⟩

end TlsMpc.Node.Flows.Masks
