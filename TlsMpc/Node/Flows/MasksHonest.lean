import TlsMpc.Node.Flows.MasksSound

/-!
# P-CUT (a): a whole honest run of `Masks.generate`, through `jointRun`

REORGANIZATION_PLAN.md 7.1 P-CUT (a); stage S10. `MasksProofs.lean` has the protocol layer
(`honest_ok`, `honest_mask`, `honest_pair`); the test vectors execute the model for the test
parameters. This file proves it for EVERY parameter set with `0 < M` and `bits ≤ N`, so for the
deployed profiles (`profile_ok`: `profile N bits` yields such a set):

  `generate_honest`: two honest parties, with candidates `rA`, `rB` in their stores
  (`HonestStore`), run `generate` in lockstep (`jointRun`). If the two challenges' commitments differ
  (else a hash collision), their expansions succeed (`permOf … = some π`; a failure has probability
  below 2⁻⁶⁴⁰ and aborts both alike), and every bit block's two references are at least 32 (else
  the flags abort the run; probability 64/p per block), then BOTH return the same pool
  `⟨maskList, pairList⟩`, the stores are unchanged, and in the final engine state
    * word mask `j` is `(word ((rA c + rB c) mod p), (rA c + rB c) mod p)` for its bucket's
      reference `c`: a Boolean word and a field element of the same value, the sum of the two
      parties' references mod p;
    * bit pair `(j, i)` is `(bit_i(rA c) ⊕ bit_i(rB c))` in both engines.
  `generate_honest_profile`: the same for `profile N bits = some p`.
-/

namespace TlsMpc.Node.Flows.Masks

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees Silent blankWire Leaves seqs_cons seqs_nil)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Conv
open TlsMpc.FieldDag (F modulus)

/-- The deployed profiles satisfy what the theorems ask of the parameters. -/
theorem profile_ok (N bits : Nat) (p : Params) (h : profile N bits = some p) : 0 < p.M ∧ p.bits ≤ p.N := by
  unfold profile at h
  split at h
  · next B hB =>
    split at h
    · next hle =>
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨?_, hle⟩
      unfold bucketFor at hB
      split at hB <;> first | (cases hB; simp [Params.M, Params.K]) | cases hB
    · cases h
  · cases h

/-! ## Both owners honest -/

/-- Both owners' candidates in the engines are honest: canonical `r2 o c`, as bits and as the
element. -/
structure BothHonest (p : Params) (r2 : Nat → Nat → Nat) (x : Vals) : Prop where
  bits : ∀ o, o < 2 → ∀ c, c < p.M → x.bits o c = word (r2 o c)
  elem : ∀ o, o < 2 → ∀ c, c < p.M → x.elem o c = TlsMpc.FieldDag.ofNat (r2 o c)
  canon : ∀ o, o < 2 → ∀ c, c < p.M → r2 o c < P

namespace BothHonest

variable {p : Params} {r2 : Nat → Nat → Nat} {x : Vals}

theorem ok (h : BothHonest p r2 x) (o c : Nat) (ho : o < 2) (hc : c < p.M) : x.val o c < P ∧ x.err o c = 0 :=
  honest_ok x o c (r2 o c) (h.canon o ho c hc) (h.bits o ho c hc) (h.elem o ho c hc)

theorem val (h : BothHonest p r2 x) (o c : Nat) (ho : o < 2) (hc : c < p.M) : x.val o c = r2 o c := by
  show natOf (x.bits o c) = _
  rw [h.bits o ho c hc, natOf_word _ (by have := h.canon o ho c hc; have := P_lt_two_pow; omega)]

/-- The cut check passes. -/
theorem cut (h : BothHonest p r2 x) (hw : x.Wide) (cut : List Nat) (hcut : ∀ c ∈ cut, c < p.M) :
    cutCheck ((cutRel x cut).map Prod.fst).flatten ((cutRel x cut).map Prod.snd) = true :=
  (cutCheck_iff x hw cut).mpr (fun o ho c hc => h.ok o c (owners_lt ho) (hcut c hc))

/-- The bucket check passes. -/
theorem bucket (h : BothHonest p r2 x) (mem : Nat → Nat → Nat) (ps : List (Nat × Nat × Nat))
    (hps : ∀ e ∈ ps, e.1 < 2 ∧ mem e.2.1 0 < p.M ∧ mem e.2.1 e.2.2 < p.M) :
    bucketCheck ((bucketRel x mem ps).map Prod.fst).flatten ((bucketRel x mem ps).map Prod.snd) = true :=
  (bucketCheck_iff x mem ps).mpr (fun e he => by
    obtain ⟨ho, h0, h1⟩ := hps e he
    obtain ⟨a1, a2⟩ := h.ok e.1 _ ho h0
    obtain ⟨b1, b2⟩ := h.ok e.1 _ ho h1
    rw [bucketOk_iff_canonical x e.1 _ _ a1 b1, a2, b2]
    rfl)

/-- Every flag is set (the bit blocks' references being at least 32). -/
theorem flags (h : BothHonest p r2 x) (hw : x.Wide) (π₁ π₂ : List Nat)
    (href : ∀ j, j < p.N → refOf p π₁ π₂ j < p.M)
    (h32 : ∀ j, j < p.bits → ∀ o, o < 2 → 32 ≤ r2 o (refOf p π₁ π₂ j)) :
    (flagsOf p π₁ π₂ x).all id = true := by
  rw [flagsOk_iff]
  intro y hy
  simp only [flagsOf, List.mem_map, List.mem_range] at hy
  obtain ⟨j, hj, rfl⟩ := hy
  have hc := href j hj
  have v0 := h.val 0 _ (by omega) hc
  have v1 := h.val 1 _ (by omega) hc
  have k0 := h.canon 0 (by omega) _ hc
  have k1 := h.canon 1 (by omega) _ hc
  simp only [Vals.val] at v0 v1
  unfold outOf pairOf
  split
  · next hjb =>
    rw [finalizeBits_flag _ _ (hw 0 _) (hw 1 _), v0, v1]
    simp [k0, k1, h32 j hjb 0 (by omega), h32 j hjb 1 (by omega)]
  · rw [finalizeMask_flag _ _ (hw 0 _) (hw 1 _), v0, v1]
    simp [k0, k1]

/-- Everything the bit-block phase opens is 0, for the honest coins. -/
theorem bitZ (h : BothHonest p r2 x) (π₁ π₂ : List Nat) (κ : Nat → Nat → Nat → F)
    (href : ∀ j, j < p.bits → refOf p π₁ π₂ j < p.M)
    (hκ : ∀ o, o < 2 → ∀ j, j < p.bits → ∀ i, i < W →
      κ o j i = X25519.bitValue ((word (r2 o (refOf p π₁ π₂ j))).getD i false)) :
    ∀ z ∈ Masks.bitZ p π₁ π₂ κ x, z = 0 := by
  intro z hz
  unfold Masks.bitZ at hz
  rw [List.mem_append] at hz
  rcases hz with hz | hz
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hz
    obtain ⟨o, ho, j, hj, rfl⟩ := hz
    have ho2 := owners_lt ho
    have e : (List.range 255).map (κ o j) =
        (List.range 255).map fun i => X25519.bitValue ((word (r2 o (refOf p π₁ π₂ j))).getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hκ o ho2 j hj i (List.mem_range.mp hi)
    unfold recVal
    rw [e, h.elem o ho2 _ (href j hj)]
    exact honest_rec _ (h.canon o ho2 _ (href j hj))
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hz
    obtain ⟨o, ho, j, hj, i, hi, rfl⟩ := hz
    unfold chkVal
    rw [hκ o (owners_lt ho) j hj i hi]
    exact bitValue_check _

end BothHonest

/-! ## Bits of the bundle -/

theorem bundle_mask_word {x : Vals} (hw : x.Wide) (p : Params) (π₁ π₂ : List Nat) (j : Nat) (hj : j < p.words) :
    ((outsOf p π₁ π₂ x).flatten.drop (256 * (p.bits + j))).take 255 =
      word (addModSpec (x.val 0 (refOf p π₁ π₂ (p.bits + j))) (x.val 1 (refOf p π₁ π₂ (p.bits + j)))) := by
  have houts := outsOf_length_each hw p π₁ π₂
  have hoN : (outsOf p π₁ π₂ x).length = p.N := by simp [outsOf]
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
  rw [finalizeMask_word _ _ (hw 0 _) (hw 1 _)]
  rfl

theorem bundle_pair_bit {x : Vals} (hw : x.Wide) (p : Params) (π₁ π₂ : List Nat) (hbits : p.bits ≤ p.N)
    (j i : Nat) (hj : j < p.bits) (hi : i < W) :
    ((outsOf p π₁ π₂ x).flatten.drop (256 * j + i)).take 1 =
      [(x.bits 0 (refOf p π₁ π₂ j)).getD i false ^^ (x.bits 1 (refOf p π₁ π₂ j)).getD i false] := by
  have houts := outsOf_length_each hw p π₁ π₂
  have hoN : (outsOf p π₁ π₂ x).length = p.N := by simp [outsOf]
  have hjN : j < p.N := by omega
  have hl : (outsOf p π₁ π₂ x).flatten.length = p.N * 256 := by
    rw [length_flatten_eq 256 _ houts, hoN]
  rw [drop_take_one _ _ false (by rw [hl]; have : i < 255 := hi; omega)]
  have hg := flatten_getD 256 (outsOf p π₁ π₂ x) j i false houts (by rw [hoN]; exact hjN)
    (by have : i < 255 := hi; omega)
  rw [Nat.mul_comm] at hg
  have eo : (outsOf p π₁ π₂ x).getD j [] = outOf p π₁ π₂ x j := getD_map_range _ _ _ _ hjN
  rw [hg, eo]
  unfold outOf
  rw [if_pos hj]
  unfold pairOf
  rw [finalizeBits_bit _ _ (hw 0 _) (hw 1 _) i hi]

/-! ## The phases, two honest parties -/

section Joint

variable (E : Env) (p : Params) (b f : Nat)

theorem cut_jret (π₁ : List Nat) (σA σB : Store) (I : Ideal) (v : Bits) (x : Vals) (h : Holds p b f I v x)
    (hπ : ∀ c ∈ cutOf p π₁, c < p.M)
    (hpass : cutCheck ((cutRel x (cutOf p π₁)).map Prod.fst).flatten ((cutRel x (cutOf p π₁)).map Prod.snd) = true) :
    ∃ I', JRet (jointRun E (cutPhase p b f π₁) (cutPhase p b f π₁) σA σB I) () () I' σA σB ∧ Holds p b f I' v x := by
  obtain ⟨c1, c2⟩ := h.cut E π₁ hπ
  refine ⟨(I.setBool ⟨b + 3⟩ ((cutRel x (cutOf p π₁)).map Prod.fst).flatten).dropBool ⟨b + 3⟩, ?_,
    h.frame (by simp [Ideal.setBool, Ideal.dropBool]) (fun _ _ => rfl)⟩
  unfold cutPhase
  refine jret_locals E _ _ σA σB () () _ σA σB [.pick ⟨b + 3⟩ ⟨b + 2⟩ (cutBits p π₁)] (by simp [isLocal]) I _ c1 ?_
  refine jret_openFieldThen E _ _ _ _ σA σB _ _ () () _ σA σB c2 ?_
  refine jret_openThen E ⟨b + 3⟩ _ _ _ σA σB _ ((cutRel x (cutOf p π₁)).map Prod.fst).flatten () () _ σA σB
    (by simp [Ideal.setBool]) ?_
  simp only [hpass, if_true]
  refine jret_locals E _ _ σA σB () () _ σA σB _ (by simp [isLocal]) _ _ (runLocal_free1 E _ _) ?_
  exact jret_done E () () σA σB _

theorem bucket_jret (hW : WordLoaded E) (π₁ π₂ : List Nat) (σA σB : Store) (I : Ideal) (v : Bits) (x : Vals)
    (h : Holds p b f I v x) (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M)
    (hpass : bucketCheck ((bucketRel x (member p π₁ π₂) (pairs p)).map Prod.fst).flatten
      ((bucketRel x (member p π₁ π₂) (pairs p)).map Prod.snd) = true) :
    ∃ I', JRet (jointRun E (bucketPhase p b f π₁ π₂) (bucketPhase p b f π₁ π₂) σA σB I) () () I' σA σB ∧
      Holds p b f I' v x := by
  obtain ⟨I3, g1, g2, g3, g4, g5⟩ := h.bucket E hW π₁ π₂ hπ₁ hM
  refine ⟨(I3.dropBool ⟨b + 4⟩).dropBool ⟨b + 5⟩, ?_, h.frame (by simp [Ideal.dropBool, g4]) g5⟩
  unfold bucketPhase
  refine jret_locals E _ _ σA σB () () _ σA σB _ (bucketBlock_local p b f π₁ π₂) I I3 g1 ?_
  refine jret_openFieldThen E _ _ _ _ σA σB _ _ () () _ σA σB g3 ?_
  refine jret_openThen E ⟨b + 5⟩ _ _ _ σA σB _ _ () () _ σA σB g2 ?_
  simp only [hpass, if_true]
  refine jret_locals E _ _ σA σB () () _ σA σB _ (by simp [isLocal]) _ _ (runLocal_free2 E _ _ _) ?_
  exact jret_done E () () σA σB _

/-- The engines after the coin inputs of the first `k` bit blocks (two honest parties): the
coins are `κ`. -/
structure CoinsAre (I0 I : Ideal) (κ : Nat → Nat → Nat → F) (k : Nat) : Prop where
  val : ∀ o, o < 2 → ∀ j, j < k → ∀ i, i < W → I.fields (coinH p f o j i).id = some (κ o j i)
  low : ∀ id, id < coinBase p f → I.fields id = I0.fields id
  bools : I.bools = I0.bools

theorem coin_inputs_jret {α β : Type} (sA sB : Slots) (π₁ π₂ : List Nat) (tA : Script α) (tB : Script β)
    (σA σB : Store) (a : α) (b' : β) (I0 : Ideal) (R : Ideal → Prop)
    (hstA : ∀ j, j < p.bits → (σA.elems (sA.coins + member p π₁ π₂ j 0)).length = W ∧
      coinsOk .coins (σA.elems (sA.coins + member p π₁ π₂ j 0)) = true)
    (hstB : ∀ j, j < p.bits → (σB.elems (sB.coins + member p π₁ π₂ j 0)).length = W ∧
      coinsOk .coins (σB.elems (sB.coins + member p π₁ π₂ j 0)) = true)
    (hrest : ∀ I, CoinsAre p f I0 I (fun o j i => if o = 0 then (σA.elems (sA.coins + member p π₁ π₂ j 0)).getD i 0
        else (σB.elems (sB.coins + member p π₁ π₂ j 0)).getD i 0) p.bits →
      ∃ J, JRet (jointRun E tA tB σA σB I) a b' J σA σB ∧ R J) :
    ∀ n, n ≤ p.bits → ∀ I, CoinsAre p f I0 I (fun o j i => if o = 0 then (σA.elems (sA.coins + member p π₁ π₂ j 0)).getD i 0
        else (σB.elems (sB.coins + member p π₁ π₂ j 0)).getD i 0) (p.bits - n) →
      ∃ J, JRet (jointRun E
        (seqs ((List.range' (p.bits - n) n).map fun j =>
          (.fieldInput ((List.range W).map (coinH p f 0 j)) ((List.range W).map (coinH p f 1 j)) .coins false
            (sA.coins + member p π₁ π₂ j 0) : Instr)) tA)
        (seqs ((List.range' (p.bits - n) n).map fun j =>
          (.fieldInput ((List.range W).map (coinH p f 0 j)) ((List.range W).map (coinH p f 1 j)) .coins false
            (sB.coins + member p π₁ π₂ j 0) : Instr)) tB) σA σB I) a b' J σA σB ∧ R J
  | 0, _, I, hinv => by
    simp only [List.range'_zero, List.map_nil, seqs_nil]
    exact hrest I (by simpa using hinv)
  | n + 1, hn, I, hinv => by
    have e : List.range' (p.bits - (n + 1)) (n + 1) = (p.bits - (n + 1)) :: List.range' (p.bits - n) n := by
      rw [List.range'_succ]
      congr 1
      congr 1
      omega
    rw [e, List.map_cons, List.map_cons, seqs_cons, seqs_cons]
    have hj : p.bits - (n + 1) < p.bits := by omega
    obtain ⟨hlA, hcA⟩ := hstA _ hj
    obtain ⟨hlB, hcB⟩ := hstB _ hj
    obtain ⟨s1, s2, s3, s4⟩ := coin_step p f .a I _ hj _ _ hlA hlB
    have hinv' : CoinsAre p f I0
        (bothFields .a I ((List.range W).map (coinH p f 0 (p.bits - (n + 1))))
          ((List.range W).map (coinH p f 1 (p.bits - (n + 1))))
          (σA.elems (sA.coins + member p π₁ π₂ (p.bits - (n + 1)) 0))
          (σB.elems (sB.coins + member p π₁ π₂ (p.bits - (n + 1)) 0)))
        (fun o j i => if o = 0 then (σA.elems (sA.coins + member p π₁ π₂ j 0)).getD i 0
          else (σB.elems (sB.coins + member p π₁ π₂ j 0)).getD i 0) (p.bits - n) := by
      refine ⟨fun o ho j hjn i hi => ?_, fun id hid => ?_, ?_⟩
      · have ho' : o = 0 ∨ o = 1 := by omega
        by_cases hjk : j = p.bits - (n + 1)
        · subst hjk
          rcases ho' with rfl | rfl
          · exact s2 i hi
          · exact s3 i hi
        · rw [s4 _ (coin_frame p f o j _ i ho (by omega) hj hi)]
          exact hinv.val o ho j (by omega) i hi
      · rw [s4 id (Or.inl (by omega))]
        exact hinv.low id hid
      · rw [s1]
        exact hinv.bools
    obtain ⟨J, hJ, hR⟩ := coin_inputs_jret sA sB π₁ π₂ tA tB σA σB a b' I0 R hstA hstB hrest n (by omega) _ hinv'
    exact ⟨J, jret_fieldInput E _ _ _ _ _ _ _ _ σA σB I a b' J σA σB (by simp) (by simpa using hlA) hcA
      (by simpa using hlB) hcB hJ, hR⟩

/-- The bit-block phase of two honest parties. -/
theorem bit_jret (hP : ProgsLoaded E) (sA sB : Slots) (π₁ π₂ : List Nat) (σA σB : Store) (I5 : Ideal)
    (x : Vals) (r2 : Nat → Nat → Nat) (bundle : Bits) (hx : BothHonest p r2 x)
    (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M)
    (hσA : ∀ c, c < p.M → σA.elems (sA.coins + c) = (word (r2 0 c)).map X25519.bitValue)
    (hσB : ∀ c, c < p.M → σB.elems (sB.coins + c) = (word (r2 1 c)).map X25519.bitValue)
    (hfld : ∀ o, o < 2 → ∀ c, c < p.M → I5.fields (fOf p f o c).id = some (x.elem o c))
    (hb : I5.bools (b + 10) = some bundle) (hlen : bundle.length = p.N * 256) (hbits : p.bits ≤ p.N) :
    ∃ J, JRet (jointRun E (bitPhase p b f sA π₁ π₂) (bitPhase p b f sB π₁ π₂) σA σB I5) () () J σA σB ∧
      ((∀ id, id < bitBase p b → J.bools id = I5.bools id) ∧
      (∀ id, id < coinBase p f → J.fields id = I5.fields id) ∧
      (∀ j, j < p.bits → ∀ i, i < W →
        J.bools (bitBase p b + j * W + i) = some ((bundle.drop (256 * j + i)).take 1) ∧
        J.fields (xorH p f (j * W + i)).id = some (X25519.bitValue
          ((word (r2 0 (refOf p π₁ π₂ j))).getD i false ^^ (word (r2 1 (refOf p π₁ π₂ j))).getD i false)))) := by
  have hml := member_lt p π₁ π₂ hπ₁ hM
  unfold bitPhase
  by_cases hb0 : p.bits = 0
  · rw [if_pos hb0, if_pos hb0]
    exact ⟨I5, jret_done E () () σA σB I5, fun _ _ => rfl, fun _ _ => rfl, fun j hj => absurd hj (by omega)⟩
  · rw [if_neg hb0, if_neg hb0]
    unfold coinInputs
    have hvalA : ∀ j, j < p.bits → ∀ i, i < W → (σA.elems (sA.coins + member p π₁ π₂ j 0)).getD i 0 =
        X25519.bitValue ((word (r2 0 (refOf p π₁ π₂ j))).getD i false) := by
      intro j _ i hi
      rw [hσA _ (hml j 0)]
      exact getD_map_lt _ _ _ _ _ (by simpa using hi)
    have hvalB : ∀ j, j < p.bits → ∀ i, i < W → (σB.elems (sB.coins + member p π₁ π₂ j 0)).getD i 0 =
        X25519.bitValue ((word (r2 1 (refOf p π₁ π₂ j))).getD i false) := by
      intro j _ i hi
      rw [hσB _ (hml j 0)]
      exact getD_map_lt _ _ _ _ _ (by simpa using hi)
    have key := coin_inputs_jret E p f sA sB π₁ π₂
      (seq (.program recomposeName (2 * p.bits) (recIns p f π₁ π₂) [] (recOuts p f) Label.bitBlockChecks) <|
        seq (.program bitCheckName (2 * (p.bits * W)) (allCoins p f) [] (chkOuts p f) Label.bitBlockChecks) <|
        openFieldThen (recOuts p f ++ chkOuts p f) Label.bitBlockChecks fun z =>
        if z.all (· == 0) then
          seq (.program bitXorName (p.bits * W) (xorIns p f) [] (xorOuts p f) Label.bitBlockChecks) <|
          seqs (pairSlices p b) (.done ())
        else .abort "bit block inconsistent with verified reference")
      (seq (.program recomposeName (2 * p.bits) (recIns p f π₁ π₂) [] (recOuts p f) Label.bitBlockChecks) <|
        seq (.program bitCheckName (2 * (p.bits * W)) (allCoins p f) [] (chkOuts p f) Label.bitBlockChecks) <|
        openFieldThen (recOuts p f ++ chkOuts p f) Label.bitBlockChecks fun z =>
        if z.all (· == 0) then
          seq (.program bitXorName (p.bits * W) (xorIns p f) [] (xorOuts p f) Label.bitBlockChecks) <|
          seqs (pairSlices p b) (.done ())
        else .abort "bit block inconsistent with verified reference")
      σA σB () () I5
      (fun J => (∀ id, id < bitBase p b → J.bools id = I5.bools id) ∧
        (∀ id, id < coinBase p f → J.fields id = I5.fields id) ∧
        (∀ j, j < p.bits → ∀ i, i < W →
          J.bools (bitBase p b + j * W + i) = some ((bundle.drop (256 * j + i)).take 1) ∧
          J.fields (xorH p f (j * W + i)).id = some (X25519.bitValue
            ((word (r2 0 (refOf p π₁ π₂ j))).getD i false ^^ (word (r2 1 (refOf p π₁ π₂ j))).getD i false))))
      (fun j _ => by rw [hσA _ (hml j 0)]; exact ⟨by simp, coinsOk_bits _⟩)
      (fun j _ => by rw [hσB _ (hml j 0)]; exact ⟨by simp, coinsOk_bits _⟩)
      (fun I6 hin => ?_) p.bits (Nat.le_refl _) I5
      ⟨fun o _ j hj => absurd hj (by omega), fun _ _ => rfl, rfl⟩
    · rw [Nat.sub_self, ← List.range_eq_range'] at key
      exact key
    · have hbase : f + 2 * p.M ≤ coinBase p f := by
        unfold coinBase maskBase
        omega
      have hκ : ∀ o, o < 2 → ∀ j, j < p.bits → ∀ i, i < W →
          (if o = 0 then (σA.elems (sA.coins + member p π₁ π₂ j 0)).getD i 0
            else (σB.elems (sB.coins + member p π₁ π₂ j 0)).getD i 0) =
          X25519.bitValue ((word (r2 o (refOf p π₁ π₂ j))).getD i false) := by
        intro o ho j hj i hi
        have ho' : o = 0 ∨ o = 1 := by omega
        rcases ho' with rfl | rfl
        · rw [if_pos rfl]
          exact hvalA j hj i hi
        · rw [if_neg (by omega)]
          exact hvalB j hj i hi
      have hc : CoinsHold p f I6 (fun o j i => if o = 0 then (σA.elems (sA.coins + member p π₁ π₂ j 0)).getD i 0
          else (σB.elems (sB.coins + member p π₁ π₂ j 0)).getD i 0) := hin.val
      obtain ⟨pr, vi, vo, pc, vi2, vo2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
        coins_programs E hP p f π₁ π₂ I6 _ x hc (fun o ho j _ => by
          rw [hin.low _ (by have := fOf_id_lt p f o _ ho (hml j 0); unfold refOf; omega)]
          exact hfld o ho _ (hml j 0))
      have hzero := hx.bitZ π₁ π₂ _ (fun j _ => hml j 0) hκ
      have hall : (Masks.bitZ p π₁ π₂ (fun o j i => if o = 0 then (σA.elems (sA.coins + member p π₁ π₂ j 0)).getD i 0
          else (σB.elems (sB.coins + member p π₁ π₂ j 0)).getD i 0) x).all (· == 0) = true := by
        rw [List.all_eq_true]
        intro z hz
        simpa using hzero z hz
      have hcJ : CoinsHold p f ((I6.setFields (recOuts p f) vo).setFields (chkOuts p f) vo2)
          (fun o j i => if o = 0 then (σA.elems (sA.coins + member p π₁ π₂ j 0)).getD i 0
            else (σB.elems (sB.coins + member p π₁ π₂ j 0)).getD i 0) := by
        intro o ho j hj i hi
        rw [q11 _ (by have := coin_lt p o j i ho hj hi; rw [coin_id]; omega)]
        exact hc o ho j hj i hi
      obtain ⟨px, wi, wo, x1, x2, x3, x4, x5, x6, x7⟩ := coins_xor E hP p f _ _ hcJ
      obtain ⟨J', y1, y2, y3, y4⟩ := pairSlices_block E p b
        (((I6.setFields (recOuts p f) vo).setFields (chkOuts p f) vo2).setFields (xorOuts p f) wo) bundle
        (by rw [x5, q10, hin.bools]; exact hb) hlen hbits
      refine ⟨J', ?_, fun id hid => ?_, fun id hid => ?_, fun j hj i hi => ⟨y3 j hj i hi, ?_⟩⟩
      · refine jret_program E _ _ _ _ _ _ _ _ σA σB I6 pr vi [] vo [] () () J' σA σB q1 q2 rfl q3 q4 ?_
        refine jret_program E _ _ _ _ _ _ _ _ σA σB _ pc vi2 [] vo2 [] () () J' σA σB q5 q6 rfl q7 q8 ?_
        refine jret_openFieldThen E _ _ _ _ σA σB _ _ () () J' σA σB q9 ?_
        simp only [hall, if_true]
        refine jret_program E _ _ _ _ _ _ _ _ σA σB _ px wi [] wo [] () () J' σA σB x1 x2 rfl x3 x4 ?_
        refine jret_locals E _ _ σA σB () () J' σA σB _ (pairSlices_local p b) _ J' y1 ?_
        exact jret_done E () () σA σB J'
      · rw [y4 id hid, x5, q10, hin.bools]
      · rw [y2, x7 id (by omega), q11 id (by omega), hin.low id hid]
      · rw [y2, x6 j hj i hi]
        unfold xorVal
        dsimp only
        rw [hκ 0 (by omega) j hj i hi, hκ 1 (by omega) j hj i hi, bitXorValue_bits]

/-- The last phase of two honest parties: the pool, and the masks' values in the engines. -/
theorem finish_jret (hW : WordLoaded E) (hP : ProgsLoaded E) (sA sB : Slots) (π₁ π₂ : List Nat) (σA σB : Store)
    (I : Ideal) (v : Bits) (x : Vals) (r2 : Nat → Nat → Nat) (h : Holds p b f I v x) (hx : BothHonest p r2 x)
    (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M) (hbits : p.bits ≤ p.N)
    (hσA : ∀ c, c < p.M → σA.elems (sA.coins + c) = (word (r2 0 c)).map X25519.bitValue)
    (hσB : ∀ c, c < p.M → σB.elems (sB.coins + c) = (word (r2 1 c)).map X25519.bitValue)
    (h32 : ∀ j, j < p.bits → ∀ o, o < 2 → 32 ≤ r2 o (refOf p π₁ π₂ j)) :
    ∃ J, JRet (jointRun E (finishPhase p b f sA π₁ π₂) (finishPhase p b f sB π₁ π₂) σA σB I)
        ⟨maskList p b f, pairList p b f⟩ ⟨maskList p b f, pairList p b f⟩ J σA σB ∧
      (∀ j, j < p.words →
        J.bools (b + 12 + j) = some (word ((r2 0 (refOf p π₁ π₂ (p.bits + j)) + r2 1 (refOf p π₁ π₂ (p.bits + j))) % P)) ∧
        J.fields (maskBase p f + j) = some (TlsMpc.FieldDag.ofNat
          ((r2 0 (refOf p π₁ π₂ (p.bits + j)) + r2 1 (refOf p π₁ π₂ (p.bits + j))) % P))) ∧
      (∀ j, j < p.bits → ∀ i, i < W →
        J.bools (bitBase p b + j * W + i) =
          some [(word (r2 0 (refOf p π₁ π₂ j))).getD i false ^^ (word (r2 1 (refOf p π₁ π₂ j))).getD i false] ∧
        J.fields (xorH p f (j * W + i)).id = some (X25519.bitValue
          ((word (r2 0 (refOf p π₁ π₂ j))).getD i false ^^ (word (r2 1 (refOf p π₁ π₂ j))).getD i false))) := by
  have hml := member_lt p π₁ π₂ hπ₁ hM
  have hwide := h.wide
  obtain ⟨I4, f1, f2, f3, f4⟩ := h.final E hW π₁ π₂ hπ₁ hM hbits
  have hflags := hx.flags hwide π₁ π₂ (fun j _ => hml j 0) h32
  have hl : (outsOf p π₁ π₂ x).flatten.length = p.N * 256 := by
    rw [length_flatten_eq 256 _ (outsOf_length_each hwide p π₁ π₂)]
    simp [outsOf]
  obtain ⟨I5, m1, m2, m3, m4, m5, m6, m7⟩ := masks_block E p b f π₁ π₂ I4 x _ f3 hl hbits
    (fun o ho c hc => by rw [f2]; exact h.hfld o ho c hc) hπ₁ hM
  have hmb : f + 2 * p.M ≤ maskBase p f := by unfold maskBase; omega
  obtain ⟨J, hJ, k2, k3, k4⟩ := bit_jret E p b f hP sA sB π₁ π₂ σA σB I5 x r2 _ hx hπ₁ hM hσA hσB
    (fun o ho c hc => by
      rw [m5 _ (by have := fOf_id_lt p f o c ho hc; omega), f2]
      exact h.hfld o ho c hc)
    m2 hl hbits
  refine ⟨J, ?_, fun j hj => ⟨?_, ?_⟩, fun j hj i hi => ⟨?_, (k4 j hj i hi).2⟩⟩
  · unfold finishPhase
    refine jret_locals E _ _ σA σB _ _ J σA σB _ (finalBlock_local p b π₁ π₂) I I4 f1 ?_
    refine jret_openThen E ⟨b + 11⟩ _ _ _ σA σB _ _ _ _ J σA σB f4 ?_
    simp only [hflags, if_true]
    refine jret_locals E _ _ σA σB _ _ J σA σB _ (maskBlock_local p b f π₁ π₂) _ I5 m1 ?_
    exact jret_bind E _ _ _ _ σA σB I5 () () J σA σB _ _ J σA σB hJ (jret_done E _ _ σA σB J)
  · have hc : refOf p π₁ π₂ (p.bits + j) < p.M := hml (p.bits + j) 0
    rw [k2 _ (by unfold bitBase; omega), m3 j hj, bundle_mask_word hwide p π₁ π₂ j hj,
      hx.val 0 _ (by omega) hc, hx.val 1 _ (by omega) hc,
      addModSpec_canonical _ _ (hx.canon 0 (by omega) _ hc) (hx.canon 1 (by omega) _ hc)]
  · have hc : refOf p π₁ π₂ (p.bits + j) < p.M := hml (p.bits + j) 0
    rw [k3 _ (by unfold coinBase; omega), m4 j hj, hx.elem 0 (by omega) _ hc, hx.elem 1 (by omega) _ hc, ofNat_add]
  · have hc : refOf p π₁ π₂ j < p.M := hml j 0
    rw [(k4 j hj i hi).1, bundle_pair_bit hwide p π₁ π₂ hbits j i hj hi, hx.bits 0 (by omega) _ hc,
      hx.bits 1 (by omega) _ hc]

/-- The two parties' candidates by owner. -/
def pick2 (rA rB : Nat → Nat) (o c : Nat) : Nat := if o = 0 then rA c else rB c

/-- **P-CUT (a) for a whole honest run.** Two honest parties run `generate` in lockstep: both
return the pool `⟨maskList, pairList⟩`, their stores are unchanged, and in the final engine state
every word mask is a Boolean word and a field element of the same value `(rA c + rB c) mod p`
(`c` its bucket's reference), and every bit pair is the XOR of the two references' bits in both
engines. Hypotheses: the two challenges' commitments differ, their expansions succeed, and the bit
blocks' references are at least 32 (each fails with negligible probability and then aborts the
run). -/
theorem generate_honest (hh : ∀ m, (E.hash m).length = 32) (hW : WordLoaded E) (hP : ProgsLoaded E)
    (hM : 0 < p.M) (hbits : p.bits ≤ p.N) (sA sB : Slots) (σA σB : Store) (I : Ideal) (rA rB : Nat → Nat)
    (hA : HonestStore p sA σA rA) (hB : HonestStore p sB σB rB)
    (hc1 : E.hash (commitFrame Random.tag .a (σA.bytes sA.cutNonce) (σA.bytes sA.cutValue)) ≠
      E.hash (commitFrame Random.tag .b (σB.bytes sB.cutNonce) (σB.bytes sB.cutValue)))
    (hc2 : E.hash (commitFrame Random.tag .a (σA.bytes sA.bucketNonce) (σA.bytes sA.bucketValue)) ≠
      E.hash (commitFrame Random.tag .b (σB.bytes sB.bucketNonce) (σB.bytes sB.bucketValue)))
    (π₁ π₂ : List Nat)
    (hπ₁ : Random.permOf E.hash (domain p "cut")
      (Random.xorBytes (σA.bytes sA.cutValue) (σB.bytes sB.cutValue)) p.M = some π₁)
    (hπ₂ : Random.permOf E.hash (domain p "bucket")
      (Random.xorBytes (σA.bytes sA.bucketValue) (σB.bytes sB.bucketValue)) p.K = some π₂)
    (h32 : ∀ j, j < p.bits → 32 ≤ rA (refOf p π₁ π₂ j) ∧ 32 ≤ rB (refOf p π₁ π₂ j)) :
    ∃ J, JRet (jointRun E (generate p b f E.hash .a sA) (generate p b f E.hash .b sB) σA σB I)
        ⟨maskList p b f, pairList p b f⟩ ⟨maskList p b f, pairList p b f⟩ J σA σB ∧
      (∀ j, j < p.words →
        J.bools (b + 12 + j) = some (word ((rA (refOf p π₁ π₂ (p.bits + j)) + rB (refOf p π₁ π₂ (p.bits + j))) % P)) ∧
        J.fields (maskBase p f + j) = some (TlsMpc.FieldDag.ofNat
          ((rA (refOf p π₁ π₂ (p.bits + j)) + rB (refOf p π₁ π₂ (p.bits + j))) % P))) ∧
      (∀ j, j < p.bits → ∀ i, i < W →
        J.bools (bitBase p b + j * W + i) =
          some [(word (rA (refOf p π₁ π₂ j))).getD i false ^^ (word (rB (refOf p π₁ π₂ j))).getD i false] ∧
        J.fields (xorH p f (j * W + i)).id = some (X25519.bitValue
          ((word (rA (refOf p π₁ π₂ j))).getD i false ^^ (word (rB (refOf p π₁ π₂ j))).getD i false))) := by
  have hs1 := Random.permOf_spec E.hash _ _ _ π₁ hπ₁
  have hπ₁M : ∀ c ∈ π₁, c < p.M := hs1.2.2
  have hml := member_lt p π₁ π₂ hπ₁M hM
  have hpe : (σB.elems sB.elems).length = p.M := by rw [hB.elems]; simp
  -- the candidates in the engines after the inputs
  have H := input_holds p b f .a sA hA
    ((bothBools .a I ⟨b⟩ ⟨b + 1⟩ (σA.bits sA.bits) (σB.bits sB.bits)).setBool ⟨b + 2⟩
      (inBundle .a (σA.bits sA.bits) (σB.bits sB.bits))) (σB.bits sB.bits) (σB.elems sB.elems)
    hB.bits_length hpe (by simp [Ideal.setBool])
  have hx : BothHonest p (pick2 rA rB)
      (inVals p .a rA (inBundle .a (σA.bits sA.bits) (σB.bits sB.bits)) (σB.elems sB.elems)) := by
    refine ⟨fun o ho c hc => ?_, fun o ho c hc => ?_, fun o ho c hc => ?_⟩
    · have ho' : o = 0 ∨ o = 1 := by omega
      rcases ho' with rfl | rfl
      · exact inVals_honest p .a sA hA _ _ hB.bits_length c hc
      · rw [(inVals_other p .a sA hA _ _ hB.bits_length 1 (by omega) (by decide) c hc).1]
        exact hB.chunk c hc
    · have ho' : o = 0 ∨ o = 1 := by omega
      rcases ho' with rfl | rfl
      · rfl
      · rw [(inVals_other p .a sA hA _ _ hB.bits_length 1 (by omega) (by decide) c hc).2, hB.elems,
          getD_map_range _ _ _ _ hc]
        rfl
    · have ho' : o = 0 ∨ o = 1 := by omega
      rcases ho' with rfl | rfl
      · exact hA.canon c hc
      · exact hB.canon c hc
  -- the cut
  have hcutM : ∀ c ∈ cutOf p π₁, c < p.M := fun c hc => hπ₁M c (List.mem_of_mem_take hc)
  obtain ⟨I2, j2, H2⟩ := cut_jret E p b f π₁ σA σB _ _ _ H hcutM (hx.cut H.wide _ hcutM)
  -- the buckets
  obtain ⟨I3, j3, H3⟩ := bucket_jret E p b f hW π₁ π₂ σA σB I2 _ _ H2 hπ₁M hM
    (hx.bucket _ _ (fun e he => ⟨mem_pairs p e he, hml _ _, hml _ _⟩))
  -- the finish
  obtain ⟨J, j4, r1, r2⟩ := finish_jret E p b f hW hP sA sB π₁ π₂ σA σB I3 _ _ (pick2 rA rB) H3 hx hπ₁M hM hbits
    hA.coins hB.coins (fun j hj o ho => by
      have ho' : o = 0 ∨ o = 1 := by omega
      rcases ho' with rfl | rfl
      · exact (h32 j hj).1
      · exact (h32 j hj).2)
  refine ⟨J, ?_, r1, r2⟩
  unfold generate inputBlock
  simp only [seqs_cons, seqs_nil]
  refine jret_boolInputBoth E _ _ _ _ _ _ _ _ _ σA σB I _ _ J σA σB hA.bits_length hB.bits_length ?_
  refine jret_locals E _ _ σA σB _ _ J σA σB [.concat ⟨b + 2⟩ [⟨b⟩, ⟨b + 1⟩]] (by simp [isLocal]) _ _
    (concat_step E b .a I _ _) ?_
  refine jret_fieldInput E _ _ _ _ _ _ _ _ σA σB _ _ _ J σA σB (by simp) (by rw [hA.elems]; simp) rfl
    (by rw [hB.elems]; simp) rfl ?_
  refine jret_bind E _ _ _ _ σA σB _ π₁ π₁ _ σA σB _ _ J σA σB
    (jret_challenge E hh σA σB _ _ _ _ _ _ _ hA.n1 hA.v1 hB.n1 hB.v1 hc1 π₁ hπ₁) ?_
  refine jret_bind E _ _ _ _ σA σB _ () () I2 σA σB _ _ J σA σB j2 ?_
  refine jret_bind E _ _ _ _ σA σB _ π₂ π₂ I2 σA σB _ _ J σA σB
    (jret_challenge E hh σA σB _ _ _ _ _ _ _ hA.n2 hA.v2 hB.n2 hB.v2 hc2 π₂ hπ₂) ?_
  exact jret_bind E _ _ _ _ σA σB _ () () I3 σA σB _ _ J σA σB j3 j4

/-- **P-CUT (a) for the deployed profiles.** -/
theorem generate_honest_profile (hh : ∀ m, (E.hash m).length = 32) (hW : WordLoaded E) (hP : ProgsLoaded E)
    (N nbits : Nat) (hprof : profile N nbits = some p) (sA sB : Slots) (σA σB : Store) (I : Ideal)
    (rA rB : Nat → Nat) (hA : HonestStore p sA σA rA) (hB : HonestStore p sB σB rB)
    (hc1 : E.hash (commitFrame Random.tag .a (σA.bytes sA.cutNonce) (σA.bytes sA.cutValue)) ≠
      E.hash (commitFrame Random.tag .b (σB.bytes sB.cutNonce) (σB.bytes sB.cutValue)))
    (hc2 : E.hash (commitFrame Random.tag .a (σA.bytes sA.bucketNonce) (σA.bytes sA.bucketValue)) ≠
      E.hash (commitFrame Random.tag .b (σB.bytes sB.bucketNonce) (σB.bytes sB.bucketValue)))
    (π₁ π₂ : List Nat)
    (hπ₁ : Random.permOf E.hash (domain p "cut")
      (Random.xorBytes (σA.bytes sA.cutValue) (σB.bytes sB.cutValue)) p.M = some π₁)
    (hπ₂ : Random.permOf E.hash (domain p "bucket")
      (Random.xorBytes (σA.bytes sA.bucketValue) (σB.bytes sB.bucketValue)) p.K = some π₂)
    (h32 : ∀ j, j < p.bits → 32 ≤ rA (refOf p π₁ π₂ j) ∧ 32 ≤ rB (refOf p π₁ π₂ j)) :
    ∃ J, JRet (jointRun E (generate p b f E.hash .a sA) (generate p b f E.hash .b sB) σA σB I)
        ⟨maskList p b f, pairList p b f⟩ ⟨maskList p b f, pairList p b f⟩ J σA σB ∧
      (∀ j, j < p.words →
        J.bools (b + 12 + j) = some (word ((rA (refOf p π₁ π₂ (p.bits + j)) + rB (refOf p π₁ π₂ (p.bits + j))) % P)) ∧
        J.fields (maskBase p f + j) = some (TlsMpc.FieldDag.ofNat
          ((rA (refOf p π₁ π₂ (p.bits + j)) + rB (refOf p π₁ π₂ (p.bits + j))) % P))) ∧
      (∀ j, j < p.bits → ∀ i, i < W →
        J.bools (bitBase p b + j * W + i) =
          some [(word (rA (refOf p π₁ π₂ j))).getD i false ^^ (word (rB (refOf p π₁ π₂ j))).getD i false] ∧
        J.fields (xorH p f (j * W + i)).id = some (X25519.bitValue
          ((word (rA (refOf p π₁ π₂ j))).getD i false ^^ (word (rB (refOf p π₁ π₂ j))).getD i false))) :=
  generate_honest E p b f hh hW hP (profile_ok N nbits p hprof).1 (profile_ok N nbits p hprof).2 sA sB σA σB I
    rA rB hA hB hc1 hc2 π₁ π₂ hπ₁ hπ₂ h32

end Joint

end TlsMpc.Node.Flows.Masks
