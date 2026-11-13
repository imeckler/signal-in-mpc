import TlsMpc.Node.Flows.MasksHides
import TlsMpc.Node.Flows.MasksSound

/-!
# P-CUT and the counting model: the model's hypotheses, as theorems about the script

REORGANIZATION_PLAN.md 7.0, 7.1; stage S10. The Mathlib package (`proofs/TlsMpcProofs/CutAndChoose*.lean`)
bounds a COUNTING MODEL: a fixed set S of bad candidates among M = 2K; one uniform arrangement of
the candidates in which the first K are cut and the next K fill N buckets of B in order; the
adversary is caught when a bad candidate is cut or a bucket mixes good and bad candidates; the
probability of not being caught with a nonempty S is `bound(t)`, below 2⁻¹²⁸ for the deployed
profiles. This file states, as theorems about `Masks.generate` in the model of `Engine/Model.lean`,
what that model takes for granted.

`generate_sound` — one statement about ANY run of `generate` that RETURNS, against ANY adversary:
  1. THE BAD SET IS FIXED BEFORE THE CHALLENGES. The other party's candidates in the two engines
     are its contributions `pb`, `pe` to the two input instructions, and those are
     `adv.act vD (skeleton)`: its choice from its view `vD` BEFORE the run, the skeleton being
     public. Nothing of this run has been released at that point: not the honest candidates, not
     the challenge randomness. So the candidates `x` in the engines, their errors
     `x.err o c = (val(bits) − elem) mod p`, and the bad set `{c | x.err o c ≠ 0}` are fixed
     before either challenge exists. (That the challenge seeds are then independent of this choice
     is P-CHAL (c), `Random.challenge_seed_injective`, under `IdealCommit`: each seed is r ⊕ v with
     the honest r unseen until the adversary's v is committed.)
  2. (d) A BAD CANDIDATE IN THE CUT ABORTS: every cut candidate of both owners is canonical with
     error 0.
  3. (e) A MIXED BUCKET ABORTS: every (reference, member) pair passes `bucketOk`; with (f) the
     reference is canonical, so by `bucket_mixed_fails` no pair has exactly one error-free
     element: in every bucket of an owner, all candidates are good or all are bad.
  4. (f) NON-CANONICAL KEPT REFERENCES ARE CAUGHT BY THE FLAGS: every kept reference of both
     owners is canonical (and at least 32 for a bit block).
  5. What comes out: the pool, the word masks' values and (g) the bit pairs' values in the final
     engine state (`finishPhase_sound`); with `mask_consistent`, a mask whose two references are
     good is consistent.
`bucket_uniform` — the corollary in the model's words: in a run that returned, a bucket of an owner
is all good or all bad.

`arrangement` — THE ONE PERMUTATION OF THE MODEL. The script draws two permutations: π₁ of [0, M)
(cut = its first K entries, the rest remain) and π₂ of [0, K) (bucket slot i holds
`remain[π₂[i]]`). `arrangement π₁ π₂ = cut ++ π₂.map remain` is ONE arrangement of the M
candidates: a permutation of [0, M) (`arrangement_perm`), whose first K entries are the cut
(`arrangement_cut`) and whose entry K + B·j + k is member k of bucket j (`arrangement_slot`):
exactly the shape of the model's arrangement.

STILL ARGUED, NOT PROVED (no probability in this package):
  * that `arrangement π₁ π₂` is UNIFORM when π₁ and π₂ are: (π₁, π₂) ↦ arrangement is K!-to-one
    onto the arrangements (for a fixed π₂ it is a bijection of π₁), so two independent uniform
    permutations give a uniform arrangement — a counting fact not formalised here;
  * that π₁ and π₂ are uniform and independent of the bad set: they are `permOf` of seeds that are
    uniform given the adversary's view (P-CHAL (c) under `IdealCommit`), expanded with SHA-256
    (a random-oracle assumption) by rejection sampling (uniform for uniform words; the 2⁻⁶⁴⁰ abort);
  * the model's "caught" is "the run aborts" (items 2–4); the model's bad candidates are those of
    BOTH owners' sets separately (each owner's buckets are checked on their own); the bound applies
    to each owner's set.
-/

namespace TlsMpc.Node.Flows.Masks

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees Silent blankWire Leaves seqs_cons seqs_nil)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Conv
open TlsMpc.FieldDag (F modulus)
open TlsMpc.FieldDag.V3 (FieldInverse)

/-! ## The cut and the buckets of a run that returned, in the engines' candidates -/

section Pass

variable (E : Env) (me : Party) (adv : Adversary) (p : Params) (b f : Nat)

/-- **P-CUT (d), run level, for the candidates `x` the engines hold.** -/
theorem cutPhase_pass (π₁ : List Nat) (σ : Store) (I : Ideal) (vD : List Release) (v : Bits) (x : Vals)
    (h : Holds p b f I v x) (hπ : ∀ c ∈ cutOf p π₁, c < p.M)
    (hres : (withAdv E me adv (cutPhase p b f π₁) σ I vD).result = some ()) :
    ∀ o ∈ owners, ∀ c ∈ cutOf p π₁, x.val o c < P ∧ x.err o c = 0 := by
  obtain ⟨c1, c2⟩ := h.cut E π₁ hπ
  have hret : Ret (withAdv E me adv (cutPhase p b f π₁) σ I vD) ()
      (withAdv E me adv (cutPhase p b f π₁) σ I vD).ideal := ⟨hres, rfl⟩
  generalize (withAdv E me adv (cutPhase p b f π₁) σ I vD).ideal = J at hret
  unfold cutPhase at hret
  obtain ⟨I1, e1, r1⟩ := ret_locals E me adv _ σ () J [.pick ⟨b + 3⟩ ⟨b + 2⟩ (cutBits p π₁)] (by simp [isLocal]) I vD
    hret
  rw [c1] at e1
  cases e1
  obtain ⟨ve, vD1, hve, r2⟩ := ret_openFieldThen E me adv _ _ _ σ _ _ () J r1
  have eve : ve = (cutRel x (cutOf p π₁)).map Prod.snd := Option.some.inj (hve.symm.trans c2)
  obtain ⟨vb, vD2, hvb, r3⟩ := ret_openThen E me adv _ _ _ σ _ _ () J r2
  have evb : vb = ((cutRel x (cutOf p π₁)).map Prod.fst).flatten := by
    simp only [Ideal.setBool, if_true, Option.some.injEq] at hvb
    exact hvb.symm
  obtain ⟨hc, -⟩ := ret_ite E me adv _ _ _ σ _ _ () J r3
  rw [evb, eve] at hc
  exact (cutCheck_iff x h.wide _).mp hc

/-- **P-CUT (e), run level, for the candidates `x` the engines hold.** -/
theorem bucketPhase_pass (hW : WordLoaded E) (π₁ π₂ : List Nat) (σ : Store) (I : Ideal) (vD : List Release)
    (v : Bits) (x : Vals) (h : Holds p b f I v x) (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M)
    (hres : (withAdv E me adv (bucketPhase p b f π₁ π₂) σ I vD).result = some ()) :
    ∀ e ∈ pairs p, bucketOk (x.val e.1 (member p π₁ π₂ e.2.1 0)) (x.val e.1 (member p π₁ π₂ e.2.1 e.2.2))
      (x.elem e.1 (member p π₁ π₂ e.2.1 0)) (x.elem e.1 (member p π₁ π₂ e.2.1 e.2.2)) = true := by
  obtain ⟨I3, g1, g2, g3, -, -⟩ := h.bucket E hW π₁ π₂ hπ₁ hM
  have hret : Ret (withAdv E me adv (bucketPhase p b f π₁ π₂) σ I vD) ()
      (withAdv E me adv (bucketPhase p b f π₁ π₂) σ I vD).ideal := ⟨hres, rfl⟩
  generalize (withAdv E me adv (bucketPhase p b f π₁ π₂) σ I vD).ideal = J at hret
  unfold bucketPhase at hret
  obtain ⟨I3', e1, r1⟩ := ret_locals E me adv _ σ () J _ (bucketBlock_local p b f π₁ π₂) I vD hret
  have eI : I3' = I3 := Option.some.inj (e1.symm.trans g1)
  subst eI
  obtain ⟨ve, vD1, hve, r2⟩ := ret_openFieldThen E me adv _ _ _ σ _ _ () J r1
  have eve : ve = (bucketRel x (member p π₁ π₂) (pairs p)).map Prod.snd := Option.some.inj (hve.symm.trans g3)
  obtain ⟨vb, vD2, hvb, r3⟩ := ret_openThen E me adv _ _ _ σ _ _ () J r2
  have evb : vb = ((bucketRel x (member p π₁ π₂) (pairs p)).map Prod.fst).flatten :=
    Option.some.inj (hvb.symm.trans g2)
  obtain ⟨hc, -⟩ := ret_ite E me adv _ _ _ σ _ _ () J r3
  rw [evb, eve] at hc
  exact (bucketCheck_iff _ _ _).mp hc

/-- **The counting model's hypotheses, for any run of `generate` that returns** (see the file
header): the other party's candidates are its choice from its view before the run; every cut
candidate is good (d); every bucket pair passes (e); every kept reference is canonical (f); and the
pool's masks hold the values `finishPhase_sound` gives (g). -/
theorem generate_sound (hinv : FieldInverse) (hh : ∀ m, (E.hash m).length = 32) (hW : WordLoaded E)
    (hP : ProgsLoaded E) (hM : 0 < p.M) (hbits : p.bits ≤ p.N) (s : Slots) (σ : Store) (I : Ideal)
    (vD : List Release) (r : Nat → Nat) (hσ : HonestStore p s σ r) (pool : MaskPool)
    (hres : (withAdv E me adv (generate p b f E.hash me s) σ I vD).result = some pool) :
    ∃ (pb pe : PeerPart) (π₁ π₂ : List Nat),
      adv.act vD (.boolInputBoth ⟨b⟩ ⟨b + 1⟩ (p.M * W) false true ()) = some pb ∧
      adv.act vD (.fieldInput ((List.range p.M).map (fOf p f 0)) ((List.range p.M).map (fOf p f 1))
        .elements true ()) = some pe ∧
      Perms p π₁ π₂ ∧
      (∀ o ∈ owners, ∀ c ∈ cutOf p π₁,
        (inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).val o c < P ∧
        (inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).err o c = 0) ∧
      (∀ e ∈ pairs p, bucketOk
        ((inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).val e.1 (member p π₁ π₂ e.2.1 0))
        ((inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).val e.1 (member p π₁ π₂ e.2.1 e.2.2))
        ((inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).elem e.1 (member p π₁ π₂ e.2.1 0))
        ((inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).elem e.1 (member p π₁ π₂ e.2.1 e.2.2)) =
          true) ∧
      (∀ j, j < p.N →
        (inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).val 0 (refOf p π₁ π₂ j) < P ∧
        (inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).val 1 (refOf p π₁ π₂ j) < P ∧
        (j < p.bits →
          32 ≤ (inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).val 0 (refOf p π₁ π₂ j) ∧
          32 ≤ (inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).val 1 (refOf p π₁ π₂ j))) ∧
      pool = ⟨maskList p b f, pairList p b f⟩ ∧
      (∀ j, j < p.words →
        (withAdv E me adv (generate p b f E.hash me s) σ I vD).ideal.bools (b + 12 + j) =
          some (word (addModSpec
            ((inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).val 0 (refOf p π₁ π₂ (p.bits + j)))
            ((inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).val 1 (refOf p π₁ π₂ (p.bits + j))))) ∧
        (withAdv E me adv (generate p b f E.hash me s) σ I vD).ideal.fields (maskBase p f + j) =
          some ((inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).elem 0 (refOf p π₁ π₂ (p.bits + j)) +
            (inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).elem 1 (refOf p π₁ π₂ (p.bits + j)))) ∧
      (∀ j, j < p.bits →
        (inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).err 0 (refOf p π₁ π₂ j) = 0 →
        (inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).err 1 (refOf p π₁ π₂ j) = 0 → ∀ i, i < W →
        (withAdv E me adv (generate p b f E.hash me s) σ I vD).ideal.bools (bitBase p b + j * W + i) =
          some [((inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).bits 0 (refOf p π₁ π₂ j)).getD i false ^^
            ((inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).bits 1 (refOf p π₁ π₂ j)).getD i false] ∧
        (withAdv E me adv (generate p b f E.hash me s) σ I vD).ideal.fields (xorH p f (j * W + i)).id =
          some (X25519.bitValue
            (((inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).bits 0 (refOf p π₁ π₂ j)).getD i false ^^
              ((inVals p me r (inBundle me (σ.bits s.bits) pb.bits) pe.elems).bits 1 (refOf p π₁ π₂ j)).getD i false))) := by
  have hret : Ret (withAdv E me adv (generate p b f E.hash me s) σ I vD) pool
      (withAdv E me adv (generate p b f E.hash me s) σ I vD).ideal := ⟨hres, rfl⟩
  generalize (withAdv E me adv (generate p b f E.hash me s) σ I vD).ideal = J at hret ⊢
  unfold generate inputBlock at hret
  simp only [seqs_cons, seqs_nil] at hret
  -- the inputs
  obtain ⟨pb, a1, l1, -, r1⟩ := ret_boolInputBoth E me adv _ _ _ _ _ _ _ σ I vD pool J hret
  obtain ⟨I2, e2, r2⟩ := ret_locals E me adv _ σ pool J [.concat ⟨b + 2⟩ [⟨b⟩, ⟨b + 1⟩]] (by simp [isLocal]) _ vD r1
  rw [concat_step] at e2
  cases e2
  obtain ⟨pe, a2, l3, -, r3⟩ := ret_fieldInput_act E me adv _ _ _ _ _ _ σ _ vD pool J
    (by rw [List.length_map, List.length_map]) r2
  have hpe : pe.elems.length = p.M := by rw [l3, List.length_map, List.length_range]
  have H := input_holds p b f me s hσ
    ((bothBools me I ⟨b⟩ ⟨b + 1⟩ (σ.bits s.bits) pb.bits).setBool ⟨b + 2⟩ (inBundle me (σ.bits s.bits) pb.bits))
    pb.bits pe.elems l1 hpe (by simp [Ideal.setBool])
  generalize bothFields me _ _ _ _ pe.elems = I3 at r3 H
  -- the first challenge
  obtain ⟨π₁, vD1, hπ1, r4⟩ := ret_bind E me adv _ _ σ I3 vD pool J r3
  have hs1 := Leaves.result E me adv _ (challenge_leaves E.hash me _ _ _ _) σ I3 vD π₁ hπ1
  obtain ⟨q1, q2, -, -⟩ := (agree_challenge E me adv hh σ σ I3 I3 vD _ _ _ _ hσ.n1 hσ.v1 rfl rfl).post π₁ hπ1
  rw [q1, q2] at r4
  have hcutM : ∀ c ∈ cutOf p π₁, c < p.M := fun c hc => hs1.2.2 c (List.mem_of_mem_take hc)
  -- the cut
  obtain ⟨u1, vD2, hu1, r5⟩ := ret_bind E me adv _ _ σ I3 vD1 pool J r4
  have hd := cutPhase_pass E me adv p b f π₁ σ I3 vD1 _ _ H hcutM hu1
  obtain ⟨q3, -, H2, -⟩ := (cut_agree E me adv p b f π₁ σ σ I3 I3 vD1 _ _ _ _ H H hcutM rfl).post u1 hu1
  rw [q3] at r5
  generalize (withAdv E me adv (cutPhase p b f π₁) σ I3 vD1).ideal = I4 at r5 H2
  -- the second challenge
  obtain ⟨π₂, vD3, hπ2, r6⟩ := ret_bind E me adv _ _ σ I4 vD2 pool J r5
  have hs2 := Leaves.result E me adv _ (challenge_leaves E.hash me _ _ _ _) σ I4 vD2 π₂ hπ2
  obtain ⟨q4, q5, -, -⟩ := (agree_challenge E me adv hh σ σ I4 I4 vD2 _ _ _ _ hσ.n2 hσ.v2 rfl rfl).post π₂ hπ2
  rw [q4, q5] at r6
  -- the buckets
  obtain ⟨u2, vD4, hu2, r7⟩ := ret_bind E me adv _ _ σ I4 vD3 pool J r6
  have he := bucketPhase_pass E me adv p b f hW π₁ π₂ σ I4 vD3 _ _ H2 hs1.2.2 hM hu2
  obtain ⟨q6, -, H3, -⟩ :=
    (bucket_agree E me adv p b f hW π₁ π₂ σ σ I4 I4 vD3 _ _ _ _ H2 H2 hs1.2.2 hM rfl).post u2 hu2
  rw [q6] at r7
  generalize (withAdv E me adv (bucketPhase p b f π₁ π₂) σ I4 vD3).ideal = I5 at r7 H3
  -- the finish
  obtain ⟨k1, k2, k3, k4⟩ := finishPhase_sound E me adv p b f hinv hW hP s π₁ π₂ σ I5 vD4 _ _ pool H3 hs1.2.2 hM
    hbits r7.1
  rw [r7.2] at k3 k4
  exact ⟨pb, pe, π₁, π₂, a1, a2, ⟨hs1, hs2⟩, hd, he, k2, k1, k3, k4⟩

end Pass

/-- **The model's rule in its own words**: in a run where every bucket pair passes and the kept
references are canonical, every bucket of an owner is uniform: its members are good exactly when
its reference is. -/
theorem bucket_uniform (x : Vals) (hw : x.Wide) (p : Params) (π₁ π₂ : List Nat)
    (he : ∀ e ∈ pairs p, bucketOk (x.val e.1 (member p π₁ π₂ e.2.1 0)) (x.val e.1 (member p π₁ π₂ e.2.1 e.2.2))
      (x.elem e.1 (member p π₁ π₂ e.2.1 0)) (x.elem e.1 (member p π₁ π₂ e.2.1 e.2.2)) = true)
    (e : Nat × Nat × Nat) (hmem : e ∈ pairs p) (hc : x.val e.1 (member p π₁ π₂ e.2.1 0) < P) :
    x.err e.1 (member p π₁ π₂ e.2.1 0) = 0 ↔ x.err e.1 (member p π₁ π₂ e.2.1 e.2.2) = 0 := by
  have hm : x.val e.1 (member p π₁ π₂ e.2.1 e.2.2) < 2 ^ 255 := by
    have := natOf_lt (x.bits e.1 (member p π₁ π₂ e.2.1 e.2.2))
    rw [hw] at this
    exact this
  have hpass := he e hmem
  constructor
  · intro h0
    apply Classical.byContradiction
    intro h1
    rw [bucket_mixed_fails x e.1 _ _ hc hm (Or.inl ⟨h0, h1⟩)] at hpass
    cases hpass
  · intro h1
    apply Classical.byContradiction
    intro h0
    rw [bucket_mixed_fails x e.1 _ _ hc hm (Or.inr ⟨h0, h1⟩)] at hpass
    cases hpass

/-! ## The two challenges as one arrangement -/

/-- **The one arrangement of the candidates** that the two challenge permutations give: the cut,
then the bucket slots in order (slot `B·j + k` is member `k` of bucket `j`). -/
def arrangement (p : Params) (π₁ π₂ : List Nat) : List Nat :=
  cutOf p π₁ ++ π₂.map fun t => (remainOf p π₁).getD t 0

/-- **The arrangement is a permutation of the candidates** [0, M), for permutations π₁ of [0, M)
and π₂ of [0, K) (what `Random.challenge` yields: `Random.permOf_perm`). -/
theorem arrangement_perm (p : Params) (π₁ π₂ : List Nat) (h1 : π₁.Perm (List.range p.M))
    (h2 : π₂.Perm (List.range p.K)) : (arrangement p π₁ π₂).Perm (List.range p.M) := by
  have hM : p.M = 2 * p.K := rfl
  have hl : (remainOf p π₁).length = p.K := by
    unfold remainOf
    rw [List.length_drop, h1.length_eq, List.length_range]
    omega
  have hr : (List.range p.K).map (fun t => (remainOf p π₁).getD t 0) = remainOf p π₁ := by
    rw [← hl]
    exact map_getD_all _ 0
  have h3 : (π₂.map fun t => (remainOf p π₁).getD t 0).Perm (remainOf p π₁) := by
    have := h2.map (fun t => (remainOf p π₁).getD t 0)
    rw [hr] at this
    exact this
  have h4 : (arrangement p π₁ π₂).Perm (cutOf p π₁ ++ remainOf p π₁) := List.Perm.append_left _ h3
  have h5 : cutOf p π₁ ++ remainOf p π₁ = π₁ := List.take_append_drop _ _
  rw [h5] at h4
  exact h4.trans h1

/-- The first K entries of the arrangement are the cut. -/
theorem arrangement_cut (p : Params) (π₁ π₂ : List Nat) (h1 : π₁.length = p.M) :
    (arrangement p π₁ π₂).take p.K = cutOf p π₁ := by
  have hM : p.M = 2 * p.K := rfl
  have hl : (cutOf p π₁).length = p.K := by
    unfold cutOf
    rw [List.length_take, h1]
    omega
  unfold arrangement
  rw [List.take_left' hl]

/-- Entry `K + B·j + k` of the arrangement is member `k` of bucket `j`. -/
theorem arrangement_slot (p : Params) (π₁ π₂ : List Nat) (h1 : π₁.length = p.M) (j k : Nat)
    (h : p.B * j + k < π₂.length) :
    (arrangement p π₁ π₂).getD (p.K + (p.B * j + k)) 0 = member p π₁ π₂ j k := by
  have hM : p.M = 2 * p.K := rfl
  have hl : (cutOf p π₁).length = p.K := by
    unfold cutOf
    rw [List.length_take, h1]
    omega
  unfold arrangement member
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl, Nat.add_sub_cancel_left]
  simp [List.getD_eq_getElem?_getD, h]

end TlsMpc.Node.Flows.Masks
