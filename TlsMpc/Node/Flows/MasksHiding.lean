import TlsMpc.Node.Flows.MasksState

/-!
# P-CUT (c): `Masks.generate` hides the kept references (the composition with the model)

REORGANIZATION_PLAN.md 7.0 and 7.1 P-CUT (c), stage S10. `MasksProofs.lean` has the core
arithmetic (`hiding_releases`: the cut and bucket releases are unchanged under a shift of the honest
party's candidates that vanishes on the cut and cancels in each bucket). This file composes it with
the model of `Engine/Model.lean`:

  * `generate_agree`: against ANY adversary, from any engine state and adversary view, two runs of
    `generate` whose honest stores hold candidates `r` and `r'` (and the same challenge randomness)
    AGREE (`Run.Agree`: the same views of both parties, the same trace, replies and result) as soon
    as, for the challenges the first run reaches: `r' = r` on the cut; in every bucket the sum of
    the reference and each member is the same mod p; and a bit block's reference is at least 32 in
    both or in neither. So the adversary's whole view of a run of `generate` is a function of the
    cut candidates, the bucket sums, the "at least 32" bits of the bit blocks' references, and the
    challenge randomness; of nothing else of the honest party's candidates.
  * The statement in plan 7.0's form, `generate_hides`, is in `MasksHides.lean`: the
    re-randomisation `reRand` moves every kept reference by any chosen amount and is a bijection.

How the proof goes: `Run.Agree` phase by phase. The inputs put the two candidate sets in the
engines (`Twin`: the honest owner's are `r` and `r'`, the other owner's are whatever the adversary
input, the same in both runs since it has seen the same); each challenge is the same (the same
randomness, the same adversary); each opening opens the same values (`cut_same`, `bucket_same`,
`flags_same`, `bitZ_same`), so the adversary and the honest script continue alike.
-/

namespace TlsMpc.Node.Flows.Masks

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees Silent blankWire Leaves seqs_cons seqs_nil)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Conv
open TlsMpc.FieldDag (F modulus)

/-! ## The script, split at the challenges -/

theorem bind_assoc' {α β γ : Type} (s : Script α) (f : α → Script β) (g : β → Script γ) :
    (s.bind f).bind g = s.bind (fun a => (f a).bind g) := by
  induction s with
  | done a => rfl
  | abort r => rfl
  | step i k ih =>
    simp only [Script.bind_step]
    congr 1
    funext r
    exact ih r

theorem seq_bind {α β : Type} (i : Instr) (s : Script α) (f : α → Script β) :
    (seq i s).bind f = seq i (s.bind f) := by
  unfold seq
  simp only [Script.bind_step]
  congr 1
  funext r
  cases r <;> rfl

theorem seqs_bind {α β : Type} (is : List Instr) (s : Script α) (f : α → Script β) :
    (seqs is s).bind f = seqs is (s.bind f) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [seqs_cons, seq_bind, ih]

/-- `generate` up to the first challenge: the cut permutation π₁. -/
def cutChallenge (p : Params) (b f : Nat) (hash : Bytes → Bytes) (me : Party) (s : Slots) : Script (List Nat) :=
  seqs (inputBlock p b f s) (Random.challenge hash me s.cutNonce s.cutValue (domain p "cut") p.M)

/-- `generate` up to the second challenge: the two permutations (π₁, π₂). -/
def bucketChallenge (p : Params) (b f : Nat) (hash : Bytes → Bytes) (me : Party) (s : Slots) :
    Script (List Nat × List Nat) :=
  seqs (inputBlock p b f s) <|
  (Random.challenge hash me s.cutNonce s.cutValue (domain p "cut") p.M).bind fun π₁ =>
  (cutPhase p b f π₁).bind fun _ =>
  (Random.challenge hash me s.bucketNonce s.bucketValue (domain p "bucket") p.K).bind fun π₂ =>
  .done (π₁, π₂)

theorem bucketChallenge_split (p : Params) (b f : Nat) (hash : Bytes → Bytes) (me : Party) (s : Slots) :
    bucketChallenge p b f hash me s = (cutChallenge p b f hash me s).bind fun π₁ =>
      (cutPhase p b f π₁).bind fun _ =>
      (Random.challenge hash me s.bucketNonce s.bucketValue (domain p "bucket") p.K).bind fun π₂ =>
      .done (π₁, π₂) := by
  unfold bucketChallenge cutChallenge
  rw [seqs_bind]

/-- **`generate` is its run up to the second challenge, then the buckets and the finish.** -/
theorem generate_split (p : Params) (b f : Nat) (hash : Bytes → Bytes) (me : Party) (s : Slots) :
    generate p b f hash me s = (bucketChallenge p b f hash me s).bind fun ππ =>
      (bucketPhase p b f ππ.1 ππ.2).bind fun _ => finishPhase p b f s ππ.1 ππ.2 := by
  unfold generate bucketChallenge
  rw [seqs_bind]
  simp only [bind_assoc', Script.bind_done]

/-- What a challenge yields (P-CHAL (b)). -/
def PermSpec (n : Nat) (π : List Nat) : Prop := π.length = n ∧ π.Nodup ∧ ∀ x ∈ π, x < n

theorem Leaves.bind' {α β : Type} {Q₁ : α → Prop} {Q : β → Prop} {s : Script α} {f : α → Script β}
    (h : Leaves Q₁ s) (hf : ∀ a, Q₁ a → Leaves Q (f a)) : Leaves Q (s.bind f) := by
  induction h with
  | done a ha => exact hf a ha
  | abort r => exact Leaves.abort r
  | step i k _ ih => exact Leaves.step i _ ih

theorem challenge_leaves (hash : Bytes → Bytes) (me : Party) (nonce value : Nat) (dom : Bytes) (n : Nat) :
    Leaves (PermSpec n) (Random.challenge hash me nonce value dom n) := by
  unfold Random.challenge
  refine Leaves.bind _ (fun seed => ?_) _
  unfold Random.finish
  split
  · next π hπ => exact Leaves.done _ (Random.permOf_spec hash dom seed n π hπ)
  · exact Leaves.abort _

theorem cutChallenge_leaves (p : Params) (b f : Nat) (hash : Bytes → Bytes) (me : Party) (s : Slots) :
    Leaves (PermSpec p.M) (cutChallenge p b f hash me s) :=
  Leaves.seqs (challenge_leaves hash me _ _ _ _) _

theorem bucketChallenge_leaves (p : Params) (b f : Nat) (hash : Bytes → Bytes) (me : Party) (s : Slots) :
    Leaves (fun ππ => PermSpec p.M ππ.1 ∧ PermSpec p.K ππ.2) (bucketChallenge p b f hash me s) := by
  unfold bucketChallenge
  refine Leaves.seqs (Leaves.bind' (challenge_leaves hash me _ _ _ _) (fun π₁ h1 => ?_)) _
  refine Leaves.bind _ (fun _ => ?_) _
  exact Leaves.bind' (challenge_leaves hash me _ _ _ _) (fun π₂ h2 => Leaves.done _ ⟨h1, h2⟩)

/-! ## The honest party's store -/

/-- The owner index of a party (0: A, 1: B). -/
def own : Party → Nat
  | .a => 0
  | .b => 1

theorem own_lt (me : Party) : own me < 2 := by cases me <;> decide

/-- **An honest party's store for `generate`**: its M candidates `r c` (canonical), as the bits and
the elements it inputs and as the coins of each (used for a bit block's reference), and 32-byte
challenge nonces and values. -/
structure HonestStore (p : Params) (s : Slots) (σ : Store) (r : Nat → Nat) : Prop where
  bits : σ.bits s.bits = ((List.range p.M).map fun c => word (r c)).flatten
  elems : σ.elems s.elems = (List.range p.M).map fun c => TlsMpc.FieldDag.ofNat (r c)
  coins : ∀ c, c < p.M → σ.elems (s.coins + c) = (word (r c)).map X25519.bitValue
  canon : ∀ c, c < p.M → r c < P
  n1 : (σ.bytes s.cutNonce).length = 32
  v1 : (σ.bytes s.cutValue).length = 32
  n2 : (σ.bytes s.bucketNonce).length = 32
  v2 : (σ.bytes s.bucketValue).length = 32

theorem HonestStore.bits_length {p : Params} {s : Slots} {σ : Store} {r : Nat → Nat} (h : HonestStore p s σ r) :
    (σ.bits s.bits).length = p.M * W := by
  rw [h.bits, length_flatten_eq W _ (by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨c, -, rfl⟩ := hy
    exact length_word _), List.length_map, List.length_range]

theorem HonestStore.chunk {p : Params} {s : Slots} {σ : Store} {r : Nat → Nat} (h : HonestStore p s σ r)
    (c : Nat) (hc : c < p.M) : ((σ.bits s.bits).drop (c * W)).take W = word (r c) := by
  rw [h.bits, flatten_drop_take W _ c (by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨c', -, rfl⟩ := hy
    exact length_word _) (by simpa using hc), getD_map_range _ _ _ _ hc]

theorem coinsOk_bits (bs : Bits) : coinsOk .coins (bs.map X25519.bitValue) = true := by
  simp only [coinsOk, List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq]
  intro x _
  cases x <;> decide

/-! ## The inputs -/

/-- The bundle A ‖ B after the inputs (`mine`: the honest party's bits). -/
def inBundle (me : Party) (mine pb : Bits) : Bits :=
  (if me = .a then mine else pb) ++ (if me = .a then pb else mine)

/-- The candidates in the engines after the inputs: the honest owner's are `r`, the other owner's
whatever was input (`pe` in the field engine; its bits are read off the bundle). -/
def inVals (p : Params) (me : Party) (r : Nat → Nat) (v : Bits) (pe : List F) : Vals where
  bits o c := (wordAt p o c).map (v.getD · false)
  elem o c := if o = own me then TlsMpc.FieldDag.ofNat (r c) else pe.getD c 0

theorem word_of_bundle (p : Params) (va vb : Bits) (ha : va.length = p.M * W) (hb : vb.length = p.M * W)
    (o c : Nat) (ho : o < 2) (hc : c < p.M) :
    (wordAt p o c).map ((va ++ vb).getD · false) = ((if o = 0 then va else vb).drop (c * W)).take W := by
  have hcW : (c + 1) * W ≤ p.M * W := Nat.mul_le_mul_right _ hc
  simp only [Nat.succ_mul] at hcW
  unfold wordAt
  rw [List.map_map]
  have ho' : o = 0 ∨ o = 1 := by omega
  rcases ho' with rfl | rfl
  · rw [if_pos rfl, ← map_getD_range va false (c * W) W (by omega)]
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply, bitAt]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
    simp
  · rw [if_neg (by omega), ← map_getD_range vb false (c * W) W (by omega)]
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply, bitAt]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    congr 2
    omega

section Inputs

variable (E : Env) (p : Params) (b f : Nat) (me : Party) (s : Slots)

theorem concat_step (I : Ideal) (mine pb : Bits) :
    runLocal E [.concat ⟨b + 2⟩ [⟨b⟩, ⟨b + 1⟩]] (bothBools me I ⟨b⟩ ⟨b + 1⟩ mine pb) =
      some ((bothBools me I ⟨b⟩ ⟨b + 1⟩ mine pb).setBool ⟨b + 2⟩ (inBundle me mine pb)) := by
  cases me <;>
    simp [runLocal, localStep, idealStep, blankWire, InstrP.map, bothBools, Ideal.setBool, inBundle]

/-- **After the input block the engines hold the candidates** (`Holds`), whatever the other party
input. -/
theorem input_holds {σ : Store} {r : Nat → Nat} (hσ : HonestStore p s σ r) (I2 : Ideal) (pb : Bits) (pe : List F)
    (hpb : pb.length = p.M * W) (hpe : pe.length = p.M)
    (hI2 : I2.bools (b + 2) = some (inBundle me (σ.bits s.bits) pb)) :
    Holds p b f
      (bothFields me I2 ((List.range p.M).map (fOf p f 0)) ((List.range p.M).map (fOf p f 1)) (σ.elems s.elems) pe)
      (inBundle me (σ.bits s.bits) pb) (inVals p me r (inBundle me (σ.bits s.bits) pb) pe) := by
  have hme : (σ.elems s.elems).length = p.M := by rw [hσ.elems]; simp
  have hmv : ∀ c, c < p.M → (σ.elems s.elems).getD c 0 = TlsMpc.FieldDag.ofNat (r c) := by
    intro c hc
    rw [hσ.elems, getD_map_range _ _ _ _ hc]
  have hla : (if me = Party.a then σ.elems s.elems else pe).length = p.M := by split <;> assumption
  have hlb : (if me = Party.a then pe else σ.elems s.elems).length = p.M := by split <;> assumption
  obtain ⟨a1, a2, a3⟩ := setFields_block I2 (fOf p f 0) f p.M (if me = Party.a then σ.elems s.elems else pe)
    (fun i _ => by simp [fOf]) hla
  obtain ⟨c1, c2, c3⟩ := setFields_block
    (I2.setFields ((List.range p.M).map (fOf p f 0)) (if me = Party.a then σ.elems s.elems else pe))
    (fOf p f 1) (f + p.M) p.M (if me = Party.a then pe else σ.elems s.elems)
    (fun i _ => by simp [fOf]) hlb
  refine ⟨?_, ?_, fun _ _ => rfl, fun o ho c hc => ?_⟩
  · show (bothFields me I2 _ _ _ _).bools (b + 2) = _
    unfold bothFields
    rw [c1, a1]
    exact hI2
  · unfold inBundle
    have := hσ.bits_length
    rw [List.length_append]
    split <;> omega
  · unfold bothFields
    have ho' : o = 0 ∨ o = 1 := by omega
    rcases ho' with rfl | rfl
    · have e : (fOf p f 0 c).id = f + c := by simp [fOf]
      rw [e, c2 _ (Or.inl (by omega)), a3 c hc]
      cases me
      · show some ((σ.elems s.elems).getD c 0) = some (TlsMpc.FieldDag.ofNat (r c))
        rw [hmv c hc]
      · simp [inVals, own]
    · have e : (fOf p f 1 c).id = f + p.M + c := by simp [fOf]
      rw [e, c3 c hc]
      cases me
      · simp [inVals, own]
      · show some ((σ.elems s.elems).getD c 0) = some (TlsMpc.FieldDag.ofNat (r c))
        rw [hmv c hc]

theorem inVals_honest {σ : Store} {r : Nat → Nat} (hσ : HonestStore p s σ r) (pb : Bits) (pe : List F)
    (hpb : pb.length = p.M * W) (c : Nat) (hc : c < p.M) :
    (inVals p me r (inBundle me (σ.bits s.bits) pb) pe).bits (own me) c = word (r c) := by
  have hl := hσ.bits_length
  show (wordAt p (own me) c).map ((inBundle me (σ.bits s.bits) pb).getD · false) = _
  cases me
  · rw [show inBundle Party.a (σ.bits s.bits) pb = σ.bits s.bits ++ pb from rfl,
      word_of_bundle p _ _ hl hpb (own .a) c (by decide) hc]
    exact hσ.chunk c hc
  · rw [show inBundle Party.b (σ.bits s.bits) pb = pb ++ σ.bits s.bits from rfl,
      word_of_bundle p _ _ hpb hl (own .b) c (by decide) hc]
    exact hσ.chunk c hc

theorem inVals_other {σ : Store} {r : Nat → Nat} (hσ : HonestStore p s σ r) (pb : Bits) (pe : List F)
    (hpb : pb.length = p.M * W) (o : Nat) (ho : o < 2) (hne : o ≠ own me) (c : Nat) (hc : c < p.M) :
    (inVals p me r (inBundle me (σ.bits s.bits) pb) pe).bits o c = (pb.drop (c * W)).take W ∧
      (inVals p me r (inBundle me (σ.bits s.bits) pb) pe).elem o c = pe.getD c 0 := by
  have hl := hσ.bits_length
  refine ⟨?_, by simp [inVals, hne]⟩
  show (wordAt p o c).map ((inBundle me (σ.bits s.bits) pb).getD · false) = _
  cases me
  · have ho1 : o = 1 := by simp only [own] at hne; omega
    subst ho1
    rw [show inBundle Party.a (σ.bits s.bits) pb = σ.bits s.bits ++ pb from rfl,
      word_of_bundle p _ _ hl hpb 1 c (by decide) hc]
    rfl
  · have ho0 : o = 0 := by simp only [own] at hne; omega
    subst ho0
    rw [show inBundle Party.b (σ.bits s.bits) pb = pb ++ σ.bits s.bits from rfl,
      word_of_bundle p _ _ hpb hl 0 c (by decide) hc]
    rfl

end Inputs

/-! ## Two candidate sets that differ only in the honest owner's -/

/-- The candidates `x` and `x'` of two runs: the honest owner `oH`'s are `r` and `r'` (canonical,
consistent in both engines); the other owner's are the same. -/
structure Twin (p : Params) (oH : Nat) (r r' : Nat → Nat) (x x' : Vals) : Prop where
  ho : oH < 2
  bitsH : ∀ c, c < p.M → x.bits oH c = word (r c)
  bitsH' : ∀ c, c < p.M → x'.bits oH c = word (r' c)
  elemH : ∀ c, c < p.M → x.elem oH c = TlsMpc.FieldDag.ofNat (r c)
  elemH' : ∀ c, c < p.M → x'.elem oH c = TlsMpc.FieldDag.ofNat (r' c)
  other : ∀ o, o < 2 → o ≠ oH → ∀ c, c < p.M → x'.bits o c = x.bits o c ∧ x'.elem o c = x.elem o c
  canon : ∀ c, c < p.M → r c < P
  canon' : ∀ c, c < p.M → r' c < P

theorem ofNat_add (a b : Nat) :
    TlsMpc.FieldDag.ofNat a + TlsMpc.FieldDag.ofNat b = TlsMpc.FieldDag.ofNat ((a + b) % P) := by
  apply Fin.ext
  rw [fadd_val, ofNat_val, ofNat_val, ofNat_val, Nat.mod_mod, ← Nat.add_mod]

namespace Twin

variable {p : Params} {oH : Nat} {r r' : Nat → Nat} {x x' : Vals}

/-- **The cut opens the same** when `r' = r` on the cut. -/
theorem cut_same (t : Twin p oH r r' x x') (cut : List Nat) (hcut : ∀ c ∈ cut, c < p.M ∧ r' c = r c) :
    cutRel x' cut = cutRel x cut := by
  unfold cutRel
  apply flatMap_congr'
  intro o ho
  apply List.map_congr_left
  intro c hc
  obtain ⟨hcM, hrr⟩ := hcut c hc
  by_cases hoH : o = oH
  · subst hoH
    rw [t.bitsH c hcM, t.bitsH' c hcM, t.elemH c hcM, t.elemH' c hcM, hrr]
  · obtain ⟨h1, h2⟩ := t.other o (owners_lt ho) hoH c hcM
    rw [h1, h2]

/-- **The buckets open the same** when in every pair the sum of the reference and the member is
the same mod p (the cancelling shift of `hiding_releases`). -/
theorem bucket_same (t : Twin p oH r r' x x') (mem : Nat → Nat → Nat) (ps : List (Nat × Nat × Nat))
    (hps : ∀ e ∈ ps, e.1 < 2 ∧ mem e.2.1 0 < p.M ∧ mem e.2.1 e.2.2 < p.M ∧
      (r' (mem e.2.1 0) + r' (mem e.2.1 e.2.2)) % P = (r (mem e.2.1 0) + r (mem e.2.1 e.2.2)) % P) :
    bucketRel x' mem ps = bucketRel x mem ps := by
  unfold bucketRel
  apply List.map_congr_left
  intro e he
  obtain ⟨ho, h0, h1, hsum⟩ := hps e he
  by_cases hoH : e.1 = oH
  · rw [hoH]
    have c0 := t.canon _ h0
    have c1 := t.canon _ h1
    have c0' := t.canon' _ h0
    have c1' := t.canon' _ h1
    have hlt : ∀ n, n < P → n < 2 ^ 255 := fun n hn => by have := P_lt_two_pow; omega
    simp only [Vals.val, t.bitsH _ h0, t.bitsH _ h1, t.bitsH' _ h0, t.bitsH' _ h1, t.elemH _ h0, t.elemH _ h1,
      t.elemH' _ h0, t.elemH' _ h1, natOf_word _ (hlt _ c0), natOf_word _ (hlt _ c1), natOf_word _ (hlt _ c0'),
      natOf_word _ (hlt _ c1'), addModSpec_canonical _ _ c0 c1, addModSpec_canonical _ _ c0' c1', ofNat_add, hsum]
  · obtain ⟨a1, a2⟩ := t.other e.1 ho hoH _ h0
    obtain ⟨b1, b2⟩ := t.other e.1 ho hoH _ h1
    simp only [Vals.val, a1, a2, b1, b2]

theorem val_honest (t : Twin p oH r r' x x') (c : Nat) (hc : c < p.M) :
    natOf (x.bits oH c) = r c ∧ natOf (x'.bits oH c) = r' c := by
  have hlt : ∀ n, n < P → n < 2 ^ 255 := fun n hn => by have := P_lt_two_pow; omega
  rw [t.bitsH c hc, t.bitsH' c hc, natOf_word _ (hlt _ (t.canon c hc)), natOf_word _ (hlt _ (t.canon' c hc))]
  exact ⟨rfl, rfl⟩

/-- **The flags are the same** when every bit block's reference is at least 32 in both runs or in
neither (the honest references are canonical in both; the other owner's are the same). -/
theorem flags_same (t : Twin p oH r r' x x') (hx : x.Wide) (hx' : x'.Wide) (π₁ π₂ : List Nat)
    (href : ∀ j, j < p.N → refOf p π₁ π₂ j < p.M)
    (h32 : ∀ j, j < p.bits → (32 ≤ r' (refOf p π₁ π₂ j) ↔ 32 ≤ r (refOf p π₁ π₂ j))) :
    flagsOf p π₁ π₂ x' = flagsOf p π₁ π₂ x := by
  unfold flagsOf
  apply List.map_congr_left
  intro j hj
  have hjN := List.mem_range.mp hj
  have hc := href j hjN
  obtain ⟨v1, v2⟩ := t.val_honest _ hc
  have k1 := t.canon _ hc
  have k2 := t.canon' _ hc
  have ho' : oH = 0 ∨ oH = 1 := by have := t.ho; omega
  unfold outOf
  split
  · next hjb =>
    have h3 := h32 j hjb
    unfold pairOf
    rw [finalizeBits_flag _ _ (hx' 0 _) (hx' 1 _), finalizeBits_flag _ _ (hx 0 _) (hx 1 _)]
    rcases ho' with rfl | rfl
    · obtain ⟨o1, -⟩ := t.other 1 (by omega) (by omega) _ hc
      rw [v1, v2, o1]
      simp [k1, k2, h3]
    · obtain ⟨o1, -⟩ := t.other 0 (by omega) (by omega) _ hc
      rw [v1, v2, o1]
      simp [k1, k2, h3]
  · unfold pairOf
    rw [finalizeMask_flag _ _ (hx' 0 _) (hx' 1 _), finalizeMask_flag _ _ (hx 0 _) (hx 1 _)]
    rcases ho' with rfl | rfl
    · obtain ⟨o1, -⟩ := t.other 1 (by omega) (by omega) _ hc
      rw [v1, v2, o1]
      simp [k1, k2]
    · obtain ⟨o1, -⟩ := t.other 0 (by omega) (by omega) _ hc
      rw [v1, v2, o1]
      simp [k1, k2]

end Twin

/-! ## The bit blocks open the same -/

theorem fsub_self (a : F) : a - a = 0 := by
  apply Fin.ext
  rw [Fin.val_sub]
  have := a.isLt
  show (modulus - a.val + a.val) % modulus = 0
  rw [Nat.sub_add_cancel (Nat.le_of_lt this), Nat.mod_self]

theorem bitValue_check (x : Bool) :
    X25519.bitValue x * (X25519.bitValue x - TlsMpc.FieldDag.ofNat 1) = 0 := by
  cases x <;> decide

theorem map_bits_range (bs : Bits) (hl : bs.length = 255) :
    (List.range 255).map (fun i => X25519.bitValue (bs.getD i false)) = bs.map X25519.bitValue := by
  have h := map_getD_all bs false
  rw [hl] at h
  conv => rhs; rw [← h]
  rw [List.map_map]
  rfl

/-- An honest owner's coins (the bits of its canonical, consistent reference) recompose to its
reference: the opened value is 0, and so is every bit check. -/
theorem honest_rec (n : Nat) (hn : n < P) :
    TlsMpc.FieldBits.hornerValue ((List.range 255).map fun i => X25519.bitValue ((word n).getD i false)) -
      TlsMpc.FieldDag.ofNat n = 0 := by
  rw [map_bits_range _ (length_word n), horner_bits, natOf_word n (by have := P_lt_two_pow; omega)]
  exact fsub_self _

/-- **The bit-block phase opens the same**: the honest owner's values are 0 in both runs; the
other owner's coins and references are the same. -/
theorem bitZ_same {p : Params} {oH : Nat} {r r' : Nat → Nat} {x x' : Vals} (t : Twin p oH r r' x x')
    (π₁ π₂ : List Nat) (κ κ' : Nat → Nat → Nat → F) (href : ∀ j, j < p.bits → refOf p π₁ π₂ j < p.M)
    (hκ : ∀ j, j < p.bits → ∀ i, i < W →
      κ oH j i = X25519.bitValue ((word (r (refOf p π₁ π₂ j))).getD i false))
    (hκ' : ∀ j, j < p.bits → ∀ i, i < W →
      κ' oH j i = X25519.bitValue ((word (r' (refOf p π₁ π₂ j))).getD i false))
    (hadv : ∀ o, o < 2 → o ≠ oH → ∀ j, j < p.bits → ∀ i, i < W → κ' o j i = κ o j i) :
    bitZ p π₁ π₂ κ' x' = bitZ p π₁ π₂ κ x := by
  have hrow : ∀ (k : Nat → Nat → Nat → F) (rr : Nat → Nat), (∀ j, j < p.bits → ∀ i, i < W →
      k oH j i = X25519.bitValue ((word (rr (refOf p π₁ π₂ j))).getD i false)) → ∀ j, j < p.bits →
      (List.range 255).map (k oH j) =
        (List.range 255).map fun i => X25519.bitValue ((word (rr (refOf p π₁ π₂ j))).getD i false) := by
    intro k rr hk j hj
    apply List.map_congr_left
    intro i hi
    exact hk j hj i (List.mem_range.mp hi)
  have e1 : (owners.flatMap fun o => (List.range p.bits).map (recVal p π₁ π₂ κ' x' o)) =
      (owners.flatMap fun o => (List.range p.bits).map (recVal p π₁ π₂ κ x o)) := by
    apply flatMap_congr'
    intro o ho
    apply List.map_congr_left
    intro j hj
    have hjb := List.mem_range.mp hj
    have hc := href j hjb
    unfold recVal
    by_cases hoH : o = oH
    · subst hoH
      rw [hrow κ' r' hκ' j hjb, hrow κ r hκ j hjb, t.elemH' _ hc, t.elemH _ hc,
        honest_rec _ (t.canon' _ hc), honest_rec _ (t.canon _ hc)]
    · have e : (List.range 255).map (κ' o j) = (List.range 255).map (κ o j) := by
        apply List.map_congr_left
        intro i hi
        exact hadv o (owners_lt ho) hoH j hjb i (List.mem_range.mp hi)
      rw [e, (t.other o (owners_lt ho) hoH _ hc).2]
  have e2 : (owners.flatMap fun o => (List.range p.bits).flatMap fun j => (List.range W).map (chkVal κ' o j)) =
      (owners.flatMap fun o => (List.range p.bits).flatMap fun j => (List.range W).map (chkVal κ o j)) := by
    apply flatMap_congr'
    intro o ho
    apply flatMap_congr'
    intro j hj
    have hjb := List.mem_range.mp hj
    apply List.map_congr_left
    intro i hi
    have hiW := List.mem_range.mp hi
    unfold chkVal
    by_cases hoH : o = oH
    · subst hoH
      rw [hκ' j hjb i hiW, hκ j hjb i hiW, bitValue_check, bitValue_check]
    · rw [hadv o (owners_lt ho) hoH j hjb i hiW]
  unfold bitZ
  rw [e1, e2]

/-! ## The coin inputs -/

theorem mul_step (j k : Nat) (h : j < k) : j * W + W ≤ k * W := by
  have := Nat.mul_le_mul_right W (show j + 1 ≤ k by omega)
  simpa [Nat.succ_mul] using this

theorem coin_id (p : Params) (f o j i : Nat) :
    (coinH p f o j i).id = coinBase p f + o * (p.bits * W) + j * W + i := rfl

/-- One block's coin inputs: the honest owner's handles hold its coins, the other owner's what it
input; nothing else changes. -/
theorem coin_step (p : Params) (f : Nat) (me : Party) (I : Ideal) (j : Nat) (hj : j < p.bits) (mine pe : List F)
    (hm : mine.length = W) (hpe : pe.length = W) :
    (bothFields me I ((List.range W).map (coinH p f 0 j)) ((List.range W).map (coinH p f 1 j)) mine pe).bools =
        I.bools ∧
    (∀ i, i < W → (bothFields me I ((List.range W).map (coinH p f 0 j)) ((List.range W).map (coinH p f 1 j)) mine
      pe).fields (coinH p f (own me) j i).id = some (mine.getD i 0)) ∧
    (∀ i, i < W → (bothFields me I ((List.range W).map (coinH p f 0 j)) ((List.range W).map (coinH p f 1 j)) mine
      pe).fields (coinH p f (1 - own me) j i).id = some (pe.getD i 0)) ∧
    (∀ id, (id < coinBase p f + j * W ∨
        (coinBase p f + j * W + W ≤ id ∧ id < coinBase p f + p.bits * W + j * W) ∨
        coinBase p f + p.bits * W + j * W + W ≤ id) →
      (bothFields me I ((List.range W).map (coinH p f 0 j)) ((List.range W).map (coinH p f 1 j)) mine pe).fields id =
        I.fields id) := by
  have hjW := mul_step j p.bits hj
  have hla : (if me = Party.a then mine else pe).length = W := by split <;> assumption
  have hlb : (if me = Party.a then pe else mine).length = W := by split <;> assumption
  obtain ⟨a1, a2, a3⟩ := setFields_block I (coinH p f 0 j) (coinBase p f + j * W) W
    (if me = Party.a then mine else pe) (fun i _ => by simp [coinH]) hla
  obtain ⟨c1, c2, c3⟩ := setFields_block
    (I.setFields ((List.range W).map (coinH p f 0 j)) (if me = Party.a then mine else pe))
    (coinH p f 1 j) (coinBase p f + p.bits * W + j * W) W (if me = Party.a then pe else mine)
    (fun i _ => by simp [coinH]) hlb
  unfold bothFields
  refine ⟨by rw [c1, a1], fun i hi => ?_, fun i hi => ?_, fun id hid => ?_⟩
  · cases me
    · have e : (coinH p f (own Party.a) j i).id = coinBase p f + j * W + i := by simp [coinH, own]
      rw [e, c2 _ (Or.inl (by omega)), a3 i hi]
      rfl
    · have e : (coinH p f (own Party.b) j i).id = coinBase p f + p.bits * W + j * W + i := by simp [coinH, own]
      rw [e, c3 i hi]
      rfl
  · cases me
    · have e : (coinH p f (1 - own Party.a) j i).id = coinBase p f + p.bits * W + j * W + i := by simp [coinH, own]
      rw [e, c3 i hi]
      rfl
    · have e : (coinH p f (1 - own Party.b) j i).id = coinBase p f + j * W + i := by simp [coinH, own]
      rw [e, c2 _ (Or.inl (by omega)), a3 i hi]
      rfl
  · rw [c2 id (by omega), a2 id (by omega)]

/-- A coin of an earlier block is outside block `k`'s two ranges. -/
theorem coin_frame (p : Params) (f o j k i : Nat) (ho : o < 2) (hj : j < k) (hk : k < p.bits) (hi : i < W) :
    (coinH p f o j i).id < coinBase p f + k * W ∨
      (coinBase p f + k * W + W ≤ (coinH p f o j i).id ∧ (coinH p f o j i).id < coinBase p f + p.bits * W + k * W) ∨
      coinBase p f + p.bits * W + k * W + W ≤ (coinH p f o j i).id := by
  have h1 := mul_step j k hj
  have h2 := mul_step k p.bits hk
  have ho' : o = 0 ∨ o = 1 := by omega
  rcases ho' with rfl | rfl
  · have e : (coinH p f 0 j i).id = coinBase p f + j * W + i := by simp [coinH]
    rw [e]
    omega
  · have e : (coinH p f 1 j i).id = coinBase p f + p.bits * W + j * W + i := by simp [coinH]
    rw [e]
    omega

/-- The two runs after the coin inputs of the first `k` bit blocks: the honest owner's coins are
its stores' (`hc`, `hc'`), the other owner's are the same in both runs, and nothing below the
coins changed. -/
structure CoinInv (p : Params) (f : Nat) (me : Party) (hc hc' : Nat → Nat → F) (I0 I0' I I' : Ideal) (k : Nat) :
    Prop where
  hon : ∀ j, j < k → ∀ i, i < W → I.fields (coinH p f (own me) j i).id = some (hc j i)
  hon' : ∀ j, j < k → ∀ i, i < W → I'.fields (coinH p f (own me) j i).id = some (hc' j i)
  adv : ∀ j, j < k → ∀ i, i < W →
    ∃ c, I.fields (coinH p f (1 - own me) j i).id = some c ∧ I'.fields (coinH p f (1 - own me) j i).id = some c
  low : ∀ id, id < coinBase p f → I.fields id = I0.fields id
  low' : ∀ id, id < coinBase p f → I'.fields id = I0'.fields id
  bools : I.bools = I0.bools
  bools' : I'.bools = I0'.bools

theorem runLocal_free1 (E : Env) (h : BoolH) (I : Ideal) : runLocal E [.freeBool h] I = some (I.dropBool h) := by
  simp only [runLocal, localStep_free]

theorem runLocal_free2 (E : Env) (h₁ h₂ : BoolH) (I : Ideal) :
    runLocal E [.freeBool h₁, .freeBool h₂] I = some ((I.dropBool h₁).dropBool h₂) := by
  simp only [runLocal, localStep_free]

theorem getD_map_lt {α β : Type} (g : α → β) (l : List α) (i : Nat) (d : α) (d' : β) (hi : i < l.length) :
    (l.map g).getD i d' = g (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD, hi]

/-! ## The phases agree -/

section Phases

variable (E : Env) (me : Party) (adv : Adversary) (p : Params) (b f : Nat)

theorem coin_inputs_agree {α : Type} {Q : α → Store → Ideal → Store → Ideal → Prop} (s : Slots) (π₁ π₂ : List Nat)
    (rest : Script α) (σ σ' : Store) (vD : List Release) (I0 I0' : Ideal)
    (hst : ∀ j, j < p.bits → (σ.elems (s.coins + member p π₁ π₂ j 0)).length = W ∧
      coinsOk .coins (σ.elems (s.coins + member p π₁ π₂ j 0)) = true)
    (hst' : ∀ j, j < p.bits → (σ'.elems (s.coins + member p π₁ π₂ j 0)).length = W ∧
      coinsOk .coins (σ'.elems (s.coins + member p π₁ π₂ j 0)) = true)
    (hrest : ∀ I I', CoinInv p f me (fun j i => (σ.elems (s.coins + member p π₁ π₂ j 0)).getD i 0)
        (fun j i => (σ'.elems (s.coins + member p π₁ π₂ j 0)).getD i 0) I0 I0' I I' p.bits →
      Agree Q (withAdv E me adv rest σ I vD) (withAdv E me adv rest σ' I' vD)) :
    ∀ n, n ≤ p.bits → ∀ I I', CoinInv p f me (fun j i => (σ.elems (s.coins + member p π₁ π₂ j 0)).getD i 0)
        (fun j i => (σ'.elems (s.coins + member p π₁ π₂ j 0)).getD i 0) I0 I0' I I' (p.bits - n) →
      Agree Q
        (withAdv E me adv (seqs ((List.range' (p.bits - n) n).map fun j =>
          (.fieldInput ((List.range W).map (coinH p f 0 j)) ((List.range W).map (coinH p f 1 j)) .coins false
            (s.coins + member p π₁ π₂ j 0) : Instr)) rest) σ I vD)
        (withAdv E me adv (seqs ((List.range' (p.bits - n) n).map fun j =>
          (.fieldInput ((List.range W).map (coinH p f 0 j)) ((List.range W).map (coinH p f 1 j)) .coins false
            (s.coins + member p π₁ π₂ j 0) : Instr)) rest) σ' I' vD)
  | 0, _, I, I', hinv => by
    simp only [List.range'_zero, List.map_nil, seqs_nil]
    exact hrest I I' (by simpa using hinv)
  | n + 1, hn, I, I', hinv => by
    have e : List.range' (p.bits - (n + 1)) (n + 1) = (p.bits - (n + 1)) :: List.range' (p.bits - n) n := by
      rw [List.range'_succ]
      congr 1
      congr 1
      omega
    rw [e, List.map_cons, seqs_cons]
    have hj : p.bits - (n + 1) < p.bits := by omega
    obtain ⟨hl, hco⟩ := hst _ hj
    obtain ⟨hl', hco'⟩ := hst' _ hj
    refine Agree.fieldInput E me adv _ _ .coins false _ _ σ σ' I I' vD (by simp) (by simpa using hl) hco
      (by simpa using hl') hco' (fun pe hpe _ => ?_)
    have hpe' : pe.length = W := by simpa using hpe
    obtain ⟨s1, s2, s3, s4⟩ := coin_step p f me I _ hj _ pe hl hpe'
    obtain ⟨t1, t2, t3, t4⟩ := coin_step p f me I' _ hj _ pe hl' hpe'
    refine coin_inputs_agree s π₁ π₂ rest σ σ' vD I0 I0' hst hst' hrest n (by omega) _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hjn i hi
      by_cases hjk : j = p.bits - (n + 1)
      · subst hjk
        exact s2 i hi
      · rw [s4 _ (coin_frame p f (own me) j _ i (own_lt me) (by omega) hj hi)]
        exact hinv.hon j (by omega) i hi
    · intro j hjn i hi
      by_cases hjk : j = p.bits - (n + 1)
      · subst hjk
        exact t2 i hi
      · rw [t4 _ (coin_frame p f (own me) j _ i (own_lt me) (by omega) hj hi)]
        exact hinv.hon' j (by omega) i hi
    · intro j hjn i hi
      by_cases hjk : j = p.bits - (n + 1)
      · subst hjk
        exact ⟨pe.getD i 0, s3 i hi, t3 i hi⟩
      · have ho : 1 - own me < 2 := by omega
        rw [s4 _ (coin_frame p f (1 - own me) j _ i ho (by omega) hj hi),
          t4 _ (coin_frame p f (1 - own me) j _ i ho (by omega) hj hi)]
        exact hinv.adv j (by omega) i hi
    · intro id hid
      rw [s4 id (Or.inl (by omega))]
      exact hinv.low id hid
    · intro id hid
      rw [t4 id (Or.inl (by omega))]
      exact hinv.low' id hid
    · rw [s1]
      exact hinv.bools
    · rw [t1]
      exact hinv.bools'

theorem cut_agree (π₁ : List Nat) (σ σ' : Store) (I I' : Ideal) (vD : List Release) (v v' : Bits) (x x' : Vals)
    (h : Holds p b f I v x) (h' : Holds p b f I' v' x') (hπ : ∀ c ∈ cutOf p π₁, c < p.M)
    (heq : cutRel x' (cutOf p π₁) = cutRel x (cutOf p π₁)) :
    Agree (fun _ s1 i s1' i' => s1 = σ ∧ s1' = σ' ∧ Holds p b f i v x ∧ Holds p b f i' v' x')
      (withAdv E me adv (cutPhase p b f π₁) σ I vD) (withAdv E me adv (cutPhase p b f π₁) σ' I' vD) := by
  obtain ⟨c1, c2⟩ := h.cut E π₁ hπ
  obtain ⟨c1', c2'⟩ := h'.cut E π₁ hπ
  rw [heq] at c1' c2'
  unfold cutPhase
  refine Agree.locals E me adv _ σ σ' [.pick ⟨b + 3⟩ ⟨b + 2⟩ (cutBits p π₁)] (by simp [isLocal]) I I' _ _ vD
    c1 c1' ?_
  refine Agree.openFieldThen E me adv _ _ _ σ σ' _ _ vD _ c2 c2' ?_
  refine Agree.openThen E me adv ⟨b + 3⟩ _ _ σ σ' _ _ _ ((cutRel x (cutOf p π₁)).map Prod.fst).flatten
    (by simp [Ideal.setBool]) (by simp [Ideal.setBool]) ?_
  split
  · refine Agree.locals E me adv _ σ σ' _ (by simp [isLocal]) _ _ _ _ _ (runLocal_free1 E _ _)
      (runLocal_free1 E _ _) ?_
    refine Agree.done E me adv _ _ _ _ _ _ ⟨rfl, rfl, h.frame ?_ (fun _ _ => rfl), h'.frame ?_ (fun _ _ => rfl)⟩
    · simp [Ideal.setBool, Ideal.dropBool]
    · simp [Ideal.setBool, Ideal.dropBool]
  · exact Agree.abort E me adv _ _ _ _ _ _

theorem bucket_agree (hW : WordLoaded E) (π₁ π₂ : List Nat) (σ σ' : Store) (I I' : Ideal) (vD : List Release)
    (v v' : Bits) (x x' : Vals) (h : Holds p b f I v x) (h' : Holds p b f I' v' x')
    (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M)
    (heq : bucketRel x' (member p π₁ π₂) (pairs p) = bucketRel x (member p π₁ π₂) (pairs p)) :
    Agree (fun _ s1 i s1' i' => s1 = σ ∧ s1' = σ' ∧ Holds p b f i v x ∧ Holds p b f i' v' x')
      (withAdv E me adv (bucketPhase p b f π₁ π₂) σ I vD) (withAdv E me adv (bucketPhase p b f π₁ π₂) σ' I' vD) := by
  obtain ⟨I3, g1, g2, g3, g4, g5⟩ := h.bucket E hW π₁ π₂ hπ₁ hM
  obtain ⟨I3', g1', g2', g3', g4', g5'⟩ := h'.bucket E hW π₁ π₂ hπ₁ hM
  rw [heq] at g2' g3'
  unfold bucketPhase
  refine Agree.locals E me adv _ σ σ' _ (bucketBlock_local p b f π₁ π₂) I I' I3 I3' vD g1 g1' ?_
  refine Agree.openFieldThen E me adv _ _ _ σ σ' _ _ vD _ g3 g3' ?_
  refine Agree.openThen E me adv ⟨b + 5⟩ _ _ σ σ' _ _ _ _ g2 g2' ?_
  split
  · refine Agree.locals E me adv _ σ σ' _ (by simp [isLocal]) _ _ _ _ _ (runLocal_free2 E _ _ _)
      (runLocal_free2 E _ _ _) ?_
    refine Agree.done E me adv _ _ _ _ _ _ ⟨rfl, rfl, h.frame ?_ g5, h'.frame ?_ g5'⟩
    · simp [Ideal.dropBool, g4]
    · simp [Ideal.dropBool, g4']
  · exact Agree.abort E me adv _ _ _ _ _ _

/-- The bit-block phase after the coin inputs. -/
theorem bit_tail_agree (hP : ProgsLoaded E) (π₁ π₂ : List Nat) (σ σ' : Store) (I I' : Ideal) (vD : List Release)
    (κ κ' : Nat → Nat → Nat → F) (x x' : Vals) (bundle bundle' : Bits)
    (hc : CoinsHold p f I κ) (hc' : CoinsHold p f I' κ')
    (hfld : ∀ o, o < 2 → ∀ j, j < p.bits →
      I.fields (fOf p f o (refOf p π₁ π₂ j)).id = some (x.elem o (refOf p π₁ π₂ j)))
    (hfld' : ∀ o, o < 2 → ∀ j, j < p.bits →
      I'.fields (fOf p f o (refOf p π₁ π₂ j)).id = some (x'.elem o (refOf p π₁ π₂ j)))
    (hz : bitZ p π₁ π₂ κ' x' = bitZ p π₁ π₂ κ x)
    (hb : I.bools (b + 10) = some bundle) (hb' : I'.bools (b + 10) = some bundle')
    (hlen : bundle.length = p.N * 256) (hlen' : bundle'.length = p.N * 256) (hbits : p.bits ≤ p.N) :
    Agree (fun _ _ _ _ _ => True)
      (withAdv E me adv
        (seq (.program recomposeName (2 * p.bits) (recIns p f π₁ π₂) [] (recOuts p f) Label.bitBlockChecks) <|
          seq (.program bitCheckName (2 * (p.bits * W)) (allCoins p f) [] (chkOuts p f) Label.bitBlockChecks) <|
          openFieldThen (recOuts p f ++ chkOuts p f) Label.bitBlockChecks fun z =>
          if z.all (· == 0) then
            seq (.program bitXorName (p.bits * W) (xorIns p f) [] (xorOuts p f) Label.bitBlockChecks) <|
            seqs (pairSlices p b) (.done ())
          else .abort "bit block inconsistent with verified reference") σ I vD)
      (withAdv E me adv
        (seq (.program recomposeName (2 * p.bits) (recIns p f π₁ π₂) [] (recOuts p f) Label.bitBlockChecks) <|
          seq (.program bitCheckName (2 * (p.bits * W)) (allCoins p f) [] (chkOuts p f) Label.bitBlockChecks) <|
          openFieldThen (recOuts p f ++ chkOuts p f) Label.bitBlockChecks fun z =>
          if z.all (· == 0) then
            seq (.program bitXorName (p.bits * W) (xorIns p f) [] (xorOuts p f) Label.bitBlockChecks) <|
            seqs (pairSlices p b) (.done ())
          else .abort "bit block inconsistent with verified reference") σ' I' vD) := by
  obtain ⟨pr, vi, vo, pc, vi2, vo2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
    coins_programs E hP p f π₁ π₂ I κ x hc hfld
  obtain ⟨pr', vi', vo', pc', vi2', vo2', q1', q2', q3', q4', q5', q6', q7', q8', q9', q10', q11'⟩ :=
    coins_programs E hP p f π₁ π₂ I' κ' x' hc' hfld'
  have epr : pr' = pr := Option.some.inj (q1'.symm.trans q1)
  have epc : pc' = pc := Option.some.inj (q5'.symm.trans q5)
  subst epr
  subst epc
  rw [hz] at q9'
  refine Agree.program E me adv _ _ _ _ _ _ _ σ σ' I I' vD pr' vi [] vo vi' [] vo' [] q1 q2 rfl q3 q4 q2' rfl q3' q4' ?_
  refine Agree.program E me adv _ _ _ _ _ _ _ σ σ' _ _ _ pc' vi2 [] vo2 vi2' [] vo2' [] q5 q6 rfl q7 q8 q6' rfl
    q7' q8' ?_
  refine Agree.openFieldThen E me adv _ _ _ σ σ' _ _ _ _ q9 q9' ?_
  split
  · have hcJ : CoinsHold p f ((I.setFields (recOuts p f) vo).setFields (chkOuts p f) vo2) κ := by
      intro o ho j hj i hi
      rw [q11 _ (by have := coin_lt p o j i ho hj hi; rw [coin_id]; omega)]
      exact hc o ho j hj i hi
    have hcJ' : CoinsHold p f ((I'.setFields (recOuts p f) vo').setFields (chkOuts p f) vo2') κ' := by
      intro o ho j hj i hi
      rw [q11' _ (by have := coin_lt p o j i ho hj hi; rw [coin_id]; omega)]
      exact hc' o ho j hj i hi
    obtain ⟨px, wi, wo, x1, x2, x3, x4, x5, -, -⟩ := coins_xor E hP p f _ κ hcJ
    obtain ⟨px', wi', wo', x1', x2', x3', x4', x5', -, -⟩ := coins_xor E hP p f _ κ' hcJ'
    have epx : px' = px := Option.some.inj (x1'.symm.trans x1)
    subst epx
    refine Agree.program E me adv _ _ _ _ _ _ _ σ σ' _ _ _ px' wi [] wo wi' [] wo' [] x1 x2 rfl x3 x4 x2' rfl
      x3' x4' ?_
    obtain ⟨J, y1, -, -, -⟩ := pairSlices_block E p b _ bundle (by rw [x5, q10]; exact hb) hlen hbits
    obtain ⟨J', y1', -, -, -⟩ := pairSlices_block E p b _ bundle' (by rw [x5', q10']; exact hb') hlen' hbits
    refine Agree.locals E me adv _ σ σ' _ (pairSlices_local p b) _ _ J J' _ y1 y1' ?_
    exact Agree.done E me adv _ _ _ _ _ _ trivial
  · exact Agree.abort E me adv _ _ _ _ _ _

theorem bit_agree (hP : ProgsLoaded E) (s : Slots) (π₁ π₂ : List Nat) (σ σ' : Store) (I I' : Ideal)
    (vD : List Release) (x x' : Vals) (r r' : Nat → Nat) (bundle bundle' : Bits)
    (t : Twin p (own me) r r' x x') (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M)
    (hσ : ∀ c, c < p.M → σ.elems (s.coins + c) = (word (r c)).map X25519.bitValue)
    (hσ' : ∀ c, c < p.M → σ'.elems (s.coins + c) = (word (r' c)).map X25519.bitValue)
    (hfld : ∀ o, o < 2 → ∀ c, c < p.M → I.fields (fOf p f o c).id = some (x.elem o c))
    (hfld' : ∀ o, o < 2 → ∀ c, c < p.M → I'.fields (fOf p f o c).id = some (x'.elem o c))
    (hb : I.bools (b + 10) = some bundle) (hb' : I'.bools (b + 10) = some bundle')
    (hlen : bundle.length = p.N * 256) (hlen' : bundle'.length = p.N * 256) (hbits : p.bits ≤ p.N) :
    Agree (fun _ _ _ _ _ => True) (withAdv E me adv (bitPhase p b f s π₁ π₂) σ I vD)
      (withAdv E me adv (bitPhase p b f s π₁ π₂) σ' I' vD) := by
  have hml := member_lt p π₁ π₂ hπ₁ hM
  unfold bitPhase
  split
  · exact Agree.done E me adv _ _ _ _ _ _ trivial
  · have key := coin_inputs_agree E me adv p f (Q := fun _ _ _ _ _ => True) s π₁ π₂
      (seq (.program recomposeName (2 * p.bits) (recIns p f π₁ π₂) [] (recOuts p f) Label.bitBlockChecks) <|
        seq (.program bitCheckName (2 * (p.bits * W)) (allCoins p f) [] (chkOuts p f) Label.bitBlockChecks) <|
        openFieldThen (recOuts p f ++ chkOuts p f) Label.bitBlockChecks fun z =>
        if z.all (· == 0) then
          seq (.program bitXorName (p.bits * W) (xorIns p f) [] (xorOuts p f) Label.bitBlockChecks) <|
          seqs (pairSlices p b) (.done ())
        else .abort "bit block inconsistent with verified reference")
      σ σ' vD I I'
      (fun j _ => by rw [hσ _ (hml j 0)]; exact ⟨by simp, coinsOk_bits _⟩)
      (fun j _ => by rw [hσ' _ (hml j 0)]; exact ⟨by simp, coinsOk_bits _⟩)
      (fun J J' hinv => ?_) p.bits (Nat.le_refl _) I I'
      ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
        fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    · rw [Nat.sub_self, ← List.range_eq_range'] at key
      exact key
    · have hbase : f + 2 * p.M ≤ coinBase p f := by
        unfold coinBase maskBase
        omega
      have hsome : ∀ o, o < 2 → ∀ j, j < p.bits → ∀ i, i < W →
          J.fields (coinH p f o j i).id = some ((J.fields (coinH p f o j i).id).getD 0) ∧
          J'.fields (coinH p f o j i).id = some ((J'.fields (coinH p f o j i).id).getD 0) := by
        intro o ho j hj i hi
        by_cases ho' : o = own me
        · subst ho'
          rw [hinv.hon j hj i hi, hinv.hon' j hj i hi]
          exact ⟨rfl, rfl⟩
        · have e : o = 1 - own me := by have := own_lt me; omega
          subst e
          obtain ⟨c, h1, h2⟩ := hinv.adv j hj i hi
          rw [h1, h2]
          exact ⟨rfl, rfl⟩
      have hval : ∀ (st : Store) (rr : Nat → Nat),
          (∀ c, c < p.M → st.elems (s.coins + c) = (word (rr c)).map X25519.bitValue) → ∀ j, j < p.bits →
          ∀ i, i < W → (st.elems (s.coins + member p π₁ π₂ j 0)).getD i 0 =
            X25519.bitValue ((word (rr (refOf p π₁ π₂ j))).getD i false) := by
        intro st rr hst j _ i hi
        rw [hst _ (hml j 0)]
        exact getD_map_lt _ _ _ _ _ (by simpa using hi)
      refine bit_tail_agree E me adv p b f hP π₁ π₂ σ σ' J J' vD
        (fun o j i => (J.fields (coinH p f o j i).id).getD 0) (fun o j i => (J'.fields (coinH p f o j i).id).getD 0)
        x x' bundle bundle' (fun o ho j hj i hi => (hsome o ho j hj i hi).1)
        (fun o ho j hj i hi => (hsome o ho j hj i hi).2)
        (fun o ho j _ => by
          rw [hinv.low _ (by have := fOf_id_lt p f o _ ho (hml j 0); unfold refOf; omega)]
          exact hfld o ho _ (hml j 0))
        (fun o ho j _ => by
          rw [hinv.low' _ (by have := fOf_id_lt p f o _ ho (hml j 0); unfold refOf; omega)]
          exact hfld' o ho _ (hml j 0))
        ?_ (by rw [hinv.bools]; exact hb) (by rw [hinv.bools']; exact hb') hlen hlen' hbits
      refine bitZ_same t π₁ π₂ _ _ (fun j _ => hml j 0) (fun j hj i hi => ?_) (fun j hj i hi => ?_)
        (fun o ho hne j hj i hi => ?_)
      · show (J.fields (coinH p f (own me) j i).id).getD 0 = _
        rw [hinv.hon j hj i hi]
        exact hval σ r hσ j hj i hi
      · show (J'.fields (coinH p f (own me) j i).id).getD 0 = _
        rw [hinv.hon' j hj i hi]
        exact hval σ' r' hσ' j hj i hi
      · have e : o = 1 - own me := by have := own_lt me; omega
        subst e
        obtain ⟨c, h1, h2⟩ := hinv.adv j hj i hi
        show (J'.fields _).getD 0 = (J.fields _).getD 0
        rw [h1, h2]

theorem finish_agree (hW : WordLoaded E) (hP : ProgsLoaded E) (s : Slots) (π₁ π₂ : List Nat) (σ σ' : Store)
    (I I' : Ideal) (vD : List Release) (v v' : Bits) (x x' : Vals) (r r' : Nat → Nat)
    (h : Holds p b f I v x) (h' : Holds p b f I' v' x') (t : Twin p (own me) r r' x x')
    (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M) (hbits : p.bits ≤ p.N)
    (hσ : ∀ c, c < p.M → σ.elems (s.coins + c) = (word (r c)).map X25519.bitValue)
    (hσ' : ∀ c, c < p.M → σ'.elems (s.coins + c) = (word (r' c)).map X25519.bitValue)
    (h32 : ∀ j, j < p.bits → (32 ≤ r' (refOf p π₁ π₂ j) ↔ 32 ≤ r (refOf p π₁ π₂ j))) :
    Agree (fun _ _ _ _ _ => True) (withAdv E me adv (finishPhase p b f s π₁ π₂) σ I vD)
      (withAdv E me adv (finishPhase p b f s π₁ π₂) σ' I' vD) := by
  have hml := member_lt p π₁ π₂ hπ₁ hM
  obtain ⟨I4, f1, f2, f3, f4⟩ := h.final E hW π₁ π₂ hπ₁ hM hbits
  obtain ⟨I4', f1', f2', f3', f4'⟩ := h'.final E hW π₁ π₂ hπ₁ hM hbits
  rw [t.flags_same h.wide h'.wide π₁ π₂ (fun j _ => hml j 0) h32] at f4'
  unfold finishPhase
  refine Agree.locals E me adv _ σ σ' _ (finalBlock_local p b π₁ π₂) I I' I4 I4' vD f1 f1' ?_
  refine Agree.openThen E me adv ⟨b + 11⟩ _ _ σ σ' _ _ _ _ f4 f4' ?_
  split
  · have hl : ∀ y : Vals, y.Wide → (outsOf p π₁ π₂ y).flatten.length = p.N * 256 := by
      intro y hy
      rw [length_flatten_eq 256 _ (outsOf_length_each hy p π₁ π₂)]
      simp [outsOf]
    obtain ⟨I5, m1, m2, -, -, m5, -, -⟩ := masks_block E p b f π₁ π₂ I4 x _ f3 (hl x h.wide) hbits
      (fun o ho c hc => by rw [f2]; exact h.hfld o ho c hc) hπ₁ hM
    obtain ⟨I5', m1', m2', -, -, m5', -, -⟩ := masks_block E p b f π₁ π₂ I4' x' _ f3' (hl x' h'.wide) hbits
      (fun o ho c hc => by rw [f2']; exact h'.hfld o ho c hc) hπ₁ hM
    refine Agree.locals E me adv _ σ σ' _ (maskBlock_local p b f π₁ π₂) _ _ I5 I5' _ m1 m1' ?_
    have hmb : f + 2 * p.M ≤ maskBase p f := by unfold maskBase; omega
    refine Agree.bind E me adv _ _ σ σ' _ _ _
      (bit_agree E me adv p b f hP s π₁ π₂ σ σ' I5 I5' _ x x' r r' _ _ t hπ₁ hM hσ hσ'
        (fun o ho c hc => by
          rw [m5 _ (by have := fOf_id_lt p f o c ho hc; omega), f2]
          exact h.hfld o ho c hc)
        (fun o ho c hc => by
          rw [m5' _ (by have := fOf_id_lt p f o c ho hc; omega), f2']
          exact h'.hfld o ho c hc)
        m2 m2' (hl x h.wide) (hl x' h'.wide) hbits)
      (fun _ _ _ => Agree.done E me adv _ _ _ _ _ _ trivial)
  · exact Agree.abort E me adv _ _ _ _ _ _

/-! ## The whole run -/

/-- The two runs' engine states between the phases: they hold candidate sets that differ only in
the honest owner's (`r`, `r'`). -/
def MidRel (r r' : Nat → Nat) (i i' : Ideal) : Prop :=
  ∃ v v' x x', Holds p b f i v x ∧ Holds p b f i' v' x' ∧ Twin p (own me) r r' x x'

theorem cutChallenge_agree (hh : ∀ m, (E.hash m).length = 32) (s : Slots) (σ σ' : Store) (I : Ideal)
    (vD : List Release) (r r' : Nat → Nat) (hσ : HonestStore p s σ r) (hσ' : HonestStore p s σ' r')
    (hbytes : σ'.bytes = σ.bytes) :
    Agree (fun _ s1 i s1' i' => s1 = σ ∧ s1' = σ' ∧ MidRel me p b f r r' i i')
      (withAdv E me adv (cutChallenge p b f E.hash me s) σ I vD)
      (withAdv E me adv (cutChallenge p b f E.hash me s) σ' I vD) := by
  unfold cutChallenge inputBlock
  simp only [seqs_cons, seqs_nil]
  refine Agree.boolInputBoth E me adv _ _ _ _ _ _ _ σ σ' I I vD hσ.bits_length hσ'.bits_length (fun pb hpb => ?_)
  refine Agree.locals E me adv _ σ σ' [.concat ⟨b + 2⟩ [⟨b⟩, ⟨b + 1⟩]] (by simp [isLocal]) _ _ _ _ vD
    (concat_step E b me I _ pb) (concat_step E b me I _ pb) ?_
  refine Agree.fieldInput E me adv _ _ _ _ _ _ σ σ' _ _ vD (by simp) (by rw [hσ.elems]; simp) rfl
    (by rw [hσ'.elems]; simp) rfl (fun pe hpe _ => ?_)
  have hpe' : pe.length = p.M := by simpa using hpe
  have H := input_holds p b f me s hσ
    ((bothBools me I ⟨b⟩ ⟨b + 1⟩ (σ.bits s.bits) pb).setBool ⟨b + 2⟩ (inBundle me (σ.bits s.bits) pb)) pb pe hpb hpe'
    (by simp [Ideal.setBool])
  have H' := input_holds p b f me s hσ'
    ((bothBools me I ⟨b⟩ ⟨b + 1⟩ (σ'.bits s.bits) pb).setBool ⟨b + 2⟩ (inBundle me (σ'.bits s.bits) pb)) pb pe hpb hpe'
    (by simp [Ideal.setBool])
  refine (agree_challenge E me adv hh σ σ' _ _ vD _ _ _ _ hσ.n1 hσ.v1 (by rw [hbytes]) (by rw [hbytes])).mono
    (fun π s1 i s1' i' hq => ?_)
  obtain ⟨e1, e2, e3, e4⟩ := hq
  subst e1 e2 e3 e4
  refine ⟨rfl, rfl, _, _, _, _, H, H', own_lt me, inVals_honest p me s hσ pb pe hpb,
    inVals_honest p me s hσ' pb pe hpb, fun c _ => by simp [inVals], fun c _ => by simp [inVals],
    fun o ho hne c hc => ?_, hσ.canon, hσ'.canon⟩
  obtain ⟨a1, a2⟩ := inVals_other p me s hσ pb pe hpb o ho hne c hc
  obtain ⟨b1, b2⟩ := inVals_other p me s hσ' pb pe hpb o ho hne c hc
  rw [a1, a2, b1, b2]
  exact ⟨rfl, rfl⟩

theorem bucketChallenge_agree (hh : ∀ m, (E.hash m).length = 32) (s : Slots) (σ σ' : Store) (I : Ideal)
    (vD : List Release) (r r' : Nat → Nat) (hσ : HonestStore p s σ r) (hσ' : HonestStore p s σ' r')
    (hbytes : σ'.bytes = σ.bytes)
    (hcut : ∀ π₁, (withAdv E me adv (cutChallenge p b f E.hash me s) σ I vD).result = some π₁ →
      ∀ c ∈ cutOf p π₁, r' c = r c) :
    Agree (fun _ s1 i s1' i' => s1 = σ ∧ s1' = σ' ∧ MidRel me p b f r r' i i')
      (withAdv E me adv (bucketChallenge p b f E.hash me s) σ I vD)
      (withAdv E me adv (bucketChallenge p b f E.hash me s) σ' I vD) := by
  rw [bucketChallenge_split]
  refine Agree.bind E me adv _ _ σ σ' I I vD (cutChallenge_agree E me adv p b f hh s σ σ' I vD r r' hσ hσ' hbytes)
    (fun π₁ hres hq => ?_)
  obtain ⟨e1, e2, v, v', x, x', H, H', tw⟩ := hq
  have hspec := Leaves.result E me adv _ (cutChallenge_leaves p b f E.hash me s) σ I vD π₁ hres
  have hπ : ∀ c ∈ cutOf p π₁, c < p.M := fun c hc => hspec.2.2 c (List.mem_of_mem_take hc)
  rw [e1, e2]
  refine Agree.bind E me adv _ _ σ σ' _ _ _
    (cut_agree E me adv p b f π₁ σ σ' _ _ _ v v' x x' H H' hπ
      (tw.cut_same _ (fun c hc => ⟨hπ c hc, hcut π₁ hres c hc⟩))) (fun _ _ hq2 => ?_)
  obtain ⟨e3, e4, H2, H2'⟩ := hq2
  rw [e3, e4]
  refine Agree.bind E me adv _ _ σ σ' _ _ _
    (agree_challenge E me adv hh σ σ' _ _ _ _ _ _ _ hσ.n2 hσ.v2 (by rw [hbytes]) (by rw [hbytes]))
    (fun π₂ _ hq3 => ?_)
  obtain ⟨e5, e6, e7, e8⟩ := hq3
  rw [e5, e6, e7, e8]
  exact Agree.done E me adv _ _ _ _ _ _ ⟨rfl, rfl, v, v', x, x', H2, H2', tw⟩

/-- **P-CUT (c), composed with the model.** Two runs of `generate` against the same adversary, from
the same engine state and adversary view, whose honest stores hold the candidates `r` and `r'` and
the same challenge randomness, AGREE (the same views of both parties, trace, replies and result:
`Run.Agree`) when, for the challenges the first run reaches: `r' = r` on the cut; in every bucket
pair the sum of reference and member is the same mod p; and every bit block's reference is at
least 32 in both runs or in neither. -/
theorem generate_agree (hh : ∀ m, (E.hash m).length = 32) (hW : WordLoaded E) (hP : ProgsLoaded E)
    (hM : 0 < p.M) (hbits : p.bits ≤ p.N) (s : Slots) (σ σ' : Store) (I : Ideal) (vD : List Release)
    (r r' : Nat → Nat) (hσ : HonestStore p s σ r) (hσ' : HonestStore p s σ' r') (hbytes : σ'.bytes = σ.bytes)
    (hcut : ∀ π₁, (withAdv E me adv (cutChallenge p b f E.hash me s) σ I vD).result = some π₁ →
      ∀ c ∈ cutOf p π₁, r' c = r c)
    (hbk : ∀ π₁ π₂, (withAdv E me adv (bucketChallenge p b f E.hash me s) σ I vD).result = some (π₁, π₂) →
      (∀ e ∈ pairs p, (r' (member p π₁ π₂ e.2.1 0) + r' (member p π₁ π₂ e.2.1 e.2.2)) % P =
        (r (member p π₁ π₂ e.2.1 0) + r (member p π₁ π₂ e.2.1 e.2.2)) % P) ∧
      (∀ j, j < p.bits → (32 ≤ r' (refOf p π₁ π₂ j) ↔ 32 ≤ r (refOf p π₁ π₂ j)))) :
    Agree (fun _ _ _ _ _ => True) (withAdv E me adv (generate p b f E.hash me s) σ I vD)
      (withAdv E me adv (generate p b f E.hash me s) σ' I vD) := by
  rw [generate_split]
  refine Agree.bind E me adv _ _ σ σ' I I vD
    (bucketChallenge_agree E me adv p b f hh s σ σ' I vD r r' hσ hσ' hbytes hcut) (fun ππ hres hq => ?_)
  obtain ⟨π₁, π₂⟩ := ππ
  obtain ⟨e1, e2, v, v', x, x', H, H', tw⟩ := hq
  obtain ⟨hs1, -⟩ := Leaves.result E me adv _ (bucketChallenge_leaves p b f E.hash me s) σ I vD _ hres
  have hπ₁ : ∀ c ∈ π₁, c < p.M := hs1.2.2
  have hml := member_lt p π₁ π₂ hπ₁ hM
  obtain ⟨hb1, hb2⟩ := hbk π₁ π₂ hres
  rw [e1, e2]
  show Agree _ (withAdv E me adv ((bucketPhase p b f π₁ π₂).bind fun _ => finishPhase p b f s π₁ π₂) _ _ _)
    (withAdv E me adv ((bucketPhase p b f π₁ π₂).bind fun _ => finishPhase p b f s π₁ π₂) _ _ _)
  refine Agree.bind E me adv _ _ σ σ' _ _ _
    (bucket_agree E me adv p b f hW π₁ π₂ σ σ' _ _ _ v v' x x' H H' hπ₁ hM
      (tw.bucket_same _ _ (fun e he => ⟨mem_pairs p e he, hml _ _, hml _ _, hb1 e he⟩))) (fun _ _ hq2 => ?_)
  obtain ⟨e3, e4, H2, H2'⟩ := hq2
  rw [e3, e4]
  exact finish_agree E me adv p b f hW hP s π₁ π₂ σ σ' _ _ _ v v' x x' r r' H2 H2' tw hπ₁ hM hbits hσ.coins
    hσ'.coins hb2

end Phases

end TlsMpc.Node.Flows.Masks
