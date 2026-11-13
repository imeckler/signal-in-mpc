import TlsMpc.Node.Flows.MasksProofs

/-!
# P-CUT at run level: the phases of `Masks.generate` against any adversary

Stage S10. Links the protocol layer (`MasksProofs.lean`) to the ideal model (`Engine/Model.lean`):
in any run of a phase, against any adversary, from any engine state, what the honest party
checks are the values in the engines, and what the adversary sees is exactly the listed releases.
`generate` is the bind of its phases (by definition), so `withAdv_bind` / `viewD_bind` carry these
statements to the corresponding segment of every run of `generate`.

  * `valsOf`: the candidates' values in an ideal state: bits from the concatenated bundle A ‖ B
    (handle b + 2), elements from the candidate field handles. In a run, both come from what the
    two parties input; the adversary's may be anything, independently per engine.
  * `cutPhase_sound` (**P-CUT (d), run level**): if the honest party gets past the cut, every cut
    candidate of BOTH owners is canonical with error 0 (in the engines' values).
    `cutPhase_disclosure` (**P-CUT (b) for the cut**): the adversary's view of the cut phase is a
    prefix of [the cut candidates' elements, the cut candidates' words], labelled `cutCandidates`.
  * `cut_disjoint` (**P-CUT (b), kept values never opened**): the cut and the remaining candidates
    (the references and bucket members) are disjoint, for every permutation the challenge yields.
  * `bucketPhase_sound` (**P-CUT (e), run level**): if the honest party gets past the buckets, every
    (reference, member) pair of both owners passes `bucketOk` in the engines' values (so, by
    `bucketOk_iff`, its errors cancel).
-/

namespace TlsMpc.Node.Flows.Masks

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees Silent blankWire)
open TlsMpc.Node.Flows.Run

theorem flatten_flatMap' {α β : Type} (l : List α) (g : α → List (List β)) :
    (l.flatMap g).flatten = l.flatMap fun a => (g a).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.flatten_append, ih]

theorem flatten_map' {α β : Type} (l : List α) (g : α → List β) : (l.map g).flatten = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]
open TlsMpc.Node.Flows.Conv
open TlsMpc.FieldDag (F modulus)

/-! ## Generic: results through openings -/

section Results

variable (E : Env) (me : Party) (adv : Adversary)

theorem result_openFieldThen {α : Type} (hs : List FieldH) (l : Label) (k : List F → Script α) (σ : Store)
    (I : Ideal) (vD : List Release) (x : α)
    (h : (withAdv E me adv (openFieldThen hs l k) σ I vD).result = some x) :
    ∃ v, hs.mapM (fun h => I.fields h.id) = some v ∧
      (withAdv E me adv (k v) σ I (vD ++ [⟨l, .elems v⟩])).result = some x := by
  simp only [openFieldThen, withAdv, fill, InstrP.map, Wire.early, Option.toList_none, List.append_nil] at h
  revert h
  split
  · simp
  · simp only [idealStep]
    cases hv : hs.mapM (fun h => I.fields h.id) with
    | none => simp
    | some v =>
      simp only [absorb, Option.toList_some]
      intro h
      exact ⟨v, rfl, h⟩

theorem result_openThen {α : Type} (h0 : BoolH) (l : Label) (k : Bits → Script α) (σ : Store)
    (I : Ideal) (vD : List Release) (x : α)
    (h : (withAdv E me adv (openThen h0 l k) σ I vD).result = some x) :
    ∃ v, I.bools h0.id = some v ∧ (withAdv E me adv (k v) σ I (vD ++ [⟨l, .bits v⟩])).result = some x := by
  simp only [openThen, withAdv, fill, InstrP.map, Wire.early, Option.toList_none, List.append_nil] at h
  revert h
  split
  · simp
  · simp only [idealStep]
    cases hv : I.bools h0.id with
    | none => simp
    | some v =>
      simp only [absorb, Option.toList_some]
      intro h
      exact ⟨v, rfl, h⟩

theorem result_ite {α : Type} (c : Bool) (s : Script α) (r : String) (σ : Store) (I : Ideal) (vD : List Release)
    (x : α) (h : (withAdv E me adv (if c then s else .abort r) σ I vD).result = some x) : c = true := by
  cases c
  · simp [withAdv] at h
  · rfl

end Results

/-- `mapM` of lookups that all succeed. -/
theorem mapM_lookups (look : FieldH → Option F) :
    ∀ (l : List FieldH), (∀ h ∈ l, (look h).isSome) → l.mapM look = some (l.map fun h => (look h).getD 0)
  | [], _ => rfl
  | h :: l, hl => by
    have h1 := hl h (by simp)
    have h2 := mapM_lookups look l (fun g hg => hl g (by simp [hg]))
    cases e : look h with
    | none => rw [e] at h1; cases h1
    | some v => simp [List.mapM_cons, e, h2]

/-! ## The candidates' values in an ideal state -/

/-- The candidates in the engines: bits from the concatenated bundle `v` (A ‖ B, handle b + 2),
elements from the candidate field handles. -/
def valsOf (p : Params) (f : Nat) (v : Bits) (I : Ideal) : Vals where
  bits o c := (wordAt p o c).map (v.getD · false)
  elem o c := (I.fields (fOf p f o c).id).getD 0

theorem valsOf_wide (p : Params) (f : Nat) (v : Bits) (I : Ideal) : (valsOf p f v I).Wide := by
  intro o c
  simp [valsOf, wordAt]

/-! ## (b) The cut and the kept candidates are disjoint -/

/-- **P-CUT (b): the kept references and the bucket members are never opened by the cut.** For a
permutation (no repeats), the cut (its first K entries) and the remaining candidates (every
reference and member, `member`) are disjoint. -/
theorem cut_disjoint (p : Params) (π₁ : List Nat) (hn : π₁.Nodup) :
    ∀ c ∈ cutOf p π₁, c ∉ remainOf p π₁ := by
  intro c hc hr
  have h := hn
  rw [← List.take_append_drop p.K π₁, List.nodup_append] at h
  exact h.2.2 c hc c hr rfl

/-! ## The cut phase -/

section Cut

variable (E : Env) (me : Party) (adv : Adversary) (p : Params) (b f : Nat) (π₁ : List Nat)

theorem pick_cut (v : Bits) :
    (cutBits p π₁).map (v.getD · false) = ((cutRel (valsOf p f v ({} : Ideal)) (cutOf p π₁)).map Prod.fst).flatten := by
  simp only [cutBits, cutRel, valsOf, List.map_flatMap, List.map_map, Function.comp_def, flatten_flatMap',
    flatten_map']

theorem cutFields_values (I : Ideal) (v : Bits)
    (hf : ∀ o ∈ owners, ∀ c ∈ cutOf p π₁, (I.fields (fOf p f o c).id).isSome) :
    (cutFields p f π₁).mapM (fun h => I.fields h.id) = some ((cutRel (valsOf p f v I) (cutOf p π₁)).map Prod.snd) := by
  rw [mapM_lookups _ _ (fun h hh => ?_)]
  · simp [cutFields, cutRel, valsOf, List.map_flatMap, Function.comp_def]
  · simp only [cutFields, List.mem_flatMap, List.mem_map] at hh
    obtain ⟨o, ho, c, hc, rfl⟩ := hh
    exact hf o ho c hc

/-- The bits the cut opens do not depend on the field state (`valsOf`'s bits read only `v`). -/
theorem valsOf_bits (v : Bits) (I I' : Ideal) (o c : Nat) : (valsOf p f v I).bits o c = (valsOf p f v I').bits o c := rfl

theorem cutRel_fst (v : Bits) (I I' : Ideal) (cut : List Nat) :
    (cutRel (valsOf p f v I) cut).map Prod.fst = (cutRel (valsOf p f v I') cut).map Prod.fst := by
  simp [cutRel, valsOf, List.map_flatMap, Function.comp_def]

/-- **P-CUT (d), run level.** Against any adversary and from any engine state in which handle
b + 2 holds the candidates' bits `v` (both owners, 2·M·255 bits) and the cut's field handles hold
values: if the honest party gets past the cut phase, every cut candidate of BOTH owners is
canonical and has error 0, in the values the engines hold. -/
theorem cutPhase_sound (σ : Store) (I : Ideal) (vD : List Release) (v : Bits)
    (hv : I.bools (b + 2) = some v) (hlen : v.length = 2 * (p.M * W)) (hπ : ∀ c ∈ cutOf p π₁, c < p.M)
    (hf : ∀ o ∈ owners, ∀ c ∈ cutOf p π₁, (I.fields (fOf p f o c).id).isSome)
    (h : (withAdv E me adv (cutPhase p b f π₁) σ I vD).result = some ()) :
    ∀ o ∈ owners, ∀ c ∈ cutOf p π₁, (valsOf p f v I).val o c < P ∧ (valsOf p f v I).err o c = 0 := by
  have hidx : (cutBits p π₁).all (· < v.length) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq, cutBits, List.mem_flatMap, wordAt, List.mem_map,
      List.mem_range, bitAt, owners, List.mem_cons, List.not_mem_nil, or_false]
    rintro x ⟨o, ho, c, hc, i, hi, rfl⟩
    have := hπ c hc
    rw [hlen]
    have hW : (c + 1) * W ≤ p.M * W := Nat.mul_le_mul_right _ this
    rcases ho with rfl | rfl <;> simp only [Nat.succ_mul] at hW <;> omega
  obtain ⟨I1, h1, h2⟩ := result_locals E me adv _ σ [.pick ⟨b + 3⟩ ⟨b + 2⟩ (cutBits p π₁)] (by simp [isLocal]) I vD () h
  have hI1 : I1 = I.setBool ⟨b + 3⟩ ((cutBits p π₁).map (v.getD · false)) := by
    simp [runLocal, localStep, idealStep, blankWire, InstrP.map, hv, hidx] at h1
    exact h1.symm
  subst hI1
  obtain ⟨ve, hve, h3⟩ := result_openFieldThen E me adv _ _ _ σ _ vD () h2
  have hve' : ve = (cutRel (valsOf p f v I) (cutOf p π₁)).map Prod.snd := by
    have := cutFields_values p f π₁ I v hf
    simp only [Ideal.setBool] at hve
    rw [this] at hve
    exact (Option.some.inj hve).symm
  obtain ⟨vb, hvb, h4⟩ := result_openThen E me adv _ _ _ σ _ _ () h3
  have hvb' : vb = ((cutRel (valsOf p f v I) (cutOf p π₁)).map Prod.fst).flatten := by
    simp only [Ideal.setBool, if_true, Option.some.injEq] at hvb
    rw [← hvb, pick_cut p f π₁ v, cutRel_fst p f v _ I]
  have hc := result_ite E me adv _ _ _ σ _ _ () h4
  rw [hvb', hve'] at hc
  exact (cutCheck_iff _ (valsOf_wide p f v I) _).mp hc

/-- **P-CUT (b) for the cut phase (T3).** The adversary's view of the cut phase is a prefix of
[the cut candidates' field values, the cut candidates' Boolean words], both labelled
`cutCandidates`: nothing of any other candidate. -/
theorem cutPhase_disclosure (σ : Store) (I : Ideal) (vD : List Release) (v : Bits)
    (hv : I.bools (b + 2) = some v) (hlen : v.length = 2 * (p.M * W)) (hπ : ∀ c ∈ cutOf p π₁, c < p.M)
    (hf : ∀ o ∈ owners, ∀ c ∈ cutOf p π₁, (I.fields (fOf p f o c).id).isSome) :
    (withAdv E me adv (cutPhase p b f π₁) σ I vD).viewD <+:
      [⟨Label.cutCandidates, .elems ((cutRel (valsOf p f v I) (cutOf p π₁)).map Prod.snd)⟩,
       ⟨Label.cutCandidates, .bits ((cutRel (valsOf p f v I) (cutOf p π₁)).map Prod.fst).flatten⟩] := by
  have hidx : (cutBits p π₁).all (· < v.length) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq, cutBits, List.mem_flatMap, wordAt, List.mem_map,
      List.mem_range, bitAt, owners, List.mem_cons, List.not_mem_nil, or_false]
    rintro x ⟨o, ho, c, hc, i, hi, rfl⟩
    have := hπ c hc
    rw [hlen]
    have hW : (c + 1) * W ≤ p.M * W := Nat.mul_le_mul_right _ this
    rcases ho with rfl | rfl <;> simp only [Nat.succ_mul] at hW <;> omega
  unfold cutPhase
  refine viewD_locals E me adv _ σ _ [.pick ⟨b + 3⟩ ⟨b + 2⟩ (cutBits p π₁)] (by simp [isLocal]) I vD
    (fun I1 h1 => ?_)
  have hI1 : I1 = I.setBool ⟨b + 3⟩ ((cutBits p π₁).map (v.getD · false)) := by
    simp [runLocal, localStep, idealStep, blankWire, InstrP.map, hv, hidx] at h1
    exact h1.symm
  subst hI1
  refine viewD_openFieldThen E me adv _ _ _ σ _ vD _ _ ?_ ?_
  · have := cutFields_values p f π₁ I v hf
    simp only [Ideal.setBool]
    exact this
  · refine TlsMpc.Node.Flows.Contacts.viewD_openThen E me adv _ _ _ σ _ _ _ _ ?_ ?_
    · simp only [Ideal.setBool, if_true]
      rw [pick_cut p f π₁ v, cutRel_fst p f v _ I]
    · split
      · exact TlsMpc.Node.Flows.Contacts.silent_prefix E me adv _
          (Silent.seqs (Silent.done _) _ (by simp [InstrP.label?])) _ _ _ _
      · exact TlsMpc.Node.Flows.Contacts.silent_prefix E me adv _ (Silent.abort _) _ _ _ _

end Cut

/-! ## The buckets -/

/-- The chunks of a flattened list of equal-width parts are the parts. -/
theorem chunks_range (w : Nat) : ∀ (L : List Bits), (∀ x ∈ L, x.length = w) →
    (List.range L.length).map (fun j => (L.flatten.drop (j * w)).take w) = L
  | [], _ => rfl
  | x :: L, h => by
    have hx := h x (by simp)
    have ih := chunks_range w L (fun y hy => h y (by simp [hy]))
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons, List.take_left' hx, Function.comp_def]
    congr 1
    conv => rhs; rw [← ih]
    apply List.map_congr_left
    intro j _
    rw [show (j + 1) * w = x.length + j * w by rw [hx, Nat.add_mul, Nat.one_mul, Nat.add_comm], List.drop_append,
      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

theorem sum_replicate' (n k : Nat) : (List.replicate n k).sum = n * k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

theorem zipIdx_map_fst {α : Type} (l : List α) : l.zipIdx.map Prod.fst = l := by
  rw [List.zipIdx_eq_zip_range', List.map_fst_zip]
  simp

theorem mem_zipIdx_fst {α : Type} {l : List α} {e : α × Nat} (h : e ∈ l.zipIdx) : e.1 ∈ l := by
  have := List.mem_map_of_mem (f := Prod.fst) h
  rwa [zipIdx_map_fst] at this

/-- `copies` side by side on a flattened list of inputs: the outputs, flattened. -/
theorem runCopies_flatten (c : Circuit) (L : List Bits) (hl : ∀ x ∈ L, x.length = c.inWidth) :
    runCopies c L.length L.flatten = (L.map c.eval).flatten := by
  unfold runCopies
  have := chunks_range c.inWidth L hl
  conv => rhs; rw [← this]
  simp only [List.map_map, Function.comp_def]

theorem modaddEval_pair (a b : Bits) (ha : a.length = W) (hb : b.length = W) :
    modaddEval (a ++ b) = word (addModSpec (natOf a) (natOf b)) := by
  have hx : wordX (a ++ b) = natOf a := by simp [wordX, List.take_left' ha]
  have hy : wordY (a ++ b) = natOf b := by simp [wordY, List.drop_left' ha, List.take_of_length_le (Nat.le_of_eq hb)]
  simp only [modaddEval, hx, hy]

theorem localStep_add (E : Env) (out a b : FieldH) (I : Ideal) :
    localStep E (.fieldAdd out a b) I =
      match I.fields a.id, I.fields b.id with
      | some x, some y => some (I.setField out (x + y))
      | _, _ => none := by
  simp only [localStep, idealStep, blankWire, InstrP.map]
  cases I.fields a.id <;> cases I.fields b.id <;> rfl

/-- **A block of field additions**, with distinct outputs that are none of the operands, and every
operand defined: each output holds the sum of its operands' values (read before the block), and
nothing else changes. -/
theorem runLocal_adds (E : Env) : ∀ (ts : List (FieldH × FieldH × FieldH)) (I : Ideal),
    (ts.map (·.1.id)).Nodup → (∀ t ∈ ts, ∀ t' ∈ ts, t.1.id ≠ t'.2.1.id ∧ t.1.id ≠ t'.2.2.id) →
    (∀ t ∈ ts, (I.fields t.2.1.id).isSome ∧ (I.fields t.2.2.id).isSome) →
    ∃ I', runLocal E (ts.map fun t => .fieldAdd t.1 t.2.1 t.2.2) I = some I' ∧ I'.bools = I.bools ∧
      (∀ t ∈ ts, I'.fields t.1.id = some ((I.fields t.2.1.id).getD 0 + (I.fields t.2.2.id).getD 0)) ∧
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
    have hfr : ∀ t ∈ ts, out.id ≠ t.2.1.id ∧ out.id ≠ t.2.2.id := fun t ht => hd (out, a, b) (by simp) t (by simp [ht])
    have hs' : ∀ t ∈ ts, ((I.setField out (x + y)).fields t.2.1.id).isSome ∧
        ((I.setField out (x + y)).fields t.2.2.id).isSome := by
      intro t ht
      have h1 := hfr t ht
      have h2 := hs t (by simp [ht])
      simp only [Ideal.setField]
      rw [if_neg (Ne.symm h1.1), if_neg (Ne.symm h1.2)]
      exact h2
    obtain ⟨I', h1, h2, h3, h4⟩ := runLocal_adds E ts (I.setField out (x + y)) hn.2 hd' hs'
    refine ⟨I', ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, runLocal, localStep_add, hx, hy]
      exact h1
    · rw [h2]; rfl
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

theorem length_pairs (p : Params) : (pairs p).length = p.D := by
  have h : ∀ (n k : Nat), ((List.range n).flatMap fun j => (List.range k).map fun i => (j, i)).length = n * k := by
    intro n k
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ, List.flatMap_append, ih, Nat.succ_mul]
  simp only [pairs, owners, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
  have e : ∀ o : Nat, ((List.range p.N).flatMap fun j => (List.range (p.B - 1)).map fun k => (o, j, k + 1)).length =
      p.N * (p.B - 1) := by
    intro o
    induction p.N with
    | zero => simp
    | succ n ih => simp [List.range_succ, List.flatMap_append, ih, Nat.succ_mul]
  rw [e, e, Params.D]
  omega

/-- The member indices in the engines' terms. -/
def memOf (p : Params) (π₁ π₂ : List Nat) (j k : Nat) : Nat := member p π₁ π₂ j k

/-- The bucket pairs' 510-bit inputs: the reference's word, then the member's. -/
theorem pick_bucket (p : Params) (f : Nat) (π₁ π₂ : List Nat) (v : Bits) :
    (bucketBits p π₁ π₂).map (v.getD · false) =
      ((pairs p).map fun e => (valsOf p f v ({} : Ideal)).bits e.1 (memOf p π₁ π₂ e.2.1 0) ++
        (valsOf p f v ({} : Ideal)).bits e.1 (memOf p π₁ π₂ e.2.1 e.2.2)).flatten := by
  simp only [bucketBits, valsOf, memOf, List.map_flatMap, List.map_append, flatten_map']

/-- The sum instructions as triples (output, reference, member). -/
def sumTriples (p : Params) (f : Nat) (π₁ π₂ : List Nat) : List (FieldH × FieldH × FieldH) :=
  ((pairs p).zipIdx).map fun (e : (Nat × Nat × Nat) × Nat) =>
    ((sumH p f e.2, fOf p f e.1.1 (member p π₁ π₂ e.1.2.1 0), fOf p f e.1.1 (member p π₁ π₂ e.1.2.1 e.1.2.2)) :
      FieldH × FieldH × FieldH)

theorem sumAdds_eq (p : Params) (f : Nat) (π₁ π₂ : List Nat) :
    sumAdds p f π₁ π₂ = (sumTriples p f π₁ π₂).map fun t => (.fieldAdd t.1 t.2.1 t.2.2 : Instr) := by
  simp [sumAdds, sumTriples, List.map_map, Function.comp_def]

section Bucket

variable (E : Env) (me : Party) (adv : Adversary) (p : Params) (b f : Nat) (π₁ π₂ : List Nat)

theorem mem_pairs (p : Params) (e : Nat × Nat × Nat) (he : e ∈ pairs p) : e.1 < 2 := by
  simp only [pairs, owners, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
  obtain ⟨o, ho, j, -, k, -, rfl⟩ := he
  rcases ho with rfl | rfl
  · show 0 < 2; omega
  · show 1 < 2; omega

theorem member_lt (hπ₁ : ∀ x ∈ π₁, x < p.M) (hM : 0 < p.M) (j k : Nat) : member p π₁ π₂ j k < p.M := by
  unfold member
  rw [List.getD_eq_getElem?_getD]
  cases h : (remainOf p π₁)[π₂.getD (p.B * j + k) 0]? with
  | none => exact hM
  | some x =>
    have := List.mem_of_getElem? h
    exact hπ₁ x (List.mem_of_mem_drop this)

theorem fOf_lt (o c : Nat) (ho : o < 2) (hc : c < p.M) : (fOf p f o c).id < f + 2 * p.M := by
  simp only [fOf]
  rcases o with _ | _ | o
  · omega
  · omega
  · omega

/-- **P-CUT (e), run level.** Against any adversary and from any engine state in which handle
b + 2 holds the candidates' bits `v` and every candidate field handle holds a value (and with the
challenges' permutations of the right range): if the honest party gets past the bucket phase,
every (reference, member) pair of both owners passes `bucketOk` in the engines' values, so
(`bucketOk_iff`) for a canonical reference `val(ref) + val(member) < 2p` and the errors cancel
mod p. -/
theorem bucketPhase_sound (hW : WordLoaded E) (σ : Store) (I : Ideal) (vD : List Release) (v : Bits)
    (hv : I.bools (b + 2) = some v) (hlen : v.length = 2 * (p.M * W))
    (hπ₁ : ∀ x ∈ π₁, x < p.M) (hM : 0 < p.M)
    (hf : ∀ o < 2, ∀ c < p.M, (I.fields (fOf p f o c).id).isSome)
    (h : (withAdv E me adv (bucketPhase p b f π₁ π₂) σ I vD).result = some ()) :
    ∀ e ∈ pairs p, bucketOk ((valsOf p f v I).val e.1 (memOf p π₁ π₂ e.2.1 0))
      ((valsOf p f v I).val e.1 (memOf p π₁ π₂ e.2.1 e.2.2))
      ((valsOf p f v I).elem e.1 (memOf p π₁ π₂ e.2.1 0))
      ((valsOf p f v I).elem e.1 (memOf p π₁ π₂ e.2.1 e.2.2)) = true := by
  have hml := member_lt p π₁ π₂ hπ₁ hM
  -- the pick
  have hidx : (bucketBits p π₁ π₂).all (· < v.length) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq, bucketBits, List.mem_flatMap, List.mem_append, wordAt,
      List.mem_map, List.mem_range, bitAt]
    rintro x ⟨e, he, ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩⟩
    all_goals
      have ho := mem_pairs p e he
      rw [hlen]
    · have := hml e.2.1 0
      have hW' : (member p π₁ π₂ e.2.1 0 + 1) * W ≤ p.M * W := Nat.mul_le_mul_right _ this
      have h1 : e.1 * (p.M * W) ≤ 1 * (p.M * W) := Nat.mul_le_mul_right _ (by omega)
      simp only [Nat.succ_mul] at hW'
      omega
    · have := hml e.2.1 e.2.2
      have hW' : (member p π₁ π₂ e.2.1 e.2.2 + 1) * W ≤ p.M * W := Nat.mul_le_mul_right _ this
      have h1 : e.1 * (p.M * W) ≤ 1 * (p.M * W) := Nat.mul_le_mul_right _ (by omega)
      simp only [Nat.succ_mul] at hW'
      omega
  have hwide : ∀ x ∈ (pairs p).map (fun e => (valsOf p f v ({} : Ideal)).bits e.1 (memOf p π₁ π₂ e.2.1 0) ++
        (valsOf p f v ({} : Ideal)).bits e.1 (memOf p π₁ π₂ e.2.1 e.2.2)), x.length = 510 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, -, rfl⟩ := hx
    simp [valsOf, wordAt, W]
  -- the block
  unfold bucketPhase at h
  rw [bucketBlock, sumAdds_eq] at h
  have hloc : ∀ i ∈ [(.pick ⟨b + 4⟩ ⟨b + 2⟩ (bucketBits p π₁ π₂) : Instr), .run ⟨b + 5⟩ modaddOpenName p.D ⟨b + 4⟩] ++
      (sumTriples p f π₁ π₂).map (fun t => (.fieldAdd t.1 t.2.1 t.2.2 : Instr)), isLocal i = true := by
    intro i hi
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hi
    rcases hi with rfl | rfl | ⟨t, -, rfl⟩ <;> rfl
  obtain ⟨I3, h1, h2⟩ := result_locals E me adv _ σ _ hloc I vD () h
  rw [runLocal_append] at h1
  have hpl : ((bucketBits p π₁ π₂).map (v.getD · false)).length = p.D * 510 := by
    rw [pick_bucket p f π₁ π₂ v, List.length_flatten]
    rw [List.map_map]
    have : ((pairs p).map ((List.length) ∘ fun e => (valsOf p f v ({} : Ideal)).bits e.1
        (memOf p π₁ π₂ e.2.1 0) ++ (valsOf p f v ({} : Ideal)).bits e.1 (memOf p π₁ π₂ e.2.1 e.2.2))) =
        List.replicate (pairs p).length 510 := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp [valsOf, wordAt, W]
    rw [this, sum_replicate', length_pairs]
  have hrun : runLocal E [(.pick ⟨b + 4⟩ ⟨b + 2⟩ (bucketBits p π₁ π₂) : Instr), .run ⟨b + 5⟩ modaddOpenName p.D ⟨b + 4⟩] I =
      some ((I.setBool ⟨b + 4⟩ ((bucketBits p π₁ π₂).map (v.getD · false))).setBool ⟨b + 5⟩
        (runCopies modaddOpenC p.D ((bucketBits p π₁ π₂).map (v.getD · false)))) := by
    have hpl' : (bucketBits p π₁ π₂).length = p.D * 510 := by simpa using hpl
    simp [runLocal, localStep, idealStep, blankWire, InstrP.map, hv, hidx, hW.modaddOpen, Ideal.setBool,
      hpl', modaddOpenC]
  rw [hrun] at h1
  simp only [Option.bind_some] at h1
  -- the sums
  generalize hI2 : (I.setBool ⟨b + 4⟩ ((bucketBits p π₁ π₂).map (v.getD · false))).setBool ⟨b + 5⟩
        (runCopies modaddOpenC p.D ((bucketBits p π₁ π₂).map (v.getD · false))) = I2 at h1
  have hfI2 : I2.fields = I.fields := by rw [← hI2]; rfl
  have hn : ((sumTriples p f π₁ π₂).map (·.1.id)).Nodup := by
    simp only [sumTriples, List.map_map, Function.comp_def, sumH]
    have : ((pairs p).zipIdx.map fun e => f + 2 * p.M + e.2) = (List.range' (f + 2 * p.M) (pairs p).length) := by
      rw [List.zipIdx_eq_zip_range']
      apply List.ext_getElem <;> simp
    rw [this]
    exact List.nodup_range'
  have hd : ∀ t ∈ sumTriples p f π₁ π₂, ∀ t' ∈ sumTriples p f π₁ π₂, t.1.id ≠ t'.2.1.id ∧ t.1.id ≠ t'.2.2.id := by
    intro t ht t' ht'
    simp only [sumTriples, List.mem_map] at ht ht'
    obtain ⟨e, -, rfl⟩ := ht
    obtain ⟨e', he', rfl⟩ := ht'
    have ho := mem_pairs p e'.1 (mem_zipIdx_fst he')
    have h1 := fOf_lt p f _ _ ho (hml e'.1.2.1 0)
    have h2 := fOf_lt p f _ _ ho (hml e'.1.2.1 e'.1.2.2)
    simp only [sumH]
    omega
  have hs : ∀ t ∈ sumTriples p f π₁ π₂, (I2.fields t.2.1.id).isSome ∧ (I2.fields t.2.2.id).isSome := by
    intro t ht
    simp only [sumTriples, List.mem_map] at ht
    obtain ⟨e, he, rfl⟩ := ht
    have ho := mem_pairs p e.1 (mem_zipIdx_fst he)
    rw [hfI2]
    exact ⟨hf _ ho _ (hml _ _), hf _ ho _ (hml _ _)⟩
  obtain ⟨I3', g1, g2, g3, -⟩ := runLocal_adds E (sumTriples p f π₁ π₂) I2 hn hd hs
  rw [g1, Option.some.injEq] at h1
  subst h1
  -- the openings
  obtain ⟨ve, hve, h3⟩ := result_openFieldThen E me adv _ _ _ σ _ vD () h2
  obtain ⟨vb, hvb, h4⟩ := result_openThen E me adv _ _ _ σ _ _ () h3
  have hc := result_ite E me adv _ _ _ σ _ _ () h4
  have hvb' : vb = ((bucketRel (valsOf p f v I) (memOf p π₁ π₂) (pairs p)).map Prod.fst).flatten := by
    rw [g2, ← hI2] at hvb
    simp only [Ideal.setBool, if_true, Option.some.injEq] at hvb
    rw [← hvb, pick_bucket p f π₁ π₂ v]
    have hlenL := length_pairs p
    rw [← hlenL]
    have e1 := runCopies_flatten modaddOpenC _ hwide
    rw [List.length_map] at e1
    rw [e1]
    simp only [bucketRel, List.map_map, Function.comp_def, modaddOpenC]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro e _
    rw [modaddEval_pair _ _ (by simp [valsOf, wordAt, W]) (by simp [valsOf, wordAt, W])]
    simp only [Vals.val, valsOf]
  have hve' : ve = (bucketRel (valsOf p f v I) (memOf p π₁ π₂) (pairs p)).map Prod.snd := by
    let G : Nat × Nat × Nat → F := fun e =>
      (valsOf p f v I).elem e.1 (memOf p π₁ π₂ e.2.1 0) + (valsOf p f v I).elem e.1 (memOf p π₁ π₂ e.2.1 e.2.2)
    have hm : (sums p f).mapM (fun h => I3'.fields h.id) =
        some ((bucketRel (valsOf p f v I) (memOf p π₁ π₂) (pairs p)).map Prod.snd) := by
      rw [mapM_lookups _ _ (fun h hh => ?_)]
      · congr 1
        have step : (sums p f).map (fun h => (I3'.fields h.id).getD 0) = (pairs p).zipIdx.map (G ∘ Prod.fst) := by
          simp only [sums, List.map_map]
          apply List.map_congr_left
          intro e he
          have := g3 (sumH p f e.2, fOf p f e.1.1 (member p π₁ π₂ e.1.2.1 0),
            fOf p f e.1.1 (member p π₁ π₂ e.1.2.1 e.1.2.2)) (by simp only [sumTriples, List.mem_map]; exact ⟨e, he, rfl⟩)
          simp only [Function.comp_apply]
          rw [this, hfI2]
          rfl
        rw [step, ← List.map_map, zipIdx_map_fst]
        simp only [bucketRel, List.map_map]
        rfl
      · simp only [sums, List.mem_map] at hh
        obtain ⟨e, he, rfl⟩ := hh
        have := g3 (sumH p f e.2, fOf p f e.1.1 (member p π₁ π₂ e.1.2.1 0),
            fOf p f e.1.1 (member p π₁ π₂ e.1.2.1 e.1.2.2)) (by simp only [sumTriples, List.mem_map]; exact ⟨e, he, rfl⟩)
        rw [this]
        rfl
    rw [hm] at hve
    exact (Option.some.inj hve).symm
  rw [hvb', hve'] at hc
  exact (bucketCheck_iff _ _ _).mp hc

end Bucket

end TlsMpc.Node.Flows.Masks
