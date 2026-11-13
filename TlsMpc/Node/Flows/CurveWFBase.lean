import TlsMpc.Node.Flows.Curve
import TlsMpc.Node.Flows.ConvertWF

/-!
# Well-formedness of the curve scripts: the shell's context as a function of handle ids

Stage S11 (PROOF_GAPS F23). The curve scripts work on large consecutive blocks of field handles
(thousands per program instruction), so their `_wf` theorems (`Flows/CurveWF.lean`) do not track
the shell's context `Ctx` literally. They track it through `St c g n P`:

  * `g : Nat → Option Mark` gives the mark of every field id (`none`: not live);
  * no field id from `n` on was ever defined (the session counter is ahead: `Counters.Ahead`);
  * the loaded programs are `P`.

Every block the scripts use moves `St` in a closed form: inputs and shared blocks (`upd`, mark
never), publics (`upd`, mark pub), a program instruction (its masks consumed: `gone`; its outputs
marked as the program declares: `updL`), frees of a block (`gone`) or of a strided family of
blocks (`goneS`), openings (no change; the opened marks must be `pub` or `revealable`).

The programs' signatures (`CurveProgs`) are the V3 shapes of the compiled programs: data inputs,
masks, and which outputs are public (read off `FieldProgramsV3.find` with
`scratch`-only tooling; the same counts as `CurveBase.shapeOf`, and the shell refuses any other
count, so a wrong entry here only makes a hypothesis false, never a script admitted wrongly).
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs checkAll WFP_seq)
open TlsMpc.Node.Flows.Run (openFieldThen)
open TlsMpc.FieldDag (F ofNat)

namespace WFB

/-! ## The state -/

/-- The context `c` has the field marks `g` (by id), no field id from `n` on was ever defined, and
the programs `P` are loaded. -/
structure St (c : Ctx) (g : Nat → Option Mark) (n : Nat) (P : Bytes → Option ProgSig) : Prop where
  marks : ∀ x : FieldH, c.field? x = g x.id
  fresh : ∀ j, n ≤ j → j ∉ c.seenF
  progs : c.progs = P

theorem St.mono {c : Ctx} {g : Nat → Option Mark} {n : Nat} {P : Bytes → Option ProgSig} (h : St c g n P)
    {n' : Nat} (hn : n ≤ n') : St c g n' P :=
  ⟨h.marks, fun j hj => h.fresh j (by omega), h.progs⟩

theorem St.congr {c : Ctx} {g : Nat → Option Mark} {n : Nat} {P : Bytes → Option ProgSig} (h : St c g n P)
    {g' : Nat → Option Mark} (e : ∀ j, g j = g' j) : St c g' n P :=
  ⟨fun x => (h.marks x).trans (e x.id), h.fresh, h.progs⟩

/-- Any context, from the counter on. -/
theorem St.init (c : Ctx) (n : Nat) (h : ∀ j, n ≤ j → j ∉ c.seenF) : St c (fun j => c.field? ⟨j⟩) n c.progs :=
  ⟨fun _ => rfl, h, rfl⟩

/-- What a script leaves: some marks `g'` from the counter `hi` on, and every id below `lo`
unchanged. -/
def Post (g : Nat → Option Mark) (lo hi : Nat) (P : Bytes → Option ProgSig) (c : Ctx) : Prop :=
  ∃ g', St c g' hi P ∧ ∀ j, j < lo → g' j = g j

/-! ## Mark updates -/

def upd (g : Nat → Option Mark) (f k : Nat) (m : Mark) : Nat → Option Mark :=
  fun j => if f ≤ j ∧ j < f + k then some m else g j

def updL (g : Nat → Option Mark) (f k : Nat) (ms : List Mark) : Nat → Option Mark :=
  fun j => if f ≤ j ∧ j < f + k then some (ms.getD (j - f) .never) else g j

def gone (g : Nat → Option Mark) (a k : Nat) : Nat → Option Mark :=
  fun j => if a ≤ j ∧ j < a + k then none else g j

open Classical in
/-- The blocks `[o + K·i, o + K·i + w)`, `i < m`, freed. -/
noncomputable def goneS (g : Nat → Option Mark) (o K w m : Nat) : Nat → Option Mark :=
  fun j => if ∃ i, i < m ∧ o + K * i ≤ j ∧ j < o + K * i + w then none else g j

variable {g : Nat → Option Mark} {f k a j : Nat} {m : Mark} {ms : List Mark}

theorem upd_in (h : f ≤ j ∧ j < f + k) : upd g f k m j = some m := if_pos h
theorem upd_out (h : ¬ (f ≤ j ∧ j < f + k)) : upd g f k m j = g j := if_neg h
theorem updL_in (h : f ≤ j ∧ j < f + k) : updL g f k ms j = some (ms.getD (j - f) .never) := if_pos h
theorem updL_out (h : ¬ (f ≤ j ∧ j < f + k)) : updL g f k ms j = g j := if_neg h
theorem gone_in (h : a ≤ j ∧ j < a + k) : gone g a k j = none := if_pos h
theorem gone_out (h : ¬ (a ≤ j ∧ j < a + k)) : gone g a k j = g j := if_neg h

theorem goneS_below {o K w n : Nat} (h : j < o) : goneS g o K w n j = g j := by
  unfold goneS
  rw [if_neg]
  rintro ⟨i, _, h1, _⟩
  omega

theorem goneS_out {o K w n : Nat} (h : ¬ ∃ i, i < n ∧ o + K * i ≤ j ∧ j < o + K * i + w) :
    goneS g o K w n j = g j := by
  unfold goneS
  rw [if_neg h]

/-! ## Handle blocks -/

theorem hs_length (f k : Nat) : (hs f k).length = k := by simp [hs]

theorem hs_zero (f : Nat) : hs f 0 = [] := rfl

theorem hs_succ (f k : Nat) : hs f (k + 1) = ⟨f⟩ :: hs (f + 1) k := by
  unfold hs
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show (⟨f + (i + 1)⟩ : FieldH) = ⟨f + 1 + i⟩
  rw [show f + (i + 1) = f + 1 + i by omega]

theorem hs_append (f a b : Nat) : hs f a ++ hs (f + a) b = hs f (a + b) := by
  induction a generalizing f with
  | zero => simp [hs_zero]
  | succ a ih =>
    rw [hs_succ, List.cons_append, show f + (a + 1) = f + 1 + a by omega, ih, show a + 1 + b = a + b + 1 by omega,
      hs_succ]

theorem mem_hs {x : FieldH} {f k : Nat} : x ∈ hs f k ↔ f ≤ x.id ∧ x.id < f + k := by
  unfold hs
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Nat.le_add_right _ _, by show f + i < f + k; omega⟩
  · intro h
    refine ⟨x.id - f, by omega, ?_⟩
    cases x with
    | mk id =>
      simp only [FieldH.mk.injEq]
      simp only at h
      omega

theorem mem_flatMap_hs {x : FieldH} {o K w n : Nat} :
    x ∈ (List.range n).flatMap (fun i => hs (o + K * i) w) ↔ ∃ i, i < n ∧ o + K * i ≤ x.id ∧ x.id < o + K * i + w := by
  simp only [List.mem_flatMap, List.mem_range, mem_hs]

theorem map_eq_flatMap_hs (o K n : Nat) :
    (List.range n).map (fun i => (⟨o + K * i⟩ : FieldH)) = (List.range n).flatMap (fun i => hs (o + K * i) 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.flatMap_append, ih, hs]

/-! ## `checkAll` -/

theorem checkAll_append (sigs : Bytes → Option Sig) :
    ∀ (c : Ctx) (a b : List Instr), checkAll sigs c (a ++ b) = (checkAll sigs c a).bind fun c' => checkAll sigs c' b
  | c, [], b => rfl
  | c, i :: a, b => by
    cases h : check sigs c i.skel with
    | none => simp [checkAll, h]
    | some p =>
      obtain ⟨c', sh⟩ := p
      cases sh <;> simp [checkAll, h, checkAll_append sigs c' a b]

theorem checkAll_of_check (sigs : Bytes → Option Sig) (c c' : Ctx) (i : Instr) (h : check sigs c i.skel = some (c', .unit)) :
    checkAll sigs c [i] = some c' := by
  simp [checkAll, h]

theorem checkAll_two (sigs : Bytes → Option Sig) (c c1 c2 : Ctx) (a b : List Instr) (h1 : checkAll sigs c a = some c1)
    (h2 : checkAll sigs c1 b = some c2) : checkAll sigs c (a ++ b) = some c2 := by
  rw [checkAll_append, h1]
  exact h2

/-! ## Definitions of fresh handles -/

theorem st_defList (sigs : Bytes → Option Sig) : ∀ (ms : List Mark) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (_ : St c g n P) (f : Nat) (_ : n ≤ f),
    ∃ c', c.defFields (hs f ms.length) ms = some c' ∧ St c' (updL g f ms.length ms) (f + ms.length) P
  | [], c, g, n, P, h, f, hf =>
    ⟨c, rfl, (h.mono (by simp only [List.length_nil]; omega)).congr fun j => by
      unfold updL; rw [if_neg (by simp only [List.length_nil]; omega)]⟩
  | m :: ms, c, g, n, P, h, f, hf => by
    have h0 : f ∉ c.seenF := h.fresh f hf
    have hd : c.defField ⟨f⟩ m = some { c with fields := (f, m) :: c.fields, seenF := f :: c.seenF } := by
      simp [Ctx.defField, h0]
    have h1 : St { c with fields := (f, m) :: c.fields, seenF := f :: c.seenF } (upd g f 1 m) (f + 1) P := by
      refine ⟨fun x => ?_, fun j hj hm => ?_, h.progs⟩
      · rw [Ctx.field?_defField hd, h.marks]
        unfold upd
        by_cases e : x.id = f
        · rw [if_pos (show x.id = (⟨f⟩ : FieldH).id from e), if_pos (by omega)]
        · rw [if_neg (show ¬ x.id = (⟨f⟩ : FieldH).id from e), if_neg (by omega)]
      · simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · omega
        · exact h.fresh j (by omega) hm
    obtain ⟨c2, hd2, h2⟩ := st_defList sigs ms h1 (f + 1) (Nat.le_refl _)
    refine ⟨c2, ?_, (h2.mono (by simp only [List.length_cons]; omega)).congr fun j => ?_⟩
    · rw [List.length_cons, hs_succ]
      simp only [Ctx.defFields, hd, Option.bind_eq_bind, Option.bind_some]
      exact hd2
    · unfold updL upd
      simp only [List.length_cons]
      by_cases e1 : f + 1 ≤ j ∧ j < f + 1 + ms.length
      · rw [if_pos e1, if_pos (by omega), show j - f = (j - (f + 1)) + 1 by omega, List.getD_cons_succ]
      · rw [if_neg e1]
        by_cases e2 : j = f
        · subst e2
          rw [if_pos (by omega), if_pos (by omega), Nat.sub_self]
          rfl
        · rw [if_neg (by omega), if_neg (by omega)]

theorem getD_replicate_mark (k i : Nat) (m : Mark) (hi : i < k) : (List.replicate k m).getD i .never = m := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi]
  rfl

theorem st_defBlk (sigs : Bytes → Option Sig) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (h : St c g n P) (f k : Nat) (m : Mark) (hf : n ≤ f) :
    ∃ c', c.defFields (hs f k) (List.replicate k m) = some c' ∧ St c' (upd g f k m) (f + k) P := by
  obtain ⟨c', hd, h'⟩ := st_defList sigs (List.replicate k m) h f hf
  rw [List.length_replicate] at hd h'
  refine ⟨c', hd, h'.congr fun j => ?_⟩
  unfold updL upd
  by_cases e : f ≤ j ∧ j < f + k
  · rw [if_pos e, if_pos e, getD_replicate_mark k _ m (by omega)]
  · rw [if_neg e, if_neg e]

theorem st_def1 (sigs : Bytes → Option Sig) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (h : St c g n P) (f : Nat) (m : Mark) (hf : n ≤ f) :
    ∃ c', c.defField ⟨f⟩ m = some c' ∧ St c' (upd g f 1 m) (f + 1) P := by
  obtain ⟨c', hd, h'⟩ := st_defBlk sigs h f 1 m hf
  refine ⟨c', ?_, h'⟩
  have e : hs f 1 = [⟨f⟩] := rfl
  rw [e] at hd
  simp only [List.replicate, Ctx.defFields, Option.bind_eq_bind] at hd
  cases h1 : c.defField ⟨f⟩ m with
  | none => rw [h1] at hd; cases hd
  | some c1 => rw [h1] at hd; simp only [Option.bind_some] at hd; rw [← hd]

/-! ## Inputs, shared blocks, publics -/

theorem st_input (sigs : Bytes → Option Sig) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (h : St c g n P) (f k : Nat) (kd : FieldIn) (slot : Nat) (hf : n ≤ f) :
    ∃ c', check sigs c (InstrP.skel (InstrP.fieldInput (hs f k) (hs (f + k) k) kd false slot : Instr)) = some (c', .unit) ∧
      St c' (upd g f (k + k) .never) (f + (k + k)) P := by
  obtain ⟨c', hd, h'⟩ := st_defBlk sigs h f (k + k) .never hf
  refine ⟨c', ?_, h'⟩
  have := Masks.check_fieldInput' sigs c c' (hs f k) (hs (f + k) k) kd false (by rw [hs_length, hs_length])
    (by rw [hs_length, hs_length, hs_append]; exact hd)
  exact this

theorem upd_upd (g : Nat → Option Mark) (o t s : Nat) (m : Mark) (j : Nat) :
    upd (upd g o t m) (o + t) s m j = upd g o (t + s) m j := by
  unfold upd
  by_cases e1 : o + t ≤ j ∧ j < o + t + s
  · rw [if_pos e1, if_pos (by omega)]
  · rw [if_neg e1]
    by_cases e2 : o ≤ j ∧ j < o + t
    · rw [if_pos e2, if_pos (by omega)]
    · rw [if_neg e2, if_neg (by omega)]

theorem st_adds (sigs : Bytes → Option Sig) : ∀ (t : Nat) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (_ : St c g n P) (o a b : Nat),
    (∀ i, i < t → g (a + i) = some .never) → (∀ i, i < t → g (b + i) = some .never) → n ≤ o → a + t ≤ o →
    b + t ≤ o →
    ∃ c', checkAll sigs c ((List.range t).map fun i => (InstrP.fieldAdd ⟨o + i⟩ ⟨a + i⟩ ⟨b + i⟩ : Instr)) = some c' ∧
      St c' (upd g o t .never) (o + t) P
  | 0, c, g, n, P, h, o, a, b, _, _, hn, _, _ =>
    ⟨c, rfl, (h.mono (by omega)).congr fun j => by unfold upd; rw [if_neg (by omega)]⟩
  | t + 1, c, g, n, P, h, o, a, b, ha, hb, hn, hao, hbo => by
    obtain ⟨c1, e1, h1⟩ := st_adds sigs t h o a b (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)) hn
      (by omega) (by omega)
    obtain ⟨c2, hd, h2⟩ := st_def1 sigs h1 (o + t) .never (by omega)
    have ha' : c1.field? ⟨a + t⟩ = some .never := by
      rw [h1.marks]
      show upd g o t .never (a + t) = some .never
      rw [upd_out (by omega)]
      exact ha t (by omega)
    have hb' : c1.field? ⟨b + t⟩ = some .never := by
      rw [h1.marks]
      show upd g o t .never (b + t) = some .never
      rw [upd_out (by omega)]
      exact hb t (by omega)
    have hck : check sigs c1 (InstrP.skel (InstrP.fieldAdd ⟨o + t⟩ ⟨a + t⟩ ⟨b + t⟩ : Instr)) = some (c2, .unit) := by
      simp [check, InstrP.skel, InstrP.map, ha', hb', Mark.join, hd]
    refine ⟨c2, ?_, (h2.mono (by omega)).congr fun j => upd_upd g o t 1 .never j⟩
    rw [List.range_succ, List.map_append, checkAll_append, e1]
    simp [checkAll, hck]

theorem st_shared (sigs : Bytes → Option Sig) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (h : St c g n P) (f k slot : Nat) (hf : n ≤ f) :
    ∃ c', checkAll sigs c (sharedBlock f k slot) = some c' ∧ St c' (upd g f (3 * k) .never) (f + 3 * k) P := by
  obtain ⟨c1, e1, h1⟩ := st_input sigs h f k .elements slot hf
  obtain ⟨c2, e2, h2⟩ := st_adds sigs k h1 (f + 2 * k) f (f + k)
    (fun i hi => upd_in (by omega)) (fun i hi => upd_in (by omega)) (by omega) (by omega) (by omega)
  refine ⟨c2, ?_, (h2.mono (by omega)).congr fun j => ?_⟩
  · unfold sharedBlock
    rw [Masks.checkAll_cons sigs c c1 _ _ e1]
    exact e2
  · rw [show f + 2 * k = f + (k + k) by omega, upd_upd, show k + k + k = 3 * k by omega]

theorem st_publicsFrom (sigs : Bytes → Option Sig) : ∀ (vs : List F) (s : Nat) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (_ : St c g n P) (f : Nat), n ≤ f + s →
    ∃ c', checkAll sigs c ((vs.zipIdx s).map fun e => (InstrP.fieldPublic ⟨f + e.2⟩ e.1 : Instr)) = some c' ∧
      St c' (upd g (f + s) vs.length .pub) (f + s + vs.length) P
  | [], s, c, g, n, P, h, f, hn =>
    ⟨c, rfl, (h.mono (by simp only [List.length_nil]; omega)).congr fun j => by
      unfold upd; rw [if_neg (by simp only [List.length_nil]; omega)]⟩
  | v :: vs, s, c, g, n, P, h, f, hn => by
    obtain ⟨c1, hd, h1⟩ := st_def1 sigs h (f + s) .pub hn
    have hck : check sigs c (InstrP.skel (InstrP.fieldPublic ⟨f + s⟩ v : Instr)) = some (c1, .unit) := by
      simp [check, InstrP.skel, InstrP.map, hd]
    obtain ⟨c2, e2, h2⟩ := st_publicsFrom sigs vs (s + 1) h1 f (by omega)
    refine ⟨c2, ?_, (h2.mono (by simp only [List.length_cons]; omega)).congr fun j => ?_⟩
    · rw [List.zipIdx_cons, List.map_cons, Masks.checkAll_cons sigs c c1 _ _ hck]
      exact e2
    · rw [show f + (s + 1) = f + s + 1 by omega, upd_upd, List.length_cons, Nat.add_comm 1]

theorem st_publics (sigs : Bytes → Option Sig) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (h : St c g n P) (f : Nat) (vs : List F) (hf : n ≤ f) :
    ∃ c', checkAll sigs c (publics f vs) = some c' ∧ St c' (upd g f vs.length .pub) (f + vs.length) P := by
  obtain ⟨c', e, h'⟩ := st_publicsFrom sigs vs 0 h f hf
  exact ⟨c', e, h'⟩

theorem st_public1 (sigs : Bytes → Option Sig) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (h : St c g n P) (f : Nat) (v : F) (hf : n ≤ f) :
    ∃ c', check sigs c (InstrP.skel (InstrP.fieldPublic ⟨f⟩ v : Instr)) = some (c', .unit) ∧
      St c' (upd g f 1 .pub) (f + 1) P := by
  obtain ⟨c1, hd, h1⟩ := st_def1 sigs h f .pub hf
  exact ⟨c1, by simp [check, InstrP.skel, InstrP.map, hd], h1⟩

/-! ## Frees -/

theorem st_drop {c : Ctx} {g : Nat → Option Mark} {n : Nat} {P : Bytes → Option ProgSig} (h : St c g n P) (a : Nat) :
    St (c.dropField a) (gone g a 1) n P := by
  refine ⟨fun x => ?_, h.fresh, h.progs⟩
  rw [Ctx.field?_dropField, h.marks]
  unfold gone
  by_cases e : x.id = a
  · rw [if_pos e, if_pos (by omega)]
  · rw [if_neg e, if_neg (by omega)]

theorem gone_gone (g : Nat → Option Mark) (a k : Nat) (j : Nat) :
    gone (gone g a 1) (a + 1) k j = gone g a (k + 1) j := by
  unfold gone
  by_cases e1 : a + 1 ≤ j ∧ j < a + 1 + k
  · rw [if_pos e1, if_pos (by omega)]
  · rw [if_neg e1]
    by_cases e2 : a ≤ j ∧ j < a + 1
    · rw [if_pos e2, if_pos (by omega)]
    · rw [if_neg e2, if_neg (by omega)]

theorem st_free (sigs : Bytes → Option Sig) : ∀ (k : Nat) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (_ : St c g n P) (a : Nat), (∀ i, i < k → (g (a + i)).isSome = true) →
    ∃ c', checkAll sigs c (freeFs (hs a k)) = some c' ∧ St c' (gone g a k) n P
  | 0, c, g, n, P, h, a, _ => ⟨c, rfl, h.congr fun j => by unfold gone; rw [if_neg (by omega)]⟩
  | k + 1, c, g, n, P, h, a, hl => by
    obtain ⟨mk, hmk⟩ := Option.isSome_iff_exists.mp (hl 0 (by omega))
    have hck : check sigs c (InstrP.skel (InstrP.freeField ⟨a⟩ : Instr)) = some (c.dropField a, .unit) := by
      have : c.field? ⟨a⟩ = some mk := by rw [h.marks]; simpa using hmk
      simp [check, InstrP.skel, InstrP.map, this]
    obtain ⟨c2, e2, h2⟩ := st_free sigs k (st_drop h a) (a + 1) (fun i hi => by
      show (gone g a 1 (a + 1 + i)).isSome = true
      rw [gone_out (by omega), show a + 1 + i = a + (i + 1) by omega]
      exact hl (i + 1) (by omega))
    refine ⟨c2, ?_, h2.congr fun j => gone_gone g a k j⟩
    rw [hs_succ]
    simp only [freeFs, List.map_cons]
    rw [Masks.checkAll_cons sigs c _ _ _ hck]
    exact e2

theorem st_freeS (sigs : Bytes → Option Sig) (o K w : Nat) (hw : w ≤ K) : ∀ (m : Nat) {c : Ctx} {g : Nat → Option Mark}
    {n : Nat} {P : Bytes → Option ProgSig} (_ : St c g n P),
    (∀ i t, i < m → t < w → (g (o + K * i + t)).isSome = true) →
    ∃ c', checkAll sigs c (freeFs ((List.range m).flatMap fun i => hs (o + K * i) w)) = some c' ∧
      St c' (goneS g o K w m) n P
  | 0, c, g, n, P, h, _ => ⟨c, rfl, h.congr fun j => by
      unfold goneS; rw [if_neg]; rintro ⟨i, hi, _⟩; omega⟩
  | m + 1, c, g, n, P, h, hl => by
    obtain ⟨c1, e1, h1⟩ := st_freeS sigs o K w hw m h (fun i t hi ht => hl i t (by omega) ht)
    obtain ⟨c2, e2, h2⟩ := st_free sigs w h1 (o + K * m) (fun t ht => by
      rw [goneS_out]
      · exact hl m t (by omega) ht
      · rintro ⟨i, hi, h1, h2⟩
        have := Nat.mul_le_mul_left K (show i + 1 ≤ m by omega)
        rw [Nat.mul_succ] at this
        omega)
    refine ⟨c2, ?_, h2.congr fun j => ?_⟩
    · rw [List.range_succ, List.flatMap_append]
      simp only [freeFs, List.map_append] at e1 ⊢
      rw [checkAll_append, e1]
      simpa [freeFs] using e2
    · unfold gone goneS
      by_cases e1 : o + K * m ≤ j ∧ j < o + K * m + w
      · rw [if_pos e1, if_pos ⟨m, by omega, e1.1, e1.2⟩]
      · rw [if_neg e1]
        by_cases e2 : ∃ i, i < m ∧ o + K * i ≤ j ∧ j < o + K * i + w
        · obtain ⟨i, hi, h1, h2⟩ := e2
          rw [if_pos ⟨i, hi, h1, h2⟩, if_pos ⟨i, by omega, h1, h2⟩]
        · rw [if_neg e2, if_neg]
          rintro ⟨i, hi, q1, q2⟩
          by_cases him : i = m
          · rw [him] at q1 q2
            exact e1 ⟨q1, q2⟩
          · exact e2 ⟨i, by omega, q1, q2⟩

/-! ## The program instruction -/

theorem st_useMasks : ∀ (k : Nat) {c : Ctx} {g : Nat → Option Mark} {n : Nat} {P : Bytes → Option ProgSig}
    (_ : St c g n P) (a : Nat), (∀ i, i < k → g (a + i) = some .never) →
    ∃ c', c.useMasks (hs a k) = some c' ∧ St c' (gone g a k) n P
  | 0, c, g, n, P, h, a, _ => ⟨c, rfl, h.congr fun j => by unfold gone; rw [if_neg (by omega)]⟩
  | k + 1, c, g, n, P, h, a, hm => by
    have e : c.field? ⟨a⟩ = some .never := by rw [h.marks]; simpa using hm 0 (by omega)
    obtain ⟨c2, e2, h2⟩ := st_useMasks k (st_drop h a) (a + 1) (fun i hi => by
      rw [gone_out (by omega), show a + 1 + i = a + (i + 1) by omega]
      exact hm (i + 1) (by omega))
    refine ⟨c2, ?_, h2.congr fun j => gone_gone g a k j⟩
    rw [hs_succ]
    simp only [Ctx.useMasks, e]
    exact e2

theorem length_flatten_replicate (copies : Nat) (om : List Mark) :
    (List.replicate copies om).flatten.length = copies * om.length := by
  induction copies with
  | zero => simp
  | succ k ih => simp only [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul]; omega

/-- **A program instruction**: masks a block of live `never` handles (consumed), inputs live once
the masks are gone, outputs a fresh block marked as the program declares. -/
theorem st_program (sigs : Bytes → Option Sig) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (h : St c g n P) (name : Bytes) (copies : Nat) (ins : List FieldH)
    (mf mk fo K : Nat) (l : Label) (s : ProgSig) (hl : l.code ≠ 0) (hp : P name = some s) (hc : 0 < copies)
    (hcw : copies ≤ maxWidth) (hi : ins.length = copies * s.inputs) (hm : mk = copies * s.masks)
    (hK : K = copies * s.outMarks.length)
    (hmask : ∀ i, i < mk → g (mf + i) = some .never)
    (hlive : ∀ x ∈ ins, (gone g mf mk x.id).isSome = true) (hf : n ≤ fo) (ms os : List FieldH)
    (hms : ms = hs mf mk) (hos : os = hs fo K) :
    ∃ c', check sigs c (InstrP.skel (InstrP.program name copies ins ms os l : Instr)) = some (c', .unit) ∧
      St c' (updL (gone g mf mk) fo K (List.replicate copies s.outMarks).flatten) (fo + K) P := by
  subst hms hos
  obtain ⟨c1, hu, h1⟩ := st_useMasks mk h mf hmask
  obtain ⟨c2, hd, h2⟩ := st_defList sigs (List.replicate copies s.outMarks).flatten h1 fo hf
  rw [length_flatten_replicate, ← hK] at hd h2
  refine ⟨c2, ?_, h2⟩
  have hlive' : (ins.all fun x => (c1.field? x).isSome) = true :=
    List.all_eq_true.mpr fun x hx => by rw [h1.marks]; exact hlive x hx
  have hlen : (hs mf mk).length = copies * s.masks := by rw [hs_length, hm]
  have hlenK : (hs fo K).length = copies * s.outMarks.length := by rw [hs_length, hK]
  simp only [check, InstrP.skel, InstrP.map, Option.bind_eq_bind, h.progs, hp, Option.bind_some, guard, hc, hcw,
    hi, hlen, hlenK, hu, hlive', hd]
  simp [hl]

/-- The marks of a program's outputs: copy `i`'s output `t`. -/
theorem flat_getD (om : List Mark) (L : Nat) (hL : om.length = L) : ∀ (copies i t : Nat), i < copies → t < L →
    (List.replicate copies om).flatten.getD (L * i + t) .never = om.getD t .never
  | 0, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | copies + 1, i, t, hi, ht => by
    rw [List.replicate_succ, List.flatten_cons, List.getD_eq_getElem?_getD]
    by_cases hi0 : i = 0
    · subst hi0
      rw [Nat.mul_zero, Nat.zero_add, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    · rw [List.getElem?_append_right (by rw [hL]; have := Nat.mul_le_mul_left L (show 1 ≤ i by omega); omega),
        ← List.getD_eq_getElem?_getD, hL,
        show L * i + t - L = L * (i - 1) + t by
          have : L * i = L * (i - 1) + L := by
            rw [← Nat.mul_succ]; congr 1; omega
          omega]
      exact flat_getD om L hL copies (i - 1) t (by omega) ht

/-- A program output's mark through `updL`. -/
theorem updL_flat (g : Nat → Option Mark) (fo copies K : Nat) (om : List Mark) (L : Nat) (hL : om.length = L)
    (hK : K = copies * L) (i t j : Nat) (hi : i < copies) (ht : t < L) (hj : j = fo + L * i + t) :
    updL g fo K (List.replicate copies om).flatten j = some (om.getD t .never) := by
  have hlt : L * i + t < copies * L := by
    have := Nat.mul_le_mul_left L (show i + 1 ≤ copies by omega)
    rw [Nat.mul_succ, Nat.mul_comm L copies] at this
    omega
  rw [updL_in (by rw [hK]; omega), show j - fo = L * i + t by omega, flat_getD om L hL copies i t hi ht]

/-- Any program output is live. -/
theorem updL_isSome (g : Nat → Option Mark) (fo K : Nat) (ms : List Mark) (j : Nat) (h : fo ≤ j ∧ j < fo + K) :
    (updL g fo K ms j).isSome = true := by
  rw [updL_in h]
  rfl

/-- Rewrite every layer of marks whose range decides the id (`omega` on the ranges). -/
macro "wf_marks" : tactic => `(tactic| simp (disch := omega) only [TlsMpc.Node.Flows.Curve.WFB.upd_in,
  TlsMpc.Node.Flows.Curve.WFB.upd_out, TlsMpc.Node.Flows.Curve.WFB.updL_in, TlsMpc.Node.Flows.Curve.WFB.updL_out,
  TlsMpc.Node.Flows.Curve.WFB.gone_in, TlsMpc.Node.Flows.Curve.WFB.gone_out,
  TlsMpc.Node.Flows.Curve.WFB.goneS_below, Option.isSome_some])

/-! ## Openings -/

theorem st_open (sigs : Bytes → Option Sig) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (h : St c g n P) (l : Label) (hl : l.code ≠ 0) (xs : List FieldH)
    (hx : ∀ x ∈ xs, ∃ m, g x.id = some m ∧ m.openable = true) :
    check sigs c (.openField xs l) = some (c, .elems xs.length) :=
  Masks.check_openField' sigs c xs l hl fun x hxm => by
    obtain ⟨m, h1, h2⟩ := hx x hxm
    exact ⟨m, by rw [h.marks]; exact h1, h2⟩

/-! ## The curve programs' signatures -/

/-- `a` public outputs, then `b` never-opened ones. -/
def marksPN (a b : Nat) : List Mark := List.replicate a .pub ++ List.replicate b .never

theorem marksPN_length (a b : Nat) : (marksPN a b).length = a + b := by simp [marksPN]

theorem marksPN_getD (a b i : Nat) (hi : i < a) : (marksPN a b).getD i .never = .pub := by
  rw [marksPN, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_replicate,
    if_pos hi]
  rfl

/-- The V3 signatures of the curve programs as the compiled programs declare them (data inputs,
masks, output marks; public outputs: `edwards-on-curve` 0; `edwards-prepare` 0–504; `lift-open`
0–4; `lift-point` 0, 3, 4; `edwards-prepare-hinted` 0–629; `edwards-bit-table` 0–125; none for the
others), and `field-quotient` (`Inversion.quotient_wf`). -/
structure CurveProgs (P : Bytes → Option ProgSig) : Prop where
  onCurve : P onCurveName = some ⟨2, 0, marksPN 1 0⟩
  addU : P addUName = some ⟨4, 0, marksPN 0 2⟩
  x25519 : P x25519Name = some ⟨257, 0, marksPN 0 2⟩
  prepare : P prepareName = some ⟨506, 2031, marksPN 505 1026⟩
  offsetSum : P offsetSumName = some ⟨194, 128, marksPN 0 1⟩
  liftOpen : P liftOpenName = some ⟨8, 0, marksPN 5 1⟩
  liftPoint : P liftPointName = some ⟨9, 5, [.pub, .never, .never, .pub, .pub]⟩
  prepareHinted : P prepareHintedName = some ⟨884, 1150, marksPN 630 1026⟩
  offsetSumFast : P offsetSumFastName = some ⟨194, 0, marksPN 0 2⟩
  bitTable : P bitTableName = some ⟨380, 252, marksPN 126 1024⟩
  bitSum : P bitSumName = some ⟨1261, 0, marksPN 0 2⟩
  affineBitSum : P affineBitSumName = some ⟨757, 0, marksPN 0 2⟩
  signatureSum : P signatureSumName = some ⟨2546, 2, marksPN 0 2⟩
  torsion : P torsionName = some ⟨7, 4, marksPN 0 2⟩
  quotient : P Inversion.quotientName = some ⟨2, 1, [.never, .pub]⟩

end WFB

end TlsMpc.Node.Flows.Curve
