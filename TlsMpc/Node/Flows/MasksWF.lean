import TlsMpc.Node.Flows.MasksHonest

/-!
# `Masks.generate` is well formed: the shell's `check` admits every instruction

REORGANIZATION_PLAN.md 5.4, 7.1; stage S10. The test vectors show that every batch of the test
instance passes `checkBatch`. This file proves it in general (`generate_wf`): from any context in
which the Boolean ids from `b` and the field ids from `f` were never defined, with the word
circuits and field programs of the script loaded under their signatures (`WordSigs`, `ProgSigs`)
and the bundles within the shell's width limit (`Sizes`; true of every deployed profile:
`profile_sizes`), every instruction of `generate`, on every branch (every reply of the expected
shape), passes `check` in the context the branch has built: handles are live when read, fresh when
defined, opened only when their marks allow it (the candidates are `revealable`, the `modadd-open`
words and the flags `pub`, the programs' check outputs `pub`), and the widths fit.

Also the generic pieces the other S10 flows' `_wf` theorems use: `WFP_seqs`, `WFP_openFieldThen`,
`defFields_ok`, `defBlock` (a block of fresh field handles), `check_fieldInput'`, `check_openField'`,
`check_program'`, `check_pick'`, `checkAll_adds`.
-/

namespace TlsMpc.Node.Flows.Masks

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees Silent blankWire Leaves seqs_cons seqs_nil push Fresh
  checkAll WFP_seq WFP_openThen frees_wfp check_boolInputBoth check_concat check_run check_slice check_openBool
  check_freeBool' bool?_push bool?_push_self bool?_push_of_ne bool?_drop bool?_drop_of_ne useBool_keep useBools_cons
  useBools_nil)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Conv
open TlsMpc.FieldDag (F modulus)

/-! ## Generic: blocks through `check` -/

theorem WFP_seqs {α : Type} (sigs : Bytes → Option Sig) {Q : Ctx → α → Prop} (s : Script α) :
    ∀ (is : List Instr) (c c' : Ctx), checkAll sigs c is = some c' → WFP sigs Q c' s → WFP sigs Q c (seqs is s)
  | [], c, c', h, hs => by
    simp only [checkAll, Option.some.injEq] at h
    subst h
    exact hs
  | i :: is, c, c', h, hs => by
    simp only [checkAll] at h
    cases hc : check sigs c i.skel with
    | none => rw [hc] at h; simp at h
    | some pr =>
      obtain ⟨c1, sh⟩ := pr
      cases sh with
      | unit =>
        rw [hc] at h
        exact WFP_seq sigs c c1 i _ hc (WFP_seqs sigs s is c1 c' h hs)
      | _ => rw [hc] at h; simp at h

theorem checkAll_cons (sigs : Bytes → Option Sig) (c c1 : Ctx) (i : Instr) (is : List Instr)
    (h : check sigs c i.skel = some (c1, .unit)) : checkAll sigs c (i :: is) = checkAll sigs c1 is := by
  simp [checkAll, h]

theorem WFP_openFieldThen {α : Type} (sigs : Bytes → Option Sig) {Q : Ctx → α → Prop} (c c' : Ctx)
    (hs : List FieldH) (l : Label) (k : List F → Script α) (m : Nat)
    (hc : check sigs c (.openField hs l) = some (c', .elems m))
    (hk : ∀ v : List F, v.length = m → WFP sigs Q c' (k v)) : WFP sigs Q c (openFieldThen hs l k) :=
  WFP.step c c' (.elems m) _ _ hc (fun r hr => by
    cases r with
    | elems v => exact hk v hr
    | _ => exact absurd hr (by simp [Shape.Fits]))

theorem bool?_congr {c c' : Ctx} (h : c'.bools = c.bools) (x : BoolH) : c'.bool? x = c.bool? x := by
  simp [Ctx.bool?, h]

/-! ## Generic: field handles in the shell's context -/

theorem defFields_ok : ∀ (hs : List FieldH) (ms : List Mark) (c : Ctx), ms.length = hs.length →
    (hs.map (·.id)).Nodup → (∀ h ∈ hs, h.id ∉ c.seenF) →
    ∃ c', c.defFields hs ms = some c' ∧ c'.bools = c.bools ∧ c'.seenB = c.seenB ∧ c'.progs = c.progs ∧
      (∀ x : FieldH, (∀ h ∈ hs, h.id ≠ x.id) → c'.field? x = c.field? x) ∧
      (∀ j, j ∈ c'.seenF ↔ j ∈ c.seenF ∨ ∃ h ∈ hs, h.id = j)
  | [], [], c, _, _, _ => ⟨c, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun j => by simp⟩
  | h :: hs, m :: ms, c, hl, hn, hf => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    have h0 : h.id ∉ c.seenF := hf h (by simp)
    have hd : c.defField h m = some { c with fields := (h.id, m) :: c.fields, seenF := h.id :: c.seenF } := by
      simp [Ctx.defField, h0]
    obtain ⟨c', e1, e2, e3, e4, e5, e6⟩ := defFields_ok hs ms
      { c with fields := (h.id, m) :: c.fields, seenF := h.id :: c.seenF } (by simpa using hl) hn.2
      (fun g hg => by
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => hn.1 ⟨g, hg, e⟩, hf g (by simp [hg])⟩)
    refine ⟨c', by simp [Ctx.defFields, hd, e1], e2, e3, e4, fun x hx => ?_, fun j => ?_⟩
    · rw [e5 x (fun g hg => hx g (by simp [hg])), Ctx.field?_defField hd, if_neg (fun e => hx h (by simp) e.symm)]
    · rw [e6 j]
      simp only [List.mem_cons]
      constructor
      · rintro ((rfl | h1) | ⟨g, hg, rfl⟩)
        · exact Or.inr ⟨h, Or.inl rfl, rfl⟩
        · exact Or.inl h1
        · exact Or.inr ⟨g, Or.inr hg, rfl⟩
      · rintro (h1 | ⟨g, hg, rfl⟩)
        · exact Or.inl (Or.inr h1)
        · rcases hg with rfl | hg
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨g, hg, rfl⟩
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl

theorem mem_zip_replicate {α β : Type} (m : β) : ∀ (l : List α) (a : α), a ∈ l →
    (a, m) ∈ l.zip (List.replicate l.length m)
  | [], a, ha => by simp at ha
  | x :: l, a, ha => by
    simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.mem_cons] at ha ⊢
    rcases ha with rfl | ha
    · exact Or.inl rfl
    · exact Or.inr (mem_zip_replicate m l a ha)

theorem defFields_append : ∀ (hs₁ : List FieldH) (ms₁ : List Mark) (hs₂ : List FieldH) (ms₂ : List Mark) (c : Ctx),
    ms₁.length = hs₁.length →
    c.defFields (hs₁ ++ hs₂) (ms₁ ++ ms₂) = (c.defFields hs₁ ms₁).bind fun c' => c'.defFields hs₂ ms₂
  | [], [], hs₂, ms₂, c, _ => rfl
  | h :: hs₁, m :: ms₁, hs₂, ms₂, c, hl => by
    simp only [List.cons_append, Ctx.defFields, Option.bind_eq_bind]
    cases hd : c.defField h m with
    | none => rfl
    | some c1 =>
      simp only [Option.bind_some]
      exact defFields_append hs₁ ms₁ hs₂ ms₂ c1 (by simpa using hl)
  | [], _ :: _, _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, hl => by simp at hl

/-- Two lists of `n` handles each, defined one after the other with the same mark. -/
theorem defFields_two (c c1 c2 : Ctx) (hs₁ hs₂ : List FieldH) (n : Nat) (m : Mark) (h1 : hs₁.length = n)
    (h2 : hs₂.length = n) (d1 : c.defFields hs₁ (List.replicate n m) = some c1)
    (d2 : c1.defFields hs₂ (List.replicate n m) = some c2) :
    c.defFields (hs₁ ++ hs₂) (List.replicate (hs₁.length + hs₂.length) m) = some c2 := by
  rw [h1, h2, ← List.replicate_append_replicate,
    defFields_append _ _ _ _ _ (by rw [List.length_replicate, h1]), d1]
  simp only [Option.bind_some]
  exact d2

/-- **A block of `n` consecutive fresh field handles**, all with mark `m`: `defFields` accepts it;
the block's handles then carry `m`, every other field handle is as before, and nothing else
changes. -/
theorem defBlock (c : Ctx) (g : Nat → FieldH) (base n : Nat) (m : Mark) (hg : ∀ i, i < n → (g i).id = base + i)
    (hfresh : ∀ j, base ≤ j → j < base + n → j ∉ c.seenF) :
    ∃ c', c.defFields ((List.range n).map g) (List.replicate n m) = some c' ∧ c'.bools = c.bools ∧
      c'.seenB = c.seenB ∧ c'.progs = c.progs ∧
      (∀ x : FieldH, c'.field? x = if base ≤ x.id ∧ x.id < base + n then some m else c.field? x) ∧
      (∀ j, j ∈ c'.seenF ↔ j ∈ c.seenF ∨ (base ≤ j ∧ j < base + n)) := by
  have hids : ((List.range n).map g).map (·.id) = List.range' base n := by
    rw [List.map_map, ← map_range_add]
    apply List.map_congr_left
    intro i hi
    exact hg i (List.mem_range.mp hi)
  have hmem : ∀ h ∈ (List.range n).map g, base ≤ h.id ∧ h.id < base + n := by
    intro h hh
    simp only [List.mem_map, List.mem_range] at hh
    obtain ⟨i, hi, rfl⟩ := hh
    rw [hg i hi]
    omega
  obtain ⟨c', e1, e2, e3, e4, e5, e6⟩ := defFields_ok ((List.range n).map g) (List.replicate n m) c (by simp)
    (by rw [hids]; exact List.nodup_range') (fun h hh => hfresh _ (hmem h hh).1 (hmem h hh).2)
  have hmarks := Ctx.defFields_marks c c' _ _ e1
  refine ⟨c', e1, e2, e3, e4, fun x => ?_, fun j => ?_⟩
  · split
    · next hx =>
      have hi : x.id - base < n := by omega
      have e : x.id = (g (x.id - base)).id := by rw [hg _ hi]; omega
      have := hmarks (g (x.id - base), m) (by
        have := mem_zip_replicate m ((List.range n).map g) (g (x.id - base))
          (List.mem_map.mpr ⟨_, List.mem_range.mpr hi, rfl⟩)
        simpa using this)
      show c'.fields.lookup x.id = some m
      rw [e]
      exact this
    · next hx =>
      exact e5 x (fun h hh e => hx (e ▸ hmem h hh))
  · rw [e6 j]
    constructor
    · rintro (h1 | ⟨h, hh, rfl⟩)
      · exact Or.inl h1
      · exact Or.inr (hmem h hh)
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr ⟨g (j - base), List.mem_map.mpr ⟨_, List.mem_range.mpr (by omega), rfl⟩, by
          rw [hg _ (by omega)]; omega⟩

theorem check_fieldInput' (sigs : Bytes → Option Sig) (c c' : Ctx) (oa ob : List FieldH) (k : FieldIn) (rev : Bool)
    (hab : oa.length = ob.length)
    (hd : c.defFields (oa ++ ob) (List.replicate (oa.length + ob.length) (Mark.ofInput rev)) = some c') :
    check sigs c (.fieldInput oa ob k rev ()) = some (c', .unit) := by
  simp only [check]
  rw [hd]
  simp [guard, hab]

theorem check_openField' (sigs : Bytes → Option Sig) (c : Ctx) (hs : List FieldH) (l : Label) (hl : l.code ≠ 0)
    (h : ∀ g ∈ hs, ∃ m, c.field? g = some m ∧ m.openable = true) :
    check sigs c (.openField hs l) = some (c, .elems hs.length) := by
  have hm : hs.mapM c.field? = some (hs.map fun g => (c.field? g).getD .never) :=
    mapM_vals _ _ hs (fun g hg => by
      obtain ⟨m, h1, _⟩ := h g hg
      rw [h1]
      rfl)
  have ha : ∀ g ∈ hs, ((c.field? g).getD .never).openable = true := by
    intro g hg
    obtain ⟨m, h1, h2⟩ := h g hg
    simp [h1, h2]
  simp only [check]
  rw [hm]
  simp [guard, hl]
  rw [if_pos ha]
  rfl

theorem check_program' (sigs : Bytes → Option Sig) (c c' : Ctx) (name : Bytes) (copies : Nat)
    (ins outs : List FieldH) (l : Label) (s : ProgSig) (hl : l.code ≠ 0) (hp : c.progs name = some s)
    (hm : s.masks = 0) (hc : 0 < copies) (hcw : copies ≤ maxWidth) (hi : ins.length = copies * s.inputs)
    (ho : outs.length = copies * s.outMarks.length) (hlive : ∀ g ∈ ins, (c.field? g).isSome = true)
    (hd : c.defFields outs (List.replicate copies s.outMarks).flatten = some c') :
    check sigs c (.program name copies ins [] outs l) = some (c', .unit) := by
  simp [check, guard, hl, hp, hc, hcw, hi, hm, ho, Ctx.useMasks, hd]
  rw [if_pos hlive]
  rfl

theorem check_pick' (sigs : Bytes → Option Sig) {c c' : Ctx} {n : Nat} {h : BoolH} {idx : List Nat} {i : BoolInfo}
    (hu : c.useBool h = some (i, c')) (hidx : idx.all (· < i.marks.length) = true) (hf : Fresh c' n)
    (hw : idx.length ≤ maxWidth) :
    check sigs c (.pick ⟨n⟩ h idx) =
      some (push c' n ⟨idx.map (fun j => i.marks.getD j .never), i.once⟩, .unit) := by
  have hidx' : ∀ x ∈ idx, x < i.marks.length := by
    simpa [List.all_eq_true] using hidx
  simp [check, hu, guard, Ctx.defBool, hf n (Nat.le_refl n), push]
  rw [if_pos hidx', if_neg (by omega)]
  rfl

theorem pick_marks_openable (idx : List Nat) (n : Nat) (m : Mark) (hm : m.openable = true)
    (hidx : idx.all (· < n) = true) :
    (idx.map fun j => (List.replicate n m).getD j .never).all Mark.openable = true := by
  rw [List.all_map, List.all_eq_true]
  intro j hj
  have := List.all_eq_true.mp hidx j hj
  simp only [decide_eq_true_eq] at this
  simp [List.getD_eq_getElem?_getD, this, hm]

/-- **A block of field additions of revealable operands into fresh, distinct outputs** passes
`check`; the outputs are revealable, nothing else changes. -/
theorem checkAll_adds (sigs : Bytes → Option Sig) : ∀ (ts : List (FieldH × FieldH × FieldH)) (c : Ctx),
    (ts.map (·.1.id)).Nodup → (∀ t ∈ ts, t.1.id ∉ c.seenF) →
    (∀ t ∈ ts, c.field? t.2.1 = some .revealable ∧ c.field? t.2.2 = some .revealable) →
    (∀ t ∈ ts, ∀ t' ∈ ts, t.1.id ≠ t'.2.1.id ∧ t.1.id ≠ t'.2.2.id) →
    ∃ c', checkAll sigs c (ts.map fun t => (.fieldAdd t.1 t.2.1 t.2.2 : Instr)) = some c' ∧ c'.bools = c.bools ∧
      c'.seenB = c.seenB ∧ c'.progs = c.progs ∧
      (∀ x : FieldH, (∀ t ∈ ts, t.1.id ≠ x.id) → c'.field? x = c.field? x) ∧
      (∀ t ∈ ts, c'.field? t.1 = some .revealable) ∧
      (∀ j, j ∈ c'.seenF ↔ j ∈ c.seenF ∨ ∃ t ∈ ts, t.1.id = j)
  | [], c, _, _, _, _ => ⟨c, rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp, fun j => by simp⟩
  | t :: ts, c, hn, hf, hop, hd => by
    obtain ⟨out, a, b⟩ := t
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    have h0 : out.id ∉ c.seenF := hf (out, a, b) (by simp)
    obtain ⟨ha, hb⟩ := hop (out, a, b) (by simp)
    have hdef : c.defField out .revealable =
        some { c with fields := (out.id, .revealable) :: c.fields, seenF := out.id :: c.seenF } := by
      simp [Ctx.defField, h0]
    have hck : check sigs c (InstrP.skel (.fieldAdd out a b : Instr)) =
        some ({ c with fields := (out.id, .revealable) :: c.fields, seenF := out.id :: c.seenF }, .unit) := by
      simp [check, InstrP.skel, InstrP.map, ha, hb, Mark.join, hdef]
    have hfr : ∀ t ∈ ts, out.id ≠ t.2.1.id ∧ out.id ≠ t.2.2.id :=
      fun t ht => hd (out, a, b) (by simp) t (by simp [ht])
    obtain ⟨c', e1, e2, e3, e4, e5, e6, e7⟩ := checkAll_adds sigs ts
      { c with fields := (out.id, .revealable) :: c.fields, seenF := out.id :: c.seenF } hn.2
      (fun t ht => by
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => hn.1 ⟨t, ht, e⟩, hf t (by simp [ht])⟩)
      (fun t ht => by
        obtain ⟨h1, h2⟩ := hop t (by simp [ht])
        obtain ⟨n1, n2⟩ := hfr t ht
        rw [Ctx.field?_defField hdef, Ctx.field?_defField hdef, if_neg (Ne.symm n1), if_neg (Ne.symm n2)]
        exact ⟨h1, h2⟩)
      (fun t ht t' ht' => hd t (by simp [ht]) t' (by simp [ht']))
    refine ⟨c', ?_, e2, e3, e4, fun x hx => ?_, fun t ht => ?_, fun j => ?_⟩
    · rw [List.map_cons, checkAll_cons sigs c _ _ _ hck]
      exact e1
    · rw [e5 x (fun t ht => hx t (by simp [ht])), Ctx.field?_defField hdef,
        if_neg (fun e => hx (out, a, b) (by simp) e.symm)]
    · simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · rw [e5 out (fun t ht e => hn.1 ⟨t, ht, e⟩), Ctx.field?_defField hdef, if_pos rfl]
      · exact e6 t ht
    · rw [e7 j]
      simp only [List.mem_cons]
      constructor
      · rintro ((rfl | h1) | ⟨g, hg, rfl⟩)
        · exact Or.inr ⟨(out, a, b), Or.inl rfl, rfl⟩
        · exact Or.inl h1
        · exact Or.inr ⟨g, Or.inr hg, rfl⟩
      · rintro (h1 | ⟨g, hg, rfl⟩)
        · exact Or.inl (Or.inr h1)
        · rcases hg with rfl | hg
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨g, hg, rfl⟩

/-! ## What `generate` asks of the shell -/

/-- The word circuits' signatures (width of one copy, output marks): what `Env.sigs` gives for a
`WordLoaded` environment. -/
structure WordSigs (sigs : Bytes → Option Sig) : Prop where
  modaddOpen : sigs modaddOpenName = some ⟨510, wordPub⟩
  finalizeMask : sigs finalizeMaskName = some ⟨510, finalMarks⟩
  finalizeBits : sigs finalizeBitsName = some ⟨510, finalMarks⟩

theorem wordSigs_of_loaded {E : Env} (h : WordLoaded E) : WordSigs E.sigs :=
  ⟨by simp [Env.sigs, h.modaddOpen, modaddOpenC], by simp [Env.sigs, h.finalizeMask, finalizeMaskC],
    by simp [Env.sigs, h.finalizeBits, finalizeBitsC]⟩

/-- The field programs' signatures in the shell's context. -/
structure ProgSigs (c : Ctx) : Prop where
  recompose : c.progs recomposeName = some ⟨256, 0, [.pub]⟩
  bitCheck : c.progs bitCheckName = some ⟨1, 0, [.pub]⟩
  bitXor : c.progs bitXorName = some ⟨2, 0, [.never]⟩

/-- The bundles fit the shell's width limit, and there is something to do. -/
structure Sizes (p : Params) : Prop where
  hM : 0 < p.M
  hD : 0 < p.D
  hbits : p.bits ≤ p.N
  bundle : 2 * (p.M * W) ≤ maxWidth
  bucket : p.D * 510 ≤ maxWidth
  final : p.N * 510 ≤ maxWidth

/-- **The shell's context during a generation** (after the inputs): the candidate bundle `b + 2`
is live, revealable, of 2·M·255 bits; the two input bundles are live; the candidate field handles
are live and revealable; Boolean ids from `nb` and field ids from `nf` were never defined; the
programs are loaded. -/
structure Gen (p : Params) (b f : Nat) (c : Ctx) (nb nf : Nat) : Prop where
  hnb : b + 3 ≤ nb
  fresh : Fresh c nb
  hb2 : c.bool? ⟨b + 2⟩ = some ⟨List.replicate (2 * (p.M * W)) .revealable, false⟩
  hb0 : (c.bool? ⟨b⟩).isSome = true
  hb1 : (c.bool? ⟨b + 1⟩).isSome = true
  cand : ∀ o, o < 2 → ∀ k, k < p.M → c.field? (fOf p f o k) = some .revealable
  freshF : ∀ j, nf ≤ j → j ∉ c.seenF
  progs : ProgSigs c

namespace Gen

variable {p : Params} {b f : Nat} {c : Ctx} {nb nf : Nat}

theorem push' (g : Gen p b f c nb nf) (n : Nat) (hn : nb ≤ n) (i : BoolInfo) : Gen p b f (push c n i) (n + 1) nf :=
  ⟨by have := g.hnb; omega, g.fresh.push n hn i,
    by rw [bool?_push_of_ne _ _ _ _ (by have := g.hnb; show b + 2 ≠ n; omega)]; exact g.hb2,
    by rw [bool?_push_of_ne _ _ _ _ (by have := g.hnb; show b ≠ n; omega)]; exact g.hb0,
    by rw [bool?_push_of_ne _ _ _ _ (by have := g.hnb; show b + 1 ≠ n; omega)]; exact g.hb1,
    g.cand, g.freshF, ⟨g.progs.recompose, g.progs.bitCheck, g.progs.bitXor⟩⟩

theorem drop (g : Gen p b f c nb nf) (id : Nat) (hid : b + 3 ≤ id) : Gen p b f (c.dropBool id) nb nf :=
  ⟨g.hnb, g.fresh.drop id,
    by rw [bool?_drop_of_ne _ _ _ (by show b + 2 ≠ id; omega)]; exact g.hb2,
    by rw [bool?_drop_of_ne _ _ _ (by show b ≠ id; omega)]; exact g.hb0,
    by rw [bool?_drop_of_ne _ _ _ (by show b + 1 ≠ id; omega)]; exact g.hb1,
    g.cand, g.freshF, ⟨g.progs.recompose, g.progs.bitCheck, g.progs.bitXor⟩⟩

/-- A change of the field side only. -/
theorem ofFields (g : Gen p b f c nb nf) {c' : Ctx} {nf' : Nat} (hb : c'.bools = c.bools) (hs : c'.seenB = c.seenB)
    (hp : c'.progs = c.progs) (hc : ∀ o, o < 2 → ∀ k, k < p.M → c'.field? (fOf p f o k) = some .revealable)
    (hf : ∀ j, nf' ≤ j → j ∉ c'.seenF) : Gen p b f c' nb nf' :=
  ⟨g.hnb, g.fresh.of_seenB hs, by rw [bool?_congr hb]; exact g.hb2, by rw [bool?_congr hb]; exact g.hb0,
    by rw [bool?_congr hb]; exact g.hb1, hc, hf,
    ⟨by rw [hp]; exact g.progs.recompose, by rw [hp]; exact g.progs.bitCheck, by rw [hp]; exact g.progs.bitXor⟩⟩

end Gen

/-! ## The cut and the bucket phases -/

theorem wordAt_length (p : Params) (o c : Nat) : (wordAt p o c).length = W := by simp [wordAt]

theorem wordAt_idx (p : Params) (o c : Nat) (ho : o < 2) (hc : c < p.M) :
    ∀ i ∈ wordAt p o c, i < 2 * (p.M * W) := by
  intro i hi
  simp only [wordAt, List.mem_map, List.mem_range] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  exact bitAt_lt p o c k ho hc hk

theorem cutBits_idx (p : Params) (π₁ : List Nat) (hπ : ∀ k ∈ cutOf p π₁, k < p.M) :
    (cutBits p π₁).all (· < (List.replicate (2 * (p.M * W)) Mark.revealable).length) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq, List.length_replicate, cutBits, List.mem_flatMap]
  rintro i ⟨o, ho, c, hc, hi⟩
  exact wordAt_idx p o c (owners_lt ho) (hπ c hc) i hi

theorem cutBits_length (p : Params) (π₁ : List Nat) : (cutBits p π₁).length = 2 * ((cutOf p π₁).length * W) := by
  unfold cutBits
  rw [length_flatMap_const _ ((cutOf p π₁).length * W) owners
    (fun o _ => length_flatMap_const _ W _ (fun c _ => wordAt_length p o c))]
  rfl

theorem bucketBits_length (p : Params) (π₁ π₂ : List Nat) : (bucketBits p π₁ π₂).length = p.D * 510 := by
  unfold bucketBits
  rw [length_flatMap_const _ 510 (pairs p) (fun e _ => by
    rw [List.length_append, wordAt_length, wordAt_length]
    rfl), length_pairs]

theorem bucketBits_idx (p : Params) (π₁ π₂ : List Nat) (hπ₁ : ∀ k ∈ π₁, k < p.M) (hM : 0 < p.M) :
    (bucketBits p π₁ π₂).all (· < (List.replicate (2 * (p.M * W)) Mark.revealable).length) = true := by
  have hml := member_lt p π₁ π₂ hπ₁ hM
  simp only [List.all_eq_true, decide_eq_true_eq, List.length_replicate, bucketBits, List.mem_flatMap,
    List.mem_append]
  rintro i ⟨e, he, hi | hi⟩
  · exact wordAt_idx p e.1 _ (mem_pairs p e he) (hml _ _) i hi
  · exact wordAt_idx p e.1 _ (mem_pairs p e he) (hml _ _) i hi

theorem zipIdx_snd_lt {α : Type} {l : List α} {e : α × Nat} (h : e ∈ l.zipIdx) : e.2 < l.length := by
  rw [List.zipIdx_eq_zip_range'] at h
  have := (List.of_mem_zip h).2
  simpa using (List.mem_range'_1.mp this).2

theorem all_pub (n : Nat) (ms : List Mark) (h : ∀ m ∈ ms, m = .pub) :
    ((List.replicate n ms).flatten).all Mark.openable = true := by
  rw [List.all_eq_true]
  intro m hm
  simp only [List.mem_flatten, List.mem_replicate] at hm
  obtain ⟨l, ⟨-, rfl⟩, hm⟩ := hm
  rw [h m hm]
  rfl

section Phases

variable (sigs : Bytes → Option Sig) {p : Params} {b f : Nat} {c : Ctx}

theorem cutPhase_wfp {nf : Nat} (g : Gen p b f c (b + 3) nf) (sz : Sizes p) (π₁ : List Nat)
    (hπ : ∀ k ∈ cutOf p π₁, k < p.M) (hcl : (cutOf p π₁).length ≤ p.M) :
    WFP sigs (fun c' _ => Gen p b f c' (b + 4) nf) c (cutPhase p b f π₁) := by
  have hidx := cutBits_idx p π₁ hπ
  have hlen : (cutBits p π₁).length ≤ maxWidth := by
    rw [cutBits_length]
    exact Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right W hcl)) sz.bundle
  unfold cutPhase
  refine WFP_seq sigs c _ _ _ (check_pick' sigs (useBool_keep g.hb2 rfl) hidx g.fresh hlen) ?_
  have g1 := g.push' (b + 3) (Nat.le_refl _)
    ⟨(cutBits p π₁).map (fun j => (List.replicate (2 * (p.M * W)) Mark.revealable).getD j .never), false⟩
  refine WFP_openFieldThen sigs _ _ _ _ _ _ (check_openField' sigs _ _ _ (by decide) (fun x hx => ?_))
    (fun ve _ => ?_)
  · simp only [cutFields, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨o, ho, k, hk, rfl⟩ := hx
    exact ⟨.revealable, g1.cand o (owners_lt ho) k (hπ k hk), rfl⟩
  refine WFP_openThen sigs _ _ ⟨b + 3⟩ _ _ _ (check_openBool sigs (by decide)
    (useBool_keep (bool?_push_self _ _ _) rfl) (pick_marks_openable _ _ _ rfl (by simpa using hidx)))
    (fun vb _ => ?_)
  split
  · exact WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by rw [bool?_push_self]; rfl))
      (WFP.done _ _ (g1.drop (b + 3) (Nat.le_refl _)))
  · exact WFP.abort _ _

theorem bucketPhase_wfp (ws : WordSigs sigs) (g : Gen p b f c (b + 4) (f + 2 * p.M)) (sz : Sizes p)
    (π₁ π₂ : List Nat) (hπ₁ : ∀ k ∈ π₁, k < p.M) :
    WFP sigs (fun c' _ => Gen p b f c' (b + 6) (f + 2 * p.M + p.D)) c (bucketPhase p b f π₁ π₂) := by
  have hml := member_lt p π₁ π₂ hπ₁ sz.hM
  have hidx := bucketBits_idx p π₁ π₂ hπ₁ sz.hM
  have hbl := bucketBits_length p π₁ π₂
  have hbk := sz.bucket
  unfold bucketPhase bucketBlock
  simp only [List.cons_append, List.nil_append, seqs_cons]
  refine WFP_seq sigs c _ _ _ (check_pick' sigs (useBool_keep g.hb2 rfl) hidx g.fresh (by rw [hbl]; exact hbk)) ?_
  have g1 := g.push' (b + 4) (Nat.le_refl _)
    ⟨(bucketBits p π₁ π₂).map (fun j => (List.replicate (2 * (p.M * W)) Mark.revealable).getD j .never), false⟩
  refine WFP_seq sigs _ _ _ _ (check_run sigs ws.modaddOpen sz.hD (useBool_keep (bool?_push_self _ _ _) rfl)
    (by simpa using hbl) g1.fresh (Nat.le_trans (Nat.le_mul_of_pos_right p.D (by decide)) hbk) (by
      show p.D * (List.replicate 255 Mark.pub).length ≤ maxWidth
      rw [List.length_replicate]
      exact Nat.le_trans (Nat.mul_le_mul_left p.D (by decide)) hbk)) ?_
  have g2 := g1.push' (b + 5) (Nat.le_refl _) ⟨(List.replicate p.D wordPub).flatten, false⟩
  rw [sumAdds_eq]
  obtain ⟨c3, a1, a2, a3, a4, a5, a6, a7⟩ := checkAll_adds sigs (sumTriples p f π₁ π₂) _
    (by
      simp only [sumTriples, List.map_map, Function.comp_def, sumH]
      have : ((pairs p).zipIdx.map fun e => f + 2 * p.M + e.2) = (List.range' (f + 2 * p.M) (pairs p).length) := by
        rw [List.zipIdx_eq_zip_range']
        apply List.ext_getElem <;> simp
      rw [this]
      exact List.nodup_range')
    (fun t ht => by
      simp only [sumTriples, List.mem_map] at ht
      obtain ⟨e, -, rfl⟩ := ht
      exact g2.freshF _ (by simp only [sumH]; omega))
    (fun t ht => by
      simp only [sumTriples, List.mem_map] at ht
      obtain ⟨e, he, rfl⟩ := ht
      have ho := mem_pairs p e.1 (mem_zipIdx_fst he)
      exact ⟨g2.cand _ ho _ (hml _ _), g2.cand _ ho _ (hml _ _)⟩)
    (fun t ht t' ht' => by
      simp only [sumTriples, List.mem_map] at ht ht'
      obtain ⟨e, -, rfl⟩ := ht
      obtain ⟨e', he', rfl⟩ := ht'
      have ho := mem_pairs p e'.1 (mem_zipIdx_fst he')
      have h1 := fOf_lt p f _ _ ho (hml e'.1.2.1 0)
      have h2 := fOf_lt p f _ _ ho (hml e'.1.2.1 e'.1.2.2)
      simp only [sumH]
      omega)
  refine WFP_seqs sigs _ _ _ c3 a1 ?_
  have hsum : ∀ t ∈ sumTriples p f π₁ π₂, f + 2 * p.M ≤ t.1.id ∧ t.1.id < f + 2 * p.M + p.D := by
    intro t ht
    simp only [sumTriples, List.mem_map] at ht
    obtain ⟨e, he, rfl⟩ := ht
    have := zipIdx_snd_lt he
    rw [length_pairs] at this
    simp only [sumH]
    omega
  have g3 : Gen p b f c3 (b + 6) (f + 2 * p.M + p.D) := g2.ofFields a2 a3 a4
    (fun o ho k hk => by
      rw [a5 _ (fun t ht e => by
        have := hsum t ht
        have := fOf_id_lt p f o k ho hk
        omega)]
      exact g2.cand o ho k hk)
    (fun j hj hmem => by
      rcases (a7 j).mp hmem with h1 | ⟨t, ht, rfl⟩
      · exact g2.freshF j (by omega) h1
      · have := hsum t ht
        omega)
  refine WFP_openFieldThen sigs _ _ _ _ _ _ (check_openField' sigs c3 _ _ (by decide) (fun x hx => ?_))
    (fun ve _ => ?_)
  · simp only [sums, List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact ⟨.revealable, a6 (sumH p f e.2, fOf p f e.1.1 (member p π₁ π₂ e.1.2.1 0),
      fOf p f e.1.1 (member p π₁ π₂ e.1.2.1 e.1.2.2)) (by
        simp only [sumTriples, List.mem_map]
        exact ⟨e, he, rfl⟩), rfl⟩
  refine WFP_openThen sigs _ _ ⟨b + 5⟩ _ _ _ (check_openBool sigs (by decide)
    (useBool_keep (by rw [bool?_congr a2]; exact bool?_push_self _ _ _) rfl)
    (all_pub p.D wordPub (fun m hm => by
      simp only [wordPub, List.mem_replicate] at hm
      exact hm.2))) (fun vb _ => ?_)
  split
  · refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by
      rw [bool?_congr a2, bool?_push_of_ne _ _ _ _ (by show b + 4 ≠ b + 5; omega), bool?_push_self]
      rfl)) ?_
    refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by
      rw [bool?_drop_of_ne _ _ _ (by show b + 5 ≠ b + 4; omega), bool?_congr a2, bool?_push_self]
      rfl)) ?_
    exact WFP.done _ _ ((g3.drop (b + 4) (by omega)).drop (b + 5) (by omega))
  · exact WFP.abort _ _

end Phases

/-! ## Marks of the finalize bundle; more generic blocks -/

/-- The marks of `n` finalize outputs: 255 never, then the public flag, `n` times. -/
def FM (n : Nat) : List Mark := (List.replicate n finalMarks).flatten

theorem finalMarks_length : finalMarks.length = 256 := by
  show (List.replicate 255 Mark.never ++ [Mark.pub]).length = 256
  rw [List.length_append, List.length_replicate]
  rfl

theorem finalMarks_each (n : Nat) : ∀ y ∈ List.replicate n finalMarks, y.length = 256 := by
  intro y hy
  rw [List.eq_of_mem_replicate hy]
  exact finalMarks_length

theorem FM_length (n : Nat) : (FM n).length = n * 256 := by
  unfold FM
  rw [length_flatten_eq 256 _ (finalMarks_each n), List.length_replicate]

theorem FM_add (a b : Nat) : FM a ++ FM b = FM (a + b) := by
  unfold FM
  rw [← List.replicate_append_replicate, List.flatten_append]

theorem finalMarks_flag : finalMarks.getD 255 Mark.never = Mark.pub := by
  show (List.replicate 255 Mark.never ++ [Mark.pub]).getD 255 Mark.never = Mark.pub
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [List.length_replicate]; exact Nat.le_refl _),
    List.length_replicate]
  rfl

theorem FM_flag (n j : Nat) (hj : j < n) : (FM n).getD (256 * j + 255) Mark.never = Mark.pub := by
  unfold FM
  have := flatten_getD 256 (List.replicate n finalMarks) j 255 Mark.never (finalMarks_each n) (by simpa using hj)
    (by omega)
  rw [Nat.mul_comm] at this
  rw [this]
  have e : (List.replicate n finalMarks).getD j [] = finalMarks := by
    simp [List.getD_eq_getElem?_getD, hj]
  rw [e]
  exact finalMarks_flag

theorem flatten_replicate_singleton {α : Type} (n : Nat) (a : α) :
    (List.replicate n [a]).flatten = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem frees_wfp' {α : Type} (sigs : Bytes → Option Sig) {Q : Ctx → α → Prop} (s : Script α) :
    ∀ (hs : List BoolH) (c : Ctx), (hs.map (·.id)).Nodup → (∀ h ∈ hs, (c.bool? h).isSome = true) →
      (∀ c' : Ctx, (∀ g : BoolH, c'.bool? g = if g.id ∈ hs.map (·.id) then none else c.bool? g) →
        c'.seenB = c.seenB → c'.fields = c.fields → c'.seenF = c.seenF → c'.progs = c.progs → WFP sigs Q c' s) →
      WFP sigs Q c (seqs (frees hs) s)
  | [], c, _, _, hk => hk c (fun g => by simp) rfl rfl rfl rfl
  | h :: hs, c, hn, hl, hk => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    refine WFP_seq sigs c _ _ _ (check_freeBool' sigs (hl h (by simp))) ?_
    refine frees_wfp' sigs s hs _ hn.2 (fun g hg => ?_) (fun c' h1 h2 h3 h4 h5 => hk c' (fun g => ?_) h2 h3 h4 h5)
    · have hne : g.id ≠ h.id := fun e => hn.1 ⟨g, hg, e⟩
      rw [bool?_drop_of_ne _ _ _ hne]
      exact hl g (by simp [hg])
    · rw [h1 g, bool?_drop]
      by_cases e : g.id = h.id
      · simp [e]
      · by_cases m : g.id ∈ hs.map (·.id)
        · simp [m]
        · simp only [m, if_false, e, List.map_cons, List.mem_cons, false_or]

/-- **A block of slices of one live bundle** into the consecutive fresh handles `base + j`. -/
theorem checkAll_slices (sigs : Bytes → Option Sig) (src : BoolH) (info : BoolInfo) (ho : info.once = false)
    (lo hi : Nat → Nat) (base : Nat) :
    ∀ (n k : Nat) (c : Ctx), c.bool? src = some info → src.id < base + k → Fresh c (base + k) →
      (∀ j, k ≤ j → j < k + n → lo j ≤ hi j ∧ hi j ≤ info.marks.length ∧ hi j - lo j ≤ maxWidth) →
      ∃ c', checkAll sigs c ((List.range' k n).map fun j => (.slice ⟨base + j⟩ src (lo j) (hi j) : Instr)) = some c' ∧
        c'.fields = c.fields ∧ c'.seenF = c.seenF ∧ c'.progs = c.progs ∧ Fresh c' (base + k + n) ∧
        (∀ x : BoolH, x.id < base + k → c'.bool? x = c.bool? x)
  | 0, k, c, _, _, hf, _ => ⟨c, rfl, rfl, rfl, rfl, hf, fun _ _ => rfl⟩
  | n + 1, k, c, hb, hs, hf, hr => by
    obtain ⟨h1, h2, h3⟩ := hr k (Nat.le_refl _) (by omega)
    have hck := check_slice sigs (useBool_keep hb ho) ⟨h1, h2⟩ hf h3
    obtain ⟨c', e1, e2, e3, e4, e5, e6⟩ := checkAll_slices sigs src info ho lo hi base n (k + 1)
      (push c (base + k) ⟨(info.marks.drop (lo k)).take (hi k - lo k), info.once⟩)
      (by rw [bool?_push_of_ne _ _ _ _ (by omega)]; exact hb) (by omega)
      (hf.push (base + k) (Nat.le_refl _) _) (fun j hj1 hj2 => hr j (by omega) (by omega))
    refine ⟨c', ?_, e2, e3, e4, ?_, fun x hx => ?_⟩
    · rw [List.range'_succ, List.map_cons,
        checkAll_cons sigs c _ (.slice ⟨base + k⟩ src (lo k) (hi k)) _ hck]
      exact e1
    · have e : base + (k + 1) + n = base + k + (n + 1) := by omega
      rw [← e]
      exact e5
    · rw [e6 x (by omega), bool?_push_of_ne _ _ _ _ (by omega)]

/-! ## The bit-block phase -/

/-- The shell's context at the bit-block phase. -/
structure BitCtx (p : Params) (b f : Nat) (c : Ctx) : Prop where
  fresh : Fresh c (bitBase p b)
  hb10 : c.bool? ⟨b + 10⟩ = some ⟨FM p.N, false⟩
  cand : ∀ o, o < 2 → ∀ k, k < p.M → (c.field? (fOf p f o k)).isSome = true
  progs : ProgSigs c

theorem BitCtx.ofFields {p : Params} {b f : Nat} {c c' : Ctx} (h : BitCtx p b f c) (hb : c'.bools = c.bools)
    (hs : c'.seenB = c.seenB) (hp : c'.progs = c.progs)
    (hc : ∀ o, o < 2 → ∀ k, k < p.M → (c'.field? (fOf p f o k)).isSome = true) : BitCtx p b f c' :=
  ⟨h.fresh.of_seenB hs, by rw [bool?_congr hb]; exact h.hb10, hc,
    ⟨by rw [hp]; exact h.progs.recompose, by rw [hp]; exact h.progs.bitCheck, by rw [hp]; exact h.progs.bitXor⟩⟩

/-- The context after the coin inputs of the first `k` bit blocks. -/
structure CoinCtx (p : Params) (b f : Nat) (c : Ctx) (k : Nat) : Prop where
  base : BitCtx p b f c
  coins : ∀ o, o < 2 → ∀ j, j < k → ∀ i, i < W → c.field? (coinH p f o j i) = some .never
  seen : ∀ id, id ∈ c.seenF → id < coinBase p f + k * W ∨
    (coinBase p f + p.bits * W ≤ id ∧ id < coinBase p f + p.bits * W + k * W)

theorem coinBase_ge (p : Params) (f : Nat) : f + 2 * p.M ≤ coinBase p f := by
  unfold coinBase maskBase
  omega

theorem coinStep_ctx (sigs : Bytes → Option Sig) {p : Params} {b f : Nat} {c : Ctx} {k : Nat}
    (h : CoinCtx p b f c k) (hk : k < p.bits) (slot : Nat) :
    ∃ c', check sigs c (InstrP.skel (.fieldInput ((List.range W).map (coinH p f 0 k))
        ((List.range W).map (coinH p f 1 k)) .coins false slot : Instr)) = some (c', .unit) ∧
      CoinCtx p b f c' (k + 1) := by
  have hkW := mul_step k p.bits hk
  have hcb := coinBase_ge p f
  obtain ⟨c1, d1, b1, s1, p1, f1, n1⟩ := defBlock c (coinH p f 0 k) (coinBase p f + k * W) W (Mark.ofInput false)
    (fun i _ => by simp [coinH]) (fun j hj1 hj2 hmem => by rcases h.seen j hmem with h' | h' <;> omega)
  obtain ⟨c2, d2, b2, s2, p2, f2, n2⟩ := defBlock c1 (coinH p f 1 k) (coinBase p f + p.bits * W + k * W) W
    (Mark.ofInput false) (fun i _ => by simp [coinH]) (fun j hj1 hj2 hmem => by
      rcases (n1 j).mp hmem with h' | h'
      · rcases h.seen j h' with h'' | h'' <;> omega
      · omega)
  have hd := defFields_two c c1 c2 _ _ W (Mark.ofInput false)
    (by rw [List.length_map, List.length_range]) (by rw [List.length_map, List.length_range]) d1 d2
  refine ⟨c2, check_fieldInput' sigs c c2 _ _ _ _ (by rw [List.length_map, List.length_map]) hd, ?_, ?_, ?_⟩
  · refine h.base.ofFields (b2.trans b1) (s2.trans s1) (p2.trans p1) (fun o ho j hj => ?_)
    have := fOf_id_lt p f o j ho hj
    rw [f2, if_neg (by omega), f1, if_neg (by omega)]
    exact h.base.cand o ho j hj
  · intro o ho j hj i hi
    rw [f2, f1]
    by_cases hjk : j = k
    · subst hjk
      have ho' : o = 0 ∨ o = 1 := by omega
      rcases ho' with rfl | rfl
      · have e : (coinH p f 0 j i).id = coinBase p f + j * W + i := by simp [coinH]
        rw [e, if_neg (by omega), if_pos (by omega)]
        rfl
      · have e : (coinH p f 1 j i).id = coinBase p f + p.bits * W + j * W + i := by simp [coinH]
        rw [e, if_pos (by omega)]
        rfl
    · have hfr := coin_frame p f o j k i ho (by omega) hk hi
      rw [if_neg (by omega), if_neg (by omega)]
      exact h.coins o ho j (by omega) i hi
  · intro id hid
    have e1 : (k + 1) * W = k * W + W := Nat.succ_mul k W
    rcases (n2 id).mp hid with h' | h'
    · rcases (n1 id).mp h' with h'' | h''
      · rcases h.seen id h'' with h3 | h3 <;> omega
      · omega
    · omega

theorem coin_inputs_wfp {α : Type} (sigs : Bytes → Option Sig) {Q : Ctx → α → Prop} {p : Params} {b f : Nat}
    (s : Slots) (π₁ π₂ : List Nat) (rest : Script α) (hrest : ∀ c, CoinCtx p b f c p.bits → WFP sigs Q c rest) :
    ∀ n, n ≤ p.bits → ∀ c, CoinCtx p b f c (p.bits - n) →
      WFP sigs Q c (seqs ((List.range' (p.bits - n) n).map fun j =>
        (.fieldInput ((List.range W).map (coinH p f 0 j)) ((List.range W).map (coinH p f 1 j)) .coins false
          (s.coins + member p π₁ π₂ j 0) : Instr)) rest)
  | 0, _, c, h => by
    simp only [List.range'_zero, List.map_nil, seqs_nil]
    exact hrest c (by simpa using h)
  | n + 1, hn, c, h => by
    have e : List.range' (p.bits - (n + 1)) (n + 1) = (p.bits - (n + 1)) :: List.range' (p.bits - n) n := by
      rw [List.range'_succ]
      congr 1
      congr 1
      omega
    rw [e, List.map_cons, seqs_cons]
    obtain ⟨c', hck, h'⟩ := coinStep_ctx sigs h (by omega) (s.coins + member p π₁ π₂ (p.bits - (n + 1)) 0)
    refine WFP_seq sigs c c' _ _ hck ?_
    have e2 : p.bits - (n + 1) + 1 = p.bits - n := by omega
    rw [e2] at h'
    exact coin_inputs_wfp sigs s π₁ π₂ rest hrest n (by omega) c' h'

theorem recIns_length (p : Params) (f : Nat) (π₁ π₂ : List Nat) : (recIns p f π₁ π₂).length = 2 * p.bits * 256 := by
  unfold recIns
  rw [length_flatMap_const _ (p.bits * 256) owners (fun o _ => by
    rw [length_flatMap_const _ 256 _ (fun j _ => by
      rw [List.length_append, List.length_map, List.length_range]
      rfl), List.length_range])]
  show 2 * (p.bits * 256) = 2 * p.bits * 256
  rw [Nat.mul_assoc]

theorem allCoins_length (p : Params) (f : Nat) : (allCoins p f).length = 2 * (p.bits * W) * 1 := by
  unfold allCoins
  rw [length_flatMap_const _ (p.bits * W) owners (fun o _ => by
    rw [length_flatMap_const _ W _ (fun j _ => by rw [List.length_map, List.length_range]), List.length_range])]
  show 2 * (p.bits * W) = 2 * (p.bits * W) * 1
  rw [Nat.mul_one]

theorem xorIns_length (p : Params) (f : Nat) : (xorIns p f).length = p.bits * W * 2 := by
  unfold xorIns
  rw [length_flatMap_const _ (W * 2) _ (fun j _ => by
    rw [length_flatMap_const _ 2 _ (fun i _ => rfl), List.length_range]), List.length_range, Nat.mul_assoc]

theorem pairSlices_eq (p : Params) (b : Nat) :
    pairSlices p b = (List.range' 0 (p.bits * W)).map fun q =>
      (.slice ⟨bitBase p b + q⟩ ⟨b + 10⟩ (256 * (q / W) + q % W) (256 * (q / W) + q % W + 1) : Instr) := by
  unfold pairSlices
  rw [← List.range_eq_range', ← flatMap_range_mul (fun q =>
    (.slice ⟨bitBase p b + q⟩ ⟨b + 10⟩ (256 * (q / W) + q % W) (256 * (q / W) + q % W + 1) : Instr)) W p.bits]
  apply flatMap_congr'
  intro j _
  apply List.map_congr_left
  intro i hi
  have hi' : i < 255 := List.mem_range.mp hi
  have h1 : (j * W + i) / W = j := by
    show (j * 255 + i) / 255 = j
    omega
  have h2 : (j * W + i) % W = i := by
    show (j * 255 + i) % 255 = i
    omega
  rw [h1, h2, Nat.add_assoc]

/-- Sizes the bit blocks need, from `Sizes`. -/
theorem Sizes.small {p : Params} (sz : Sizes p) :
    2 * p.bits ≤ maxWidth ∧ 2 * (p.bits * W) ≤ maxWidth ∧ p.bits * W ≤ maxWidth ∧ p.N ≤ maxWidth ∧
      p.N * 256 ≤ maxWidth := by
  have hb := sz.hbits
  have hN : p.bits * 510 ≤ p.N * 510 := Nat.mul_le_mul_right 510 hb
  have h3 : p.bits * W ≤ p.N * 510 :=
    Nat.le_trans (Nat.mul_le_mul_left p.bits (by decide : W ≤ 510)) hN
  have h2 : 2 * (p.bits * W) ≤ p.N * 510 := by
    have e : 2 * (p.bits * W) = p.bits * 510 := by
      show 2 * (p.bits * 255) = p.bits * 510
      rw [Nat.mul_comm 2, Nat.mul_assoc]
    rw [e]
    exact hN
  have h1 : 2 * p.bits ≤ p.N * 510 :=
    Nat.le_trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left p.bits (by decide : 2 ≤ 510)) hN
  have h4 : p.N ≤ p.N * 510 := Nat.le_mul_of_pos_right p.N (by decide)
  have h5 : p.N * 256 ≤ p.N * 510 := Nat.mul_le_mul_left p.N (by decide)
  exact ⟨Nat.le_trans h1 sz.final, Nat.le_trans h2 sz.final, Nat.le_trans h3 sz.final, Nat.le_trans h4 sz.final,
    Nat.le_trans h5 sz.final⟩

theorem bitPhase_wfp (sigs : Bytes → Option Sig) {p : Params} {b f : Nat} {c : Ctx} (h : BitCtx p b f c)
    (hfresh : ∀ j, coinBase p f ≤ j → j ∉ c.seenF) (sz : Sizes p) (s : Slots) (π₁ π₂ : List Nat)
    (hπ₁ : ∀ k ∈ π₁, k < p.M) :
    WFP sigs (fun _ _ => True) c (bitPhase p b f s π₁ π₂) := by
  have hml := member_lt p π₁ π₂ hπ₁ sz.hM
  obtain ⟨z1, z2, z3, z4, z5⟩ := sz.small
  have hbits := sz.hbits
  clear sz
  unfold bitPhase
  split
  · exact WFP.done _ _ trivial
  · next hb0 =>
    have key := coin_inputs_wfp sigs (Q := fun _ _ => True) (p := p) (b := b) (f := f) s π₁ π₂
      (seq (.program recomposeName (2 * p.bits) (recIns p f π₁ π₂) [] (recOuts p f) Label.bitBlockChecks) <|
        seq (.program bitCheckName (2 * (p.bits * W)) (allCoins p f) [] (chkOuts p f) Label.bitBlockChecks) <|
        openFieldThen (recOuts p f ++ chkOuts p f) Label.bitBlockChecks fun z =>
        if z.all (· == 0) then
          seq (.program bitXorName (p.bits * W) (xorIns p f) [] (xorOuts p f) Label.bitBlockChecks) <|
          seqs (pairSlices p b) (.done ())
        else .abort "bit block inconsistent with verified reference")
      (fun c6 h6 => ?_) p.bits (Nat.le_refl _) c
      ⟨h, fun o _ j hj => absurd hj (by omega), fun id hid => Or.inl (by
        apply Classical.byContradiction
        intro hc
        exact hfresh id (by omega) hid)⟩
    · unfold coinInputs
      rw [Nat.sub_self, ← List.range_eq_range'] at key
      exact key
    · have hcb := coinBase_ge p f
      have hseen : ∀ id, id ∈ c6.seenF → id < coinBase p f + 2 * (p.bits * W) := by
        intro id hid
        rcases h6.seen id hid with h' | h' <;> omega
      have hcoin : ∀ o, o < 2 → ∀ j, j < p.bits → ∀ i, i < W →
          (coinH p f o j i).id < coinBase p f + 2 * (p.bits * W) := by
        intro o ho j hj i hi
        have := coin_lt p o j i ho hj hi
        rw [coin_id]
        omega
      -- the recomposition
      obtain ⟨c7, d7, b7, s7, p7, f7, n7⟩ := defBlock c6
        (fun q => (⟨coinBase p f + 2 * (p.bits * W) + q⟩ : FieldH)) (coinBase p f + 2 * (p.bits * W)) (2 * p.bits)
        .pub (fun _ _ => rfl) (fun j hj1 _ hmem => by have := hseen j hmem; omega)
      refine WFP_seq sigs c6 c7 _ _ (check_program' sigs c6 c7 recomposeName (2 * p.bits) (recIns p f π₁ π₂)
        (recOuts p f) Label.bitBlockChecks ⟨256, 0, [.pub]⟩ (by decide) h6.base.progs.recompose rfl (by omega) z1
        (recIns_length p f π₁ π₂) (by
          rw [recOuts_block, List.length_map, List.length_range]
          show _ = 2 * p.bits * 1
          rw [Nat.mul_one]) (fun g hg => ?_) (by
          rw [recOuts_block]
          show c6.defFields _ (List.replicate (2 * p.bits) [Mark.pub]).flatten = some c7
          rw [flatten_replicate_singleton]
          exact d7)) ?_
      · simp only [recIns, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hg
        obtain ⟨o, ho, j, hj, hg | hg⟩ := hg
        · obtain ⟨i, hi, rfl⟩ := hg
          rw [h6.coins o (owners_lt ho) j hj i hi]
          rfl
        · subst hg
          exact h6.base.cand o (owners_lt ho) _ (hml j 0)
      -- the bit checks
      obtain ⟨c8, d8, b8, s8, p8, f8, n8⟩ := defBlock c7 (chkH p f)
        (coinBase p f + 2 * (p.bits * W) + 2 * p.bits) (2 * (p.bits * W)) .pub (fun _ _ => rfl)
        (fun j hj1 _ hmem => by
          rcases (n7 j).mp hmem with h' | h'
          · have := hseen j h'
            omega
          · omega)
      have hcoin7 : ∀ o, o < 2 → ∀ j, j < p.bits → ∀ i, i < W → c7.field? (coinH p f o j i) = some .never := by
        intro o ho j hj i hi
        have := hcoin o ho j hj i hi
        rw [f7, if_neg (by omega)]
        exact h6.coins o ho j hj i hi
      refine WFP_seq sigs c7 c8 _ _ (check_program' sigs c7 c8 bitCheckName (2 * (p.bits * W)) (allCoins p f)
        (chkOuts p f) Label.bitBlockChecks ⟨1, 0, [.pub]⟩ (by decide) (by rw [p7]; exact h6.base.progs.bitCheck) rfl
        (by have : 0 < p.bits * W := Nat.mul_pos (by omega) (by decide); omega) z2
        (allCoins_length p f) (by simp [chkOuts]) (fun g hg => ?_) (by
          show c7.defFields ((List.range (2 * (p.bits * W))).map (chkH p f))
            (List.replicate (2 * (p.bits * W)) [Mark.pub]).flatten = some c8
          rw [flatten_replicate_singleton]
          exact d8)) ?_
      · simp only [allCoins, List.mem_flatMap, List.mem_map, List.mem_range] at hg
        obtain ⟨o, ho, j, hj, i, hi, rfl⟩ := hg
        rw [hcoin7 o (owners_lt ho) j hj i hi]
        rfl
      -- the opening
      refine WFP_openFieldThen sigs c8 c8 _ _ _ _ (check_openField' sigs c8 _ _ (by decide) (fun x hx => ?_))
        (fun z _ => ?_)
      · rw [List.mem_append] at hx
        rcases hx with hx | hx
        · rw [recOuts_block] at hx
          simp only [List.mem_map, List.mem_range] at hx
          obtain ⟨q, hq, rfl⟩ := hx
          refine ⟨.pub, ?_, rfl⟩
          have e8 := f8 ⟨coinBase p f + 2 * (p.bits * W) + q⟩
          have e7 := f7 ⟨coinBase p f + 2 * (p.bits * W) + q⟩
          dsimp only at e8 e7
          rw [e8, if_neg (by omega), e7, if_pos (by omega)]
        · simp only [chkOuts, List.mem_map, List.mem_range] at hx
          obtain ⟨q, hq, rfl⟩ := hx
          refine ⟨.pub, ?_, rfl⟩
          have e8 := f8 (chkH p f q)
          have hid : (chkH p f q).id = coinBase p f + 2 * (p.bits * W) + 2 * p.bits + q := rfl
          rw [hid] at e8
          rw [e8, if_pos (by omega)]
      split
      · -- the XOR
        obtain ⟨c9, d9, b9, s9, p9, f9, n9⟩ := defBlock c8 (xorH p f)
          (coinBase p f + 4 * (p.bits * W) + 2 * p.bits) (p.bits * W) .never (fun _ _ => rfl)
          (fun j hj1 _ hmem => by
            rcases (n8 j).mp hmem with h' | h'
            · rcases (n7 j).mp h' with h'' | h''
              · have := hseen j h''
                omega
              · omega
            · omega)
        refine WFP_seq sigs c8 c9 _ _ (check_program' sigs c8 c9 bitXorName (p.bits * W) (xorIns p f)
          (xorOuts p f) Label.bitBlockChecks ⟨2, 0, [.never]⟩ (by decide)
          (by rw [p8, p7]; exact h6.base.progs.bitXor) rfl (Nat.mul_pos (by omega) (by decide)) z3
          (xorIns_length p f) (by simp [xorOuts]) (fun g hg => ?_) (by
            show c8.defFields ((List.range (p.bits * W)).map (xorH p f))
              (List.replicate (p.bits * W) [Mark.never]).flatten = some c9
            rw [flatten_replicate_singleton]
            exact d9)) ?_
        · simp only [xorIns, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hg
          obtain ⟨j, hj, i, hi, hg | hg⟩ := hg
          · subst hg
            have := hcoin 0 (by omega) j hj i hi
            rw [f8, if_neg (by omega), hcoin7 0 (by omega) j hj i hi]
            rfl
          · subst hg
            have := hcoin 1 (by omega) j hj i hi
            rw [f8, if_neg (by omega), hcoin7 1 (by omega) j hj i hi]
            rfl
        -- the slices
        have hb10 : c9.bool? ⟨b + 10⟩ = some ⟨FM p.N, false⟩ := by
          rw [bool?_congr (b9.trans (b8.trans b7))]
          exact h6.base.hb10
        have hfr9 : Fresh c9 (bitBase p b + 0) :=
          h6.base.fresh.of_seenB (s9.trans (s8.trans s7))
        obtain ⟨c10, e10, -⟩ := checkAll_slices sigs ⟨b + 10⟩ ⟨FM p.N, false⟩ rfl
          (fun q => 256 * (q / W) + q % W) (fun q => 256 * (q / W) + q % W + 1) (bitBase p b) (p.bits * W) 0 c9 hb10
          (by show b + 10 < bitBase p b + 0; unfold bitBase; omega) hfr9
          (fun q _ hq => by
            refine ⟨by omega, ?_, by rw [maxWidth_eq]; omega⟩
            show 256 * (q / W) + q % W + 1 ≤ (FM p.N).length
            rw [FM_length]
            have hq' : q < p.bits * 255 := by simpa using hq
            show 256 * (q / 255) + q % 255 + 1 ≤ p.N * 256
            omega)
        rw [pairSlices_eq]
        exact WFP_seqs sigs _ _ _ c10 e10 (WFP.done _ _ trivial)
      · exact WFP.abort _ _

/-! ## The finish phase -/

theorem Gen.mono {p : Params} {b f : Nat} {c : Ctx} {nb nf : Nat} (g : Gen p b f c nb nf) (nb' : Nat)
    (h : nb ≤ nb') : Gen p b f c nb' nf :=
  ⟨by have := g.hnb; omega, g.fresh.mono h, g.hb2, g.hb0, g.hb1, g.cand, g.freshF, g.progs⟩

theorem field?_congr {c c' : Ctx} (h : c'.fields = c.fields) (x : FieldH) : c'.field? x = c.field? x := by
  simp [Ctx.field?, h]

theorem isSome_push (c : Ctx) (n : Nat) (i : BoolInfo) (h : BoolH) (hs : (c.bool? h).isSome = true) :
    ((push c n i).bool? h).isSome = true := by
  rw [bool?_push]
  split
  · rfl
  · exact hs

theorem slice_hi (bits j N : Nat) (h : j < N - bits) : 256 * (bits + j) + 255 ≤ N * 256 := by
  have h1 : bits + j + 1 ≤ N := by omega
  have h2 := Nat.mul_le_mul_left 256 h1
  rw [Nat.mul_comm N 256]
  omega

/-- The five handles the mask block frees whatever the parameters. -/
def Live (b : Nat) (c : Ctx) : Prop :=
  ∀ h ∈ ([⟨b⟩, ⟨b + 1⟩, ⟨b + 2⟩, ⟨b + 6⟩, ⟨b + 7⟩] : List BoolH), (c.bool? h).isSome = true

theorem Live.push {b : Nat} {c : Ctx} (l : Live b c) (n : Nat) (i : BoolInfo) : Live b (push c n i) :=
  fun h hh => isSome_push c n i h (l h hh)

/-- From the concatenation of the finalize outputs to the end of `finishPhase`. -/
theorem finishTail_wfp (sigs : Bytes → Option Sig) {p : Params} {b f : Nat} {c : Ctx}
    (g : Gen p b f c (b + 10) (maskBase p f)) (sz : Sizes p) (s : Slots) (π₁ π₂ : List Nat)
    (hπ₁ : ∀ k ∈ π₁, k < p.M) (parts : List BoolH) (infos : List BoolInfo)
    (hu : c.useBools parts = some (infos, c)) (hmarks : (infos.map (·.marks)).flatten = FM p.N)
    (honce : infos.any (·.once) = false) (hlive : Live b c)
    (h8 : p.bits ≠ 0 → (c.bool? ⟨b + 8⟩).isSome = true) (h9 : p.words ≠ 0 → (c.bool? ⟨b + 9⟩).isSome = true) :
    WFP sigs (fun _ _ => True) c
      (seq (.concat ⟨b + 10⟩ parts) <|
        seq (.pick ⟨b + 11⟩ ⟨b + 10⟩ ((List.range p.N).map fun j => 256 * j + 255)) <|
        openThen ⟨b + 11⟩ Label.referenceFlags fun fl =>
          if fl.all id then
            seqs (maskBlock p b f π₁ π₂)
              ((bitPhase p b f s π₁ π₂).bind fun _ => .done (⟨maskList p b f, pairList p b f⟩ : MaskPool))
          else .abort "kept reference out of range") := by
  have hml := member_lt p π₁ π₂ hπ₁ sz.hM
  obtain ⟨z1, z2, z3, z4, z5⟩ := sz.small
  have hwords : p.words = p.N - p.bits := rfl
  have hmb : f + 2 * p.M ≤ maskBase p f := by unfold maskBase; omega
  -- the concatenation
  refine WFP_seq sigs c _ _ _ (check_concat sigs hu g.fresh (by rw [hmarks, FM_length]; exact z5)) ?_
  rw [hmarks, honce]
  have g1 := g.push' (b + 10) (Nat.le_refl _) ⟨FM p.N, false⟩
  -- the flags
  have hidx : ((List.range p.N).map fun j => 256 * j + 255).all (· < (FM p.N).length) = true := by
    rw [FM_length]
    simp only [List.all_eq_true, decide_eq_true_eq, List.mem_map, List.mem_range]
    rintro i ⟨j, hj, rfl⟩
    omega
  refine WFP_seq sigs _ _ _ _ (check_pick' sigs (useBool_keep (bool?_push_self _ _ _) rfl) hidx g1.fresh
    (by rw [List.length_map, List.length_range]; exact z4)) ?_
  have g2 := g1.push' (b + 11) (Nat.le_refl _)
    ⟨((List.range p.N).map fun j => 256 * j + 255).map (fun j => (FM p.N).getD j .never), false⟩
  refine WFP_openThen sigs _ _ ⟨b + 11⟩ _ _ _ (check_openBool sigs (by decide)
    (useBool_keep (bool?_push_self _ _ _) rfl) (by
      rw [List.all_eq_true]
      intro m hm
      simp only [List.mem_map, List.mem_range] at hm
      obtain ⟨i, ⟨j, hj, rfl⟩, rfl⟩ := hm
      rw [FM_flag p.N j hj]
      rfl)) (fun fl _ => ?_)
  split
  · rw [maskBlock, ← TlsMpc.Node.Flows.Contacts.seqs_append, ← TlsMpc.Node.Flows.Contacts.seqs_append]
    -- the slices
    obtain ⟨cs, e1, e2, e3, e4, e5, e6⟩ := checkAll_slices sigs ⟨b + 10⟩ ⟨FM p.N, false⟩ rfl
      (fun j => 256 * (p.bits + j)) (fun j => 256 * (p.bits + j) + W) (b + 12) p.words 0 _
      (by rw [bool?_push_of_ne _ _ _ _ (by show b + 10 ≠ b + 11; omega)]; exact bool?_push_self _ _ _)
      (by show b + 10 < b + 12 + 0; omega) (g2.fresh.mono (by omega))
      (fun j _ hj => by
        refine ⟨Nat.le_add_right _ _, ?_, by rw [Nat.add_sub_cancel_left]; decide⟩
        rw [FM_length]
        exact slice_hi p.bits j p.N (by omega))
    rw [← List.range_eq_range'] at e1
    refine WFP_seqs sigs _ _ _ cs e1 ?_
    -- the sums
    have had : (List.range p.words).map (fun j =>
        (.fieldAdd ⟨maskBase p f + j⟩ (fOf p f 0 (member p π₁ π₂ (p.bits + j) 0))
          (fOf p f 1 (member p π₁ π₂ (p.bits + j) 0)) : Instr)) =
        ((List.range p.words).map fun j => ((⟨maskBase p f + j⟩, fOf p f 0 (member p π₁ π₂ (p.bits + j) 0),
          fOf p f 1 (member p π₁ π₂ (p.bits + j) 0)) : FieldH × FieldH × FieldH)).map
          fun t => (.fieldAdd t.1 t.2.1 t.2.2 : Instr) := by
      rw [List.map_map]
      rfl
    have hcs : ∀ x : FieldH, cs.field? x = c.field? x := fun x => field?_congr e2 x
    have hseen : cs.seenF = c.seenF := e3
    obtain ⟨ca, a1, a2, a3, a4, a5, a6, a7⟩ := checkAll_adds sigs
      ((List.range p.words).map fun j => ((⟨maskBase p f + j⟩, fOf p f 0 (member p π₁ π₂ (p.bits + j) 0),
          fOf p f 1 (member p π₁ π₂ (p.bits + j) 0)) : FieldH × FieldH × FieldH)) cs
      (by
        rw [List.map_map]
        show ((List.range p.words).map fun j => maskBase p f + j).Nodup
        rw [map_range_add]
        exact List.nodup_range')
      (fun t ht => by
        simp only [List.mem_map, List.mem_range] at ht
        obtain ⟨j, -, rfl⟩ := ht
        rw [hseen]
        exact g.freshF _ (Nat.le_add_right _ _))
      (fun t ht => by
        simp only [List.mem_map, List.mem_range] at ht
        obtain ⟨j, -, rfl⟩ := ht
        rw [hcs, hcs]
        exact ⟨g.cand 0 (by omega) _ (hml _ _), g.cand 1 (by omega) _ (hml _ _)⟩)
      (fun t ht t' ht' => by
        simp only [List.mem_map, List.mem_range] at ht ht'
        obtain ⟨j, -, rfl⟩ := ht
        obtain ⟨j', -, rfl⟩ := ht'
        have h1 := fOf_id_lt p f 0 _ (by omega) (hml (p.bits + j') 0)
        have h2 := fOf_id_lt p f 1 _ (by omega) (hml (p.bits + j') 0)
        refine ⟨?_, ?_⟩ <;> dsimp only <;> omega)
    rw [had]
    refine WFP_seqs sigs _ _ _ ca a1 ?_
    -- the frees
    have hLmem : ∀ h ∈ ([⟨b⟩, ⟨b + 1⟩, ⟨b + 2⟩, ⟨b + 6⟩, ⟨b + 7⟩, ⟨b + 11⟩] ++
        (if p.bits = 0 then [] else [(⟨b + 8⟩ : BoolH)]) ++
        (if p.words = 0 then [] else [(⟨b + 9⟩ : BoolH)]) : List BoolH),
        h.id < b + 10 ∧ (c.bool? h).isSome = true ∨ h.id = b + 11 := by
      intro h hh
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with (hh | hh) | hh
      · rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl ⟨by show b < b + 10; omega, hlive _ (by simp)⟩
        · exact Or.inl ⟨by show b + 1 < b + 10; omega, hlive _ (by simp)⟩
        · exact Or.inl ⟨by show b + 2 < b + 10; omega, hlive _ (by simp)⟩
        · exact Or.inl ⟨by show b + 6 < b + 10; omega, hlive _ (by simp)⟩
        · exact Or.inl ⟨by show b + 7 < b + 10; omega, hlive _ (by simp)⟩
        · exact Or.inr rfl
      · by_cases hb0 : p.bits = 0
        · rw [if_pos hb0] at hh
          cases hh
        · rw [if_neg hb0] at hh
          simp only [List.mem_singleton] at hh
          subst hh
          exact Or.inl ⟨by show b + 8 < b + 10; omega, h8 hb0⟩
      · by_cases hw0 : p.words = 0
        · rw [if_pos hw0] at hh
          cases hh
        · rw [if_neg hw0] at hh
          simp only [List.mem_singleton] at hh
          subst hh
          exact Or.inl ⟨by show b + 9 < b + 10; omega, h9 hw0⟩
    have hca : ∀ x : BoolH, x.id < b + 12 → ca.bool? x =
        (push (push c (b + 10) ⟨FM p.N, false⟩) (b + 11)
          ⟨((List.range p.N).map fun j => 256 * j + 255).map (fun j => (FM p.N).getD j .never), false⟩).bool? x := by
      intro x hx
      rw [bool?_congr a2, e6 x (by omega)]
    refine frees_wfp' sigs _ _ ca ?_ (fun h hh => ?_) (fun c' k1 k2 k3 k4 k5 => ?_)
    · by_cases hb0 : p.bits = 0 <;> by_cases hw0 : p.words = 0 <;> simp [hb0, hw0] <;> omega
    · rcases hLmem h hh with ⟨n2, n3⟩ | n1
      · rw [hca h (by omega), bool?_push_of_ne _ _ _ _ (by omega), bool?_push_of_ne _ _ _ _ (by omega)]
        exact n3
      · have e : h = ⟨b + 11⟩ := by
          cases h
          simp only at n1
          rw [n1]
        rw [e, hca _ (by show b + 11 < b + 12; omega), bool?_push_self]
        rfl
    · have hbit : BitCtx p b f c' := by
        refine ⟨?_, ?_, fun o ho k hk => ?_, ?_⟩
        · have e : bitBase p b = b + 12 + 0 + p.words := by unfold bitBase; omega
          rw [e]
          exact (e5.of_seenB a3).of_seenB k2
        · rw [k1, if_neg (fun hmem => ?_), hca _ (by show b + 10 < b + 12; omega),
            bool?_push_of_ne _ _ _ _ (by show b + 10 ≠ b + 11; omega), bool?_push_self]
          simp only [List.mem_map] at hmem
          obtain ⟨h, hh, hid⟩ := hmem
          rcases hLmem h hh with ⟨n1, -⟩ | n1
          · omega
          · omega
        · rw [field?_congr k3, a5 _ (fun t ht e => ?_), hcs, g.cand o ho k hk]
          · rfl
          · simp only [List.mem_map, List.mem_range] at ht
            obtain ⟨j, -, rfl⟩ := ht
            have := fOf_id_lt p f o k ho hk
            have e' : maskBase p f + j = (fOf p f o k).id := e
            omega
        · exact ⟨by rw [k5, a4, e4]; exact g.progs.recompose, by rw [k5, a4, e4]; exact g.progs.bitCheck,
            by rw [k5, a4, e4]; exact g.progs.bitXor⟩
      have hfr : ∀ j, coinBase p f ≤ j → j ∉ c'.seenF := by
        intro j hj hmem
        rw [k4] at hmem
        rcases (a7 j).mp hmem with h1 | ⟨t, ht, rfl⟩
        · rw [hseen] at h1
          exact g.freshF j (by unfold coinBase at hj; omega) h1
        · simp only [List.mem_map, List.mem_range] at ht
          obtain ⟨j', hj', rfl⟩ := ht
          have : maskBase p f + p.words ≤ maskBase p f + j' := hj
          omega
      exact WFP.bind (bitPhase_wfp sigs hbit hfr sz s π₁ π₂ hπ₁) (fun _ _ _ => WFP.done _ _ trivial)
  · exact WFP.abort _ _

theorem optRun_wfp {α : Type} (sigs : Bytes → Option Sig) {Q : Ctx → α → Prop} (c : Ctx) (n copies : Nat)
    (name : Bytes) (inp : BoolH) (i : BoolInfo) (outMarks : List Mark) (rest : Script α)
    (hs : sigs name = some ⟨510, outMarks⟩) (hu : c.bool? inp = some i) (ho : i.once = false)
    (hl : i.marks.length = copies * 510) (hf : Fresh c n) (hcw : copies ≤ maxWidth)
    (hw : copies * outMarks.length ≤ maxWidth) (hk0 : copies = 0 → WFP sigs Q c rest)
    (hk1 : copies ≠ 0 → WFP sigs Q (push c n ⟨(List.replicate copies outMarks).flatten, false⟩) rest) :
    WFP sigs Q c (seqs (if copies = 0 then [] else [.run ⟨n⟩ name copies inp]) rest) := by
  by_cases h0 : copies = 0
  · rw [if_pos h0]
    exact hk0 h0
  · rw [if_neg h0]
    exact WFP_seq sigs c _ _ _ (check_run sigs hs (Nat.pos_of_ne_zero h0) (useBool_keep hu ho) hl hf hcw hw)
      (hk1 h0)

theorem refPairs_idx' (p : Params) (π₁ π₂ : List Nat) (hπ₁ : ∀ k ∈ π₁, k < p.M) (hM : 0 < p.M) (js : List Nat) :
    (js.flatMap (refPair p π₁ π₂)).all (· < (List.replicate (2 * (p.M * W)) Mark.revealable).length) = true := by
  have hml := member_lt p π₁ π₂ hπ₁ hM
  simp only [List.all_eq_true, decide_eq_true_eq, List.length_replicate, List.mem_flatMap, refPair,
    List.mem_append]
  rintro i ⟨j, -, hi | hi⟩
  · exact wordAt_idx p 0 _ (by omega) (hml j 0) i hi
  · exact wordAt_idx p 1 _ (by omega) (hml j 0) i hi

section Finish

variable (sigs : Bytes → Option Sig) {p : Params} {b f : Nat} {c : Ctx}

theorem finish_after_runs (g : Gen p b f c (b + 10) (maskBase p f)) (sz : Sizes p) (s : Slots)
    (π₁ π₂ : List Nat) (hπ₁ : ∀ k ∈ π₁, k < p.M) (hlive : Live b c)
    (h8 : p.bits ≠ 0 → c.bool? ⟨b + 8⟩ = some ⟨FM p.bits, false⟩)
    (h9 : p.words ≠ 0 → c.bool? ⟨b + 9⟩ = some ⟨FM p.words, false⟩) :
    WFP sigs (fun _ _ => True) c
      (seq (.concat ⟨b + 10⟩ ((if p.bits = 0 then [] else [⟨b + 8⟩]) ++ (if p.words = 0 then [] else [⟨b + 9⟩]))) <|
        seq (.pick ⟨b + 11⟩ ⟨b + 10⟩ ((List.range p.N).map fun j => 256 * j + 255)) <|
        openThen ⟨b + 11⟩ Label.referenceFlags fun fl =>
          if fl.all id then
            seqs (maskBlock p b f π₁ π₂)
              ((bitPhase p b f s π₁ π₂).bind fun _ => .done (⟨maskList p b f, pairList p b f⟩ : MaskPool))
          else .abort "kept reference out of range") := by
  have hNw : p.N = p.bits + p.words := by
    have := sz.hbits
    unfold Params.words
    omega
  have l8 : p.bits ≠ 0 → (c.bool? ⟨b + 8⟩).isSome = true := fun h => by rw [h8 h]; rfl
  have l9 : p.words ≠ 0 → (c.bool? ⟨b + 9⟩).isSome = true := fun h => by rw [h9 h]; rfl
  by_cases hb0 : p.bits = 0
  · by_cases hw0 : p.words = 0
    · rw [if_pos hb0, if_pos hw0]
      exact finishTail_wfp sigs g sz s π₁ π₂ hπ₁ [] [] (useBools_nil _)
        (by rw [show p.N = 0 by omega]; rfl) rfl hlive l8 l9
    · rw [if_pos hb0, if_neg hw0]
      exact finishTail_wfp sigs g sz s π₁ π₂ hπ₁ [⟨b + 9⟩] [⟨FM p.words, false⟩]
        (useBools_cons (useBool_keep (h9 hw0) rfl) (useBools_nil _))
        (by
          show FM p.words ++ [] = FM p.N
          rw [List.append_nil, show p.N = p.words by omega]) rfl hlive l8 l9
  · by_cases hw0 : p.words = 0
    · rw [if_neg hb0, if_pos hw0]
      exact finishTail_wfp sigs g sz s π₁ π₂ hπ₁ [⟨b + 8⟩] [⟨FM p.bits, false⟩]
        (useBools_cons (useBool_keep (h8 hb0) rfl) (useBools_nil _))
        (by
          show FM p.bits ++ [] = FM p.N
          rw [List.append_nil, show p.N = p.bits by omega]) rfl hlive l8 l9
    · rw [if_neg hb0, if_neg hw0]
      exact finishTail_wfp sigs g sz s π₁ π₂ hπ₁ [⟨b + 8⟩, ⟨b + 9⟩] [⟨FM p.bits, false⟩, ⟨FM p.words, false⟩]
        (useBools_cons (useBool_keep (h8 hb0) rfl) (useBools_cons (useBool_keep (h9 hw0) rfl) (useBools_nil _)))
        (by
          show FM p.bits ++ (FM p.words ++ []) = FM p.N
          rw [List.append_nil, FM_add, ← hNw]) rfl hlive l8 l9

theorem finish_after_bits (ws : WordSigs sigs) (g : Gen p b f c (b + 9) (maskBase p f)) (sz : Sizes p) (s : Slots)
    (π₁ π₂ : List Nat) (hπ₁ : ∀ k ∈ π₁, k < p.M) (i7 : BoolInfo) (hb7 : c.bool? ⟨b + 7⟩ = some i7)
    (ho7 : i7.once = false) (hl7 : i7.marks.length = p.words * 510) (hlive : Live b c)
    (h8 : p.bits ≠ 0 → c.bool? ⟨b + 8⟩ = some ⟨FM p.bits, false⟩) :
    WFP sigs (fun _ _ => True) c
      (seqs (if p.words = 0 then [] else [.run ⟨b + 9⟩ finalizeMaskName p.words ⟨b + 7⟩]) <|
        seq (.concat ⟨b + 10⟩ ((if p.bits = 0 then [] else [⟨b + 8⟩]) ++ (if p.words = 0 then [] else [⟨b + 9⟩]))) <|
        seq (.pick ⟨b + 11⟩ ⟨b + 10⟩ ((List.range p.N).map fun j => 256 * j + 255)) <|
        openThen ⟨b + 11⟩ Label.referenceFlags fun fl =>
          if fl.all id then
            seqs (maskBlock p b f π₁ π₂)
              ((bitPhase p b f s π₁ π₂).bind fun _ => .done (⟨maskList p b f, pairList p b f⟩ : MaskPool))
          else .abort "kept reference out of range") := by
  obtain ⟨z1, z2, z3, z4, z5⟩ := sz.small
  have hwN : p.words ≤ p.N := Nat.sub_le _ _
  refine optRun_wfp sigs c (b + 9) p.words finalizeMaskName ⟨b + 7⟩ i7 finalMarks _ ws.finalizeMask hb7 ho7 hl7
    g.fresh (Nat.le_trans hwN z4) (by rw [finalMarks_length]; exact Nat.le_trans (Nat.mul_le_mul_right 256 hwN) z5)
    (fun h0 => ?_) (fun h0 => ?_)
  · exact finish_after_runs sigs (g.mono (b + 10) (by omega)) sz s π₁ π₂ hπ₁ hlive h8 (fun h => absurd h0 h)
  · exact finish_after_runs sigs (g.push' (b + 9) (Nat.le_refl _) _) sz s π₁ π₂ hπ₁ (hlive.push _ _)
      (fun h => by rw [bool?_push_of_ne _ _ _ _ (by show b + 8 ≠ b + 9; omega)]; exact h8 h)
      (fun _ => bool?_push_self _ _ _)

theorem finishPhase_wfp (ws : WordSigs sigs) (g : Gen p b f c (b + 6) (maskBase p f)) (sz : Sizes p) (s : Slots)
    (π₁ π₂ : List Nat) (hπ₁ : ∀ k ∈ π₁, k < p.M) :
    WFP sigs (fun _ _ => True) c (finishPhase p b f s π₁ π₂) := by
  obtain ⟨z1, z2, z3, z4, z5⟩ := sz.small
  have hbits := sz.hbits
  have hfin := sz.final
  have hM := sz.hM
  have hlen : ∀ js : List Nat, (js.flatMap (refPair p π₁ π₂)).length = js.length * 510 := fun js =>
    length_flatMap_const _ 510 js (fun j _ => by
      unfold refPair
      rw [List.length_append, wordAt_length, wordAt_length]
      rfl)
  unfold finishPhase finalBlock
  rw [← TlsMpc.Node.Flows.Contacts.seqs_append, ← TlsMpc.Node.Flows.Contacts.seqs_append,
    ← TlsMpc.Node.Flows.Contacts.seqs_append]
  simp only [seqs_cons, seqs_nil]
  refine WFP_seq sigs c _ _ _ (check_pick' sigs (useBool_keep g.hb2 rfl) (refPairs_idx' p π₁ π₂ hπ₁ hM _) g.fresh
    (by rw [hlen, List.length_range]; exact Nat.le_trans (Nat.mul_le_mul_right 510 hbits) hfin)) ?_
  have g1 := g.push' (b + 6) (Nat.le_refl _)
    ⟨((List.range p.bits).flatMap (refPair p π₁ π₂)).map
      (fun j => (List.replicate (2 * (p.M * W)) Mark.revealable).getD j .never), false⟩
  refine WFP_seq sigs _ _ _ _ (check_pick' sigs (useBool_keep g1.hb2 rfl) (refPairs_idx' p π₁ π₂ hπ₁ hM _)
    g1.fresh (by
      rw [hlen, List.length_range']
      exact Nat.le_trans (Nat.mul_le_mul_right 510 (Nat.sub_le _ _)) hfin)) ?_
  have g2 := g1.push' (b + 7) (Nat.le_refl _)
    ⟨((List.range' p.bits p.words).flatMap (refPair p π₁ π₂)).map
      (fun j => (List.replicate (2 * (p.M * W)) Mark.revealable).getD j .never), false⟩
  have hlive : Live b (push (push c (b + 6)
      ⟨((List.range p.bits).flatMap (refPair p π₁ π₂)).map
        (fun j => (List.replicate (2 * (p.M * W)) Mark.revealable).getD j .never), false⟩) (b + 7)
      ⟨((List.range' p.bits p.words).flatMap (refPair p π₁ π₂)).map
        (fun j => (List.replicate (2 * (p.M * W)) Mark.revealable).getD j .never), false⟩) := by
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl
    · exact g2.hb0
    · exact g2.hb1
    · rw [g2.hb2]
      rfl
    · rw [bool?_push_of_ne _ _ _ _ (by show b + 6 ≠ b + 7; omega), bool?_push_self]
      rfl
    · rw [bool?_push_self]
      rfl
  refine optRun_wfp sigs _ (b + 8) p.bits finalizeBitsName ⟨b + 6⟩ _ finalMarks _ ws.finalizeBits
    (by rw [bool?_push_of_ne _ _ _ _ (by show b + 6 ≠ b + 7; omega)]; exact bool?_push_self _ _ _) rfl
    (by
      show (List.map _ _).length = _
      rw [List.length_map, hlen, List.length_range])
    g2.fresh (Nat.le_trans (Nat.le_mul_of_pos_left _ (by decide)) z1)
    (by rw [finalMarks_length]; exact Nat.le_trans (Nat.mul_le_mul_right 256 hbits) z5)
    (fun h0 => ?_) (fun h0 => ?_)
  · exact finish_after_bits sigs ws (g2.mono (b + 9) (by omega)) sz s π₁ π₂ hπ₁ _ (bool?_push_self _ _ _) rfl
      (by
        show (List.map _ _).length = _
        rw [List.length_map, hlen, List.length_range'])
      hlive (fun h => absurd h0 h)
  · exact finish_after_bits sigs ws (g2.push' (b + 8) (Nat.le_refl _) _) sz s π₁ π₂ hπ₁ _
      (by rw [bool?_push_of_ne _ _ _ _ (by show b + 7 ≠ b + 8; omega)]; exact bool?_push_self _ _ _) rfl
      (by
        show (List.map _ _).length = _
        rw [List.length_map, hlen, List.length_range'])
      (hlive.push _ _) (fun _ => bool?_push_self _ _ _)

end Finish

/-! ## The whole script -/

theorem challenge_wfp' (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (me : Party) (nonce value : Nat)
    (dom : Bytes) (n : Nat) (c : Ctx) :
    WFP sigs (fun c' π => c' = c ∧ PermSpec n π) c (Random.challenge hash me nonce value dom n) := by
  unfold Random.challenge
  refine WFP.bind (Random.joint_wfp sigs hash me nonce value c) (fun c' seed hc => ?_)
  unfold Random.finish
  split
  · next π hπ => exact WFP.done _ _ ⟨hc, Random.permOf_spec hash dom seed n π hπ⟩
  · exact WFP.abort _ _

theorem two_marks (n : Nat) :
    ([(⟨List.replicate n (Mark.ofInput true), false⟩ : BoolInfo),
      ⟨List.replicate n (Mark.ofInput true), false⟩].map (·.marks)).flatten =
      List.replicate (2 * n) Mark.revealable := by
  show List.replicate n Mark.revealable ++ (List.replicate n Mark.revealable ++ []) = _
  rw [List.append_nil, List.replicate_append_replicate, Nat.two_mul]

/-- **`generate` is well formed.** From any context in which no Boolean id from `b` and no field
id from `f` was ever defined, with the word circuits and field programs loaded and the bundles
within the width limit: every instruction of `generate`, on every branch, passes the shell's
`check`. -/
theorem generate_wf (sigs : Bytes → Option Sig) (ws : WordSigs sigs) (p : Params) (sz : Sizes p) (b f : Nat)
    (hash : Bytes → Bytes) (me : Party) (s : Slots) (c : Ctx) (hfb : Fresh c b)
    (hff : ∀ j, f ≤ j → j ∉ c.seenF) (hp : ProgSigs c) :
    WF sigs c (generate p b f hash me s) := by
  have hbun := sz.bundle
  have hMW : p.M * W ≤ maxWidth := Nat.le_trans (Nat.le_mul_of_pos_left _ (by decide)) hbun
  suffices h : WFP sigs (fun _ _ => True) c (generate p b f hash me s) from h.wf
  unfold generate inputBlock
  simp only [seqs_cons, seqs_nil]
  -- the Boolean inputs
  refine WFP_seq sigs c _ _ _ (check_boolInputBoth sigs hfb (p.M * W) false true hMW) ?_
  have f1 : Fresh (push (push c b ⟨List.replicate (p.M * W) (Mark.ofInput true), false⟩) (b + 1)
      ⟨List.replicate (p.M * W) (Mark.ofInput true), false⟩) (b + 2) :=
    (hfb.push b (Nat.le_refl _) _).push (b + 1) (Nat.le_refl _) _
  refine WFP_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep (by
        rw [bool?_push_of_ne _ _ _ _ (by show b ≠ b + 1; omega)]
        exact bool?_push_self _ _ _) rfl)
      (useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl) (useBools_nil _)))
    f1 (by rw [two_marks, List.length_replicate]; exact hbun)) ?_
  rw [two_marks]
  -- the field inputs
  obtain ⟨c3, d1, b1, s1, p1, e1, n1⟩ := defBlock
    (push (push (push c b ⟨List.replicate (p.M * W) (Mark.ofInput true), false⟩) (b + 1)
      ⟨List.replicate (p.M * W) (Mark.ofInput true), false⟩) (b + 2)
      ⟨List.replicate (2 * (p.M * W)) Mark.revealable,
        [(⟨List.replicate (p.M * W) (Mark.ofInput true), false⟩ : BoolInfo),
          ⟨List.replicate (p.M * W) (Mark.ofInput true), false⟩].any (·.once)⟩)
    (fOf p f 0) f p.M (Mark.ofInput true) (fun i _ => by simp [fOf])
    (fun j hj _ => hff j hj)
  obtain ⟨c4, d2, b2, s2, p2, e2, n2⟩ := defBlock c3 (fOf p f 1) (f + p.M) p.M (Mark.ofInput true)
    (fun i _ => by simp [fOf])
    (fun j hj1 _ hmem => by
      rcases (n1 j).mp hmem with h' | h'
      · exact hff j (by omega) h'
      · omega)
  refine WFP_seq sigs _ c4 _ _ (check_fieldInput' sigs _ c4 _ _ _ _ (by rw [List.length_map, List.length_map])
    (defFields_two _ c3 c4 _ _ p.M _ (by rw [List.length_map, List.length_range])
      (by rw [List.length_map, List.length_range]) d1 d2)) ?_
  have gen : Gen p b f c4 (b + 3) (f + 2 * p.M) := by
    refine ⟨Nat.le_refl _, ?_, ?_, ?_, ?_, fun o ho k hk => ?_, fun j hj hmem => ?_, ?_⟩
    · exact ((f1.push (b + 2) (Nat.le_refl _) _).of_seenB s1).of_seenB s2
    · rw [bool?_congr (b2.trans b1), bool?_push_self]
      rfl
    · rw [bool?_congr (b2.trans b1), bool?_push_of_ne _ _ _ _ (by show b ≠ b + 2; omega),
        bool?_push_of_ne _ _ _ _ (by show b ≠ b + 1; omega), bool?_push_self]
      rfl
    · rw [bool?_congr (b2.trans b1), bool?_push_of_ne _ _ _ _ (by show b + 1 ≠ b + 2; omega), bool?_push_self]
      rfl
    · have ho' : o = 0 ∨ o = 1 := by omega
      rcases ho' with rfl | rfl
      · have e : (fOf p f 0 k).id = f + k := by simp [fOf]
        rw [e2, e, if_neg (by omega), e1, e, if_pos (by omega)]
        rfl
      · have e : (fOf p f 1 k).id = f + p.M + k := by simp [fOf]
        rw [e2, e, if_pos (by omega)]
        rfl
    · rcases (n2 j).mp hmem with h' | h'
      · rcases (n1 j).mp h' with h'' | h''
        · exact hff j (by omega) h''
        · omega
      · omega
    · exact ⟨by rw [p2, p1]; exact hp.recompose, by rw [p2, p1]; exact hp.bitCheck,
        by rw [p2, p1]; exact hp.bitXor⟩
  -- the challenges and the phases
  refine WFP.bind (challenge_wfp' sigs hash me _ _ _ _ c4) (fun c' π₁ h1 => ?_)
  obtain ⟨rfl, hs1⟩ := h1
  have hcl : (cutOf p π₁).length ≤ p.M :=
    Nat.le_trans (List.length_take_le _ _) (by show p.K ≤ 2 * p.K; omega)
  refine WFP.bind (cutPhase_wfp sigs gen sz π₁ (fun k hk => hs1.2.2 k (List.mem_of_mem_take hk)) hcl)
    (fun c5 _ g5 => ?_)
  refine WFP.bind (challenge_wfp' sigs hash me _ _ _ _ c5) (fun c' π₂ h2 => ?_)
  obtain ⟨rfl, -⟩ := h2
  refine WFP.bind (bucketPhase_wfp sigs ws g5 sz π₁ π₂ hs1.2.2) (fun c6 _ g6 => ?_)
  exact finishPhase_wfp sigs ws g6 sz s π₁ π₂ hs1.2.2

theorem sizes_of (N B bits : Nat) (hle : bits ≤ N) (h1 : 0 < 2 * (B * N)) (h2 : 0 < 2 * (N * (B - 1)))
    (h3 : 2 * (2 * (B * N) * 255) ≤ 67108864) (h4 : 2 * (N * (B - 1)) * 510 ≤ 67108864)
    (h5 : N * 510 ≤ 67108864) : Sizes ⟨N, B, bits⟩ :=
  ⟨h1, h2, hle, by rw [maxWidth_eq]; exact h3, by rw [maxWidth_eq]; exact h4, by rw [maxWidth_eq]; exact h5⟩

/-- **The deployed profiles are within the shell's limits.** -/
theorem profile_sizes (N bits : Nat) (p : Params) (h : profile N bits = some p) : Sizes p := by
  unfold profile at h
  split at h
  · next B hB =>
    split at h
    · next hle =>
      simp only [Option.some.injEq] at h
      subst h
      unfold bucketFor at hB
      split at hB <;> first
        | (cases hB
           exact sizes_of _ _ _ hle (by decide) (by decide) (by decide) (by decide) (by decide))
        | cases hB
    · cases h
  · cases h

/-- **`generate` is well formed for every deployed profile** (in an environment that loads the word
circuits and the three field programs). -/
theorem generate_wf_profile (sigs : Bytes → Option Sig) (ws : WordSigs sigs) (N bits : Nat) (p : Params)
    (hprof : profile N bits = some p) (b f : Nat) (hash : Bytes → Bytes) (me : Party) (s : Slots) (c : Ctx)
    (hfb : Fresh c b) (hff : ∀ j, f ≤ j → j ∉ c.seenF) (hp : ProgSigs c) :
    WF sigs c (generate p b f hash me s) :=
  generate_wf sigs ws p (profile_sizes N bits p hprof) b f hash me s c hfb hff hp

end TlsMpc.Node.Flows.Masks
