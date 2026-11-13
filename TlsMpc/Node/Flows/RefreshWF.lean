import TlsMpc.Node.Flows.RefreshFlowProofs

/-!
# `Refresh.*`: well-formedness and the refresh state's invariant

REORGANIZATION_PLAN.md stage S15 (`_wf`, the state's invariant like `Table.Inv`). No I/O; no
emitter imports this module.

  * `shapeScript_wfp`, `takeScript_wfp` (each with the post-condition: the handles below the block
    are as before, the counter fresh past the block); `opDrop_wfp`.
  * `RState.Inv c t st`: the refresh state's handles are distinct, below the table's counter, live,
    and none is a contact table handle; the sealed content has the marks of a state of its size
    and valid kinds. `RState.Inv.empty`. `opDrop_inv`: a drop is well formed and leaves the table
    invariant and the empty refresh state's invariant (ORD-2: the table's entries are as before,
    `opDrop_table`).

Not here (S15_NOTES.md, gaps): WF of `fetchScript`, the establishment steps (S11's parameters'
own WF is a hypothesis S11 must supply), `scratchSealScript`, and `opCommit`'s preservation of
`Table.Inv` (stated, `opCommit` changes only the entry, `opCommit_entry`; the invariant's proof
follows `opOpen_inv`'s pattern and is open).
-/

namespace TlsMpc.Node.Flows.Refresh

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts

/-- What a block of ids from `n` leaves: the handles below `n` as before, the counter fresh from `n + k`. -/
def BlockPost {α : Type} (c : Ctx) (n k : Nat) (c' : Ctx) (_ : α) : Prop :=
  (∀ g : BoolH, g.id < n → c'.bool? g = c.bool? g) ∧ Fresh c' (n + k)

/-- **The shape script is well formed** (the circuit's signature: the padded body in, one public
flag byte per byte out). -/
theorem shapeScript_wfp (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (body : BoolH) (size : Nat)
    (bm : List Mark) (hf : Fresh c n) (hbn : body.id < n) (hb : c.bool? body = some ⟨bm, false⟩)
    (hbm : bm.length = 8 * size) (hcap : size ≤ shapeCapacity size) (hw : 8 * shapeCapacity size ≤ maxWidth)
    (hsig : sigs (shapeName (shapeCapacity size)) =
      some ⟨8 * shapeCapacity size, List.replicate (8 * shapeCapacity size) .pub⟩) :
    WFP sigs (BlockPost c n 3) c (shapeScript n body size) := by
  unfold shapeScript
  simp only [seqs_cons, seqs_nil]
  generalize hC : shapeCapacity size = cap at hcap hw hsig
  have hwM := maxWidth_eq
  refine WFP_seq sigs c _ _ _ (check_boolPublic sigs hf _ (by simp; omega)) ?_
  have hf1 := hf.push n (Nat.le_refl n) ⟨List.replicate (List.replicate (8 * (cap - size)) false).length .pub, false⟩
  refine WFP_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ (by omega)).trans hb) rfl)
      (useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl) (useBools_nil _))) hf1
    (by simp [hbm]; omega)) ?_
  have hf2 := hf1.push (n + 1) (Nat.le_refl _) ⟨(List.map BoolInfo.marks [⟨bm, false⟩,
    ⟨List.replicate (List.replicate (8 * (cap - size)) false).length .pub, false⟩]).flatten, false⟩
  refine WFP_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_keep (bool?_push_self _ _ _) rfl)
    (by simp [hbm]; omega) hf2 (by decide) (by simp; omega)) ?_
  have hf3 := hf2.push (n + 2) (Nat.le_refl _) ⟨(List.replicate 1 (List.replicate (8 * cap) Mark.pub)).flatten, false⟩
  refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push])) ?_
  refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop])) ?_
  refine WFP_openThen sigs _ _ _ _ _ _ (check_openBool sigs (by decide)
    (useBool_keep ((bool?_drop_of_ne _ _ _ (by simp)).trans ((bool?_drop_of_ne _ _ _ (by simp)).trans
      (bool?_push_self _ _ _))) rfl)
    (by simp [Mark.openable])) ?_
  intro b _
  refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop])) ?_
  refine WFP.done _ _ ⟨fun g hg => ?_, ((hf3.drop n).drop (n + 1)).drop (n + 2)⟩
  have e0 : g.id ≠ n := by omega
  have e1 : g.id ≠ n + 1 := by omega
  have e2 : g.id ≠ n + 2 := by omega
  simp only [bool?_push, bool?_drop, e0, e1, e2, if_false]

/-- **The take script is well formed.** -/
theorem takeScript_wfp (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (body : Option BoolH) (content : BoolH)
    (offset count : Nat) (cm bm : List Mark) (hf : Fresh c n) (hcn : content.id < n)
    (hc : c.bool? content = some ⟨cm, false⟩) (hcm : 8 * (offset + count) ≤ cm.length)
    (hbody : ∀ b, body = some b → b.id < n ∧ b.id ≠ content.id ∧ c.bool? b = some ⟨bm, false⟩)
    (hw : bm.length + 8 * count ≤ maxWidth) (hw' : 8 * count ≤ maxWidth) :
    WFP sigs (fun c' (_ : BoolH) => (∀ g : BoolH, g.id < n → (∀ b, body = some b → g.id ≠ b.id) →
      c'.bool? g = c.bool? g) ∧ Fresh c' (n + 2)) c (takeScript n body content offset count) := by
  unfold takeScript
  cases body with
  | none =>
    simp only [seqs_cons, seqs_nil]
    refine WFP_seq sigs c _ _ _ (check_slice sigs (useBool_keep hc rfl) ⟨by omega, hcm⟩ hf (by omega)) ?_
    refine WFP.done _ _ ⟨fun g hg _ => ?_, (hf.push n (Nat.le_refl n) _).mono (by omega)⟩
    rw [bool?_push_of_ne _ _ _ _ (by omega)]
  | some b =>
    obtain ⟨hbn, hbc, hb⟩ := hbody b rfl
    simp only [seqs_cons, seqs_nil]
    refine WFP_seq sigs c _ _ _ (check_slice sigs (useBool_keep hc rfl) ⟨by omega, hcm⟩ hf (by omega)) ?_
    have hf1 := hf.push n (Nat.le_refl n) ⟨(cm.drop (8 * offset)).take (8 * (offset + count) - 8 * offset), false⟩
    refine WFP_seq sigs _ _ _ _ (check_concat sigs
      (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ (by omega)).trans hb) rfl)
        (useBools_cons (useBool_keep (bool?_push_self _ _ _) rfl) (useBools_nil _))) hf1
      (by simp; omega)) ?_
    have hf2 := hf1.push (n + 1) (Nat.le_refl _) ⟨(List.map BoolInfo.marks [⟨bm, false⟩,
      ⟨(cm.drop (8 * offset)).take (8 * (offset + count) - 8 * offset), false⟩]).flatten, false⟩
    refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, hb, show b.id ≠ n + 1 by omega,
      show b.id ≠ n by omega])) ?_
    refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by simp [bool?_push, bool?_drop, show n ≠ b.id by omega])) ?_
    refine WFP.done _ _ ⟨fun g hg hne => ?_, (hf2.drop b.id).drop n⟩
    have e0 : g.id ≠ n := by omega
    have e1 : g.id ≠ n + 1 := by omega
    have e2 : g.id ≠ b.id := hne b rfl
    simp only [bool?_push, bool?_drop, e0, e1, e2, if_false]

/-! ## The refresh state's invariant -/

/-- **The refresh state's invariant** in the shell's context `c`, beside the contact table `t`. -/
structure RState.Inv (c : Ctx) (t : Contacts.Table) (st : RState) : Prop where
  nodup : (st.handles.map (·.id)).Nodup
  below : ∀ h ∈ st.handles, h.id < t.next
  live : ∀ h ∈ st.handles, (c.bool? h).isSome = true
  sep : ∀ h ∈ st.handles, ∀ p ∈ t.entries, ∀ g ∈ p.2.handles, g.id ≠ h.id
  sealed : ∀ content size kinds, st.sealed = some (content, size, kinds) →
    c.bool? content = some ⟨List.replicate (8 * size) .never, false⟩ ∧ kindsOk kinds size

theorem handles_empty : (({} : RState)).handles = [] := rfl

theorem RState.Inv.empty (c : Ctx) (t : Contacts.Table) : RState.Inv c t {} where
  nodup := by simp [handles_empty]
  below := by simp [handles_empty]
  live := by simp [handles_empty]
  sep := by simp [handles_empty]
  sealed := by intro _ _ _ h; cases h

/-- **A drop is well formed and keeps the table's invariant** (its entries untouched: ORD-2's
"dropped scratch leaves the table unchanged", `opDrop_table`), and the refresh state is empty. -/
theorem opDrop_inv (sigs : Bytes → Option Sig) (c : Ctx) (t : Contacts.Table) (st : RState)
    (hT : t.Inv c) (hR : st.Inv c t) :
    WFP sigs (fun c' r => ((opDrop t st).commit r).1.Inv c' ∧ ((opDrop t st).commit r).2.Inv c' t) c
      (opDrop t st).script := by
  refine frees_wfp sigs _ st.handles c hR.nodup hR.live (fun c1 h1 h2 => WFP.done _ _ ⟨?_, RState.Inv.empty c1 t⟩)
  refine Table.Inv.keep hT rfl (Nat.le_refl _) (hT.fresh.of_seenB h2) (fun p hp g hg => ?_)
  exact bool?_after_frees h1 (fun h hh => hR.sep h hh p hp g hg)

end TlsMpc.Node.Flows.Refresh
