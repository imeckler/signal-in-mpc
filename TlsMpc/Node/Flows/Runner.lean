import Std.Data.HashMap
import TlsMpc.Node.Flows.Legacy
import TlsMpc.Node.Flows.JoinBackend
import TlsMpc.Node.Flows.ReceiveBackend

/-!
# The controller-side script runner (REORGANIZATION_PLAN.md S9 "what remains": `runIO`)

The one place the script flows reach the worker: a `Script α` (Engine.lean) is run batch by batch
as pipe operation 93 (`TlsWorker.Operation.batch`, node_worker `interp.rs`):

    nextBatch (fill from this party's store) → encodeBatch → op 93 → decodeReplies → resume → …

until the script returns (its result) or aborts (an error: the session is aborted, as for any
failed worker operation). Like `Flows/Legacy.lean` it calls the pipe through `Legacy.call`, so
op 93 is recorded among the operations used and no connection is selected for it (batches are not
tied to a connection: handles are the session's).

## The pure core (proved)

`drive hash me fuel s σ items` is the runner as a function: from a script, this party's store and
the reply items the worker returned (in order), the batches sent, the result and the final store.
The IO loop (`Runner.run`) computes exactly its steps, batch by batch: `nextBatch` on the store,
`resume` on the batch's items (checked to be `itemCount` of them).

  * **`drive_model`: the controller sends exactly the batches the model says.** For any
    adversary, store, engine state: if the honest party's model run (`Engine/Model.lean`
    `withAdv`) returns `a`, then the runner fed the model's view (`viewH`, the released values)
    sends batches whose instructions are, in order, exactly the model run's trace, and returns
    `a` with the model's final store. (With T12 `trace_eq_skeletons`: the skeletons of the script
    along the replies the model gave it; with `honest_replay`: nothing but the view reaches it.)
  * `drive_bounded`: every wire of every batch is `Wire.Bounded` when the script's instructions
    are (`Every Instr.Bounded`, Flows/Registry.lean per flow): so `decodeBatch_encodeBatch`
    applies and the peer decodes exactly what was sent.
  * `nextBatch_fill_only`: the batches depend on the store only through `fill` (two stores that
    fill every instruction alike give the same batch); `resume` reads it only in `absorb`
    (an exchange's own payload, which `fill` computed the same way, and the write of an
    `openBoolTo`'s bits). The store's other reader is `takeBits`, which returns a `Secret`.

## The runner record (IO glue, unverified like the backends it serves)

`Runner` holds the session's ONE public script state (`Receive.St`: the contact table, whose
`Table.ctr` are the session's ONE `Counters`; the S10 mask pool; the J1 slot supply), this party's
private store (`Slots`, written only through `Secret.stash`, the eliminator next to
`Secret.inputOwn`), the store-slot counter and this party's randomness (`Channels.random`, rule 5).
Every runner interface the backends take is a view of it:

  * `tls` (S12/S13 `TlsBackend.Runner`): `run`, `allocB` (the table's counters), `stashBits`,
    `stashBytes`, `slot`, `take`, `random`;
  * `field` (the `JoinBackend.FieldRunner` adapter, J2): `allocF` (the same counters), `stashElems`,
    `takeWord` (the same pool, each mask handed out once);
  * `receive` (S14 `ReceiveBackend.Runner`): the same state reference, stashes, `loaded`,
    `programMasks`; per-call agreement slots are the J1 supply (`ReceiveBackend.supplyOf`, fresh
    slots per operation);
  * S15 (`Flows/RefreshBackend.lean`): `allocB`/`allocF` blocks for `allocBoth`, the table, the
    pool and the supply per call (`Join.RefreshCurve`).

No I/O primitive (only `IO.Ref`); no emitter imports this module.
-/

namespace TlsMpc.Node.Flows.Runner

open TlsMpc.Node.Engine
open TlsMpc.TlsClient (M insist)
open TlsMpc.FieldDag (F)

/-! ## The pure core -/

/-- The reply items a batch gets: one per instruction that releases to `me` (design note item 6). -/
def itemCount (me : Party) (ws : List Wire) : Nat := (ws.filter fun w => w.releasesTo me).length

/-- The release a batch's last instruction gets from the batch's reply items: the last item. -/
def lastRelease (i : Instr) (items : List Datum) : Option Release :=
  items.getLast?.map fun d => ⟨i.label?.getD ⟨0⟩, d⟩

/-- **What the batch's last instruction gives the script**: its reply and the store after it
(`absorb`). The items before the last are the batch's program openings, which the script does not
read (design note item 6). -/
def resume (hash : Bytes → Bytes) (me : Party) (i : Instr) (σ : Store) (items : List Datum) : Reply × Store :=
  absorb hash me i σ (if i.releasesTo me then lastRelease i items else none)

/-- **The runner's pure core**: the batches sent, the result and the final store, from the script,
this party's store and the reply items (in order); at most `fuel` batches. -/
def drive (hash : Bytes → Bytes) (me : Party) {α : Type} :
    Nat → Script α → Store → List Datum → List (List Wire) × Option α × Store
  | 0, _, σ, _ => ([], none, σ)
  | fuel + 1, s, σ, ds =>
    match nextBatch hash me σ s with
    | ⟨_, .aborted _⟩ => ([], none, σ)
    | ⟨ws, .finished a⟩ => (if ws.isEmpty then [] else [ws], some a, σ)
    | ⟨ws, .waiting i k⟩ =>
      if ds.length < itemCount me ws then ([ws], none, σ) else
      let r := resume hash me i σ (ds.take (itemCount me ws))
      let o := drive hash me fuel (k r.1) r.2 (ds.drop (itemCount me ws))
      (ws :: o.1, o.2.1, o.2.2)

section Core

variable (hash : Bytes → Bytes) (me : Party)

theorem absorb_label (i : Instr) (σ : Store) (l l' : Label) (d : Datum) :
    absorb hash me i σ (some ⟨l, d⟩) = absorb hash me i σ (some ⟨l', d⟩) := by
  cases i <;> cases d <;> rfl

theorem absorb_notEnds (i : Instr) (σ : Store) (t : Option Release) (h : i.endsBatch = false) :
    absorb hash me i σ t = (.unit, σ) := by
  cases i <;> simp only [InstrP.endsBatch, reduceCtorEq] at h <;>
    (rcases t with _ | ⟨l, d⟩ <;> (try cases d) <;> rfl)

theorem resume_eq (i : Instr) (σ : Store) (pre : List Release) (toI : Option Release)
    (h : toI.isSome = i.releasesTo me) :
    resume hash me i σ ((pre ++ toI.toList).map (·.datum)) = absorb hash me i σ toI := by
  unfold resume
  cases toI with
  | none =>
    have : i.releasesTo me = false := by rw [← h]; rfl
    simp [this]
  | some x =>
    have : i.releasesTo me = true := by rw [← h]; rfl
    simp only [this, if_true, lastRelease, Option.toList_some, List.map_append, List.map_cons, List.map_nil,
      List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some]
    exact absorb_label hash me i σ _ x.label x.datum

theorem itemCount_cons (w : Wire) (ws : List Wire) :
    itemCount me (w :: ws) = (if w.releasesTo me then 1 else 0) + itemCount me ws := by
  unfold itemCount
  cases h : w.releasesTo me <;> simp [List.filter_cons, h] <;> omega

theorem nextBatch_waiting_ne {α : Type} (σ : Store) (s : Script α) :
    ∀ ws i k, nextBatch hash me σ s = ⟨ws, .waiting i k⟩ → ws ≠ [] := by
  induction s with
  | done a => intro ws i k h; simp [nextBatch] at h
  | abort r => intro ws i k h; simp [nextBatch] at h
  | step i₀ k₀ ih =>
    intro ws i k h
    rcases hf : fill hash me σ i₀ with _ | w
    · simp [nextBatch, hf] at h
    · by_cases he : i₀.endsBatch = true
      · simp only [nextBatch, hf, he, if_true, Batch.mk.injEq] at h
        rw [← h.1]; simp
      · have he' : i₀.endsBatch = false := by simpa using he
        rcases hn : nextBatch hash me σ (k₀ .unit) with ⟨ws', rest⟩
        cases rest with
        | aborted r => simp [nextBatch, hf, he', hn] at h
        | finished a =>
          simp only [nextBatch, hf, he', hn, Bool.false_eq_true, if_false, Batch.mk.injEq] at h
          rw [← h.1]; simp
        | waiting i' k' =>
          simp only [nextBatch, hf, he', hn, Bool.false_eq_true, if_false, Batch.mk.injEq] at h
          rw [← h.1]; simp

/-- **The batches depend on the store only through `fill`.** -/
theorem nextBatch_fill_only {α : Type} (σ₁ σ₂ : Store) (h : ∀ i, fill hash me σ₁ i = fill hash me σ₂ i)
    (s : Script α) : nextBatch hash me σ₁ s = nextBatch hash me σ₂ s := by
  induction s with
  | done a => rfl
  | abort r => rfl
  | step i k ih => simp only [nextBatch, h i, ih .unit]

theorem nextBatch_every {P : Instr → Prop} {α : Type} (σ : Store) {s : Script α} (hs : Every P s) :
    ∀ ws i k, nextBatch hash me σ s = ⟨ws, .waiting i k⟩ → ∀ r, Every P (k r) := by
  induction hs with
  | done a => intro ws i k h; simp [nextBatch] at h
  | abort r => intro ws i k h; simp [nextBatch] at h
  | step i₀ k₀ _ hk ih =>
    intro ws i k h
    rcases hf : fill hash me σ i₀ with _ | w
    · simp [nextBatch, hf] at h
    · by_cases he : i₀.endsBatch = true
      · simp only [nextBatch, hf, he, if_true, Batch.mk.injEq, Pending.waiting.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        exact hk
      · have he' : i₀.endsBatch = false := by simpa using he
        rcases hn : nextBatch hash me σ (k₀ .unit) with ⟨ws', rest⟩
        cases rest with
        | aborted r => simp [nextBatch, hf, he', hn] at h
        | finished a => simp [nextBatch, hf, he', hn] at h
        | waiting i' k' =>
          simp only [nextBatch, hf, he', hn, Bool.false_eq_true, if_false, Batch.mk.injEq, Pending.waiting.injEq] at h
          obtain ⟨-, -, rfl⟩ := h
          exact ih .unit ws' i' k' hn

/-- **The runner sends only bounded wires** (so every batch round-trips through the encoding),
for a script whose instructions are bounded on every branch. -/
theorem drive_bounded {α : Type} : ∀ (fuel : Nat) (s : Script α) (σ : Store) (ds : List Datum),
    Every Instr.Bounded s → ∀ b ∈ (drive hash me fuel s σ ds).1, ∀ w ∈ b, w.Bounded
  | 0, _, _, _, _ => by simp [drive]
  | fuel + 1, s, σ, ds, hs => by
    have hb := nextBatch_bounded hash me σ s hs
    rcases hn : nextBatch hash me σ s with ⟨ws, rest⟩
    rw [hn] at hb
    cases rest with
    | aborted r => simp [drive, hn]
    | finished a =>
      simp only [drive, hn]
      intro b hbm w hw
      split at hbm
      · simp at hbm
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbm
        subst hbm
        exact hb w hw
    | waiting i k =>
      simp only [drive, hn]
      intro b hbm w hw
      split at hbm
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbm
        subst hbm
        exact hb w hw
      · simp only [List.mem_cons] at hbm
        rcases hbm with rfl | hbm
        · exact hb w hw
        · exact drive_bounded fuel _ _ _ (nextBatch_every hash me σ hs ws i k hn _) b hbm w hw

end Core

section Model

variable (E : Env) (me : Party) (adv : Adversary)

/-- The model run after a batch: the continuation with the last instruction's reply. -/
def after {α : Type} (i : Instr) (k : Reply → Script α) (σ : Store) (toI : Option Release) (I : Ideal)
    (vD : List Release) : Outcome α :=
  withAdv E me adv (k (absorb E.hash me i σ toI).1) (absorb E.hash me i σ toI).2 I vD

theorem releasesTo_fill (σ : Store) (i : Instr) (w : Wire) (h : fill E.hash me σ i = some w) :
    w.releasesTo me = i.releasesTo me := by
  rw [← InstrP.releasesTo_skel, fill_skel E.hash me σ i w h, InstrP.releasesTo_skel]

theorem count_one (w : Wire) (toH : Option Release) (h : toH.isSome = w.releasesTo me) :
    toH.toList.length = (if w.releasesTo me then 1 else 0) := by
  cases toH <;> cases hw : w.releasesTo me <;> simp_all

/-- A batch that the builder aborts: the model run does not return either. -/
theorem batch_aborted {α : Type} (s : Script α) : ∀ (σ : Store) (I : Ideal) (vD : List Release) ws r,
    nextBatch E.hash me σ s = ⟨ws, .aborted r⟩ → (withAdv E me adv s σ I vD).result = none := by
  induction s with
  | done a => intro σ I vD ws r h; simp [nextBatch] at h
  | abort r => intro σ I vD ws r' h; rfl
  | step i₀ k₀ ih =>
    intro σ I vD ws r h
    rcases hf : fill E.hash me σ i₀ with _ | w
    · simp [withAdv, hf]
    · by_cases he : i₀.endsBatch = true
      · simp [nextBatch, hf, he] at h
      · have he' : i₀.endsBatch = false := by simpa using he
        rcases hn : nextBatch E.hash me σ (k₀ .unit) with ⟨ws', rest⟩
        cases rest with
        | finished a => simp [nextBatch, hf, he', hn] at h
        | waiting i' k' => simp [nextBatch, hf, he', hn] at h
        | aborted r' =>
          rcases ha : adv.act (vD ++ w.early.toList) i₀.skel with _ | part
          · simp [withAdv, hf, ha]
          · rcases hi : idealStep E me w part I with _ | ⟨I', toH, toD⟩
            · simp [withAdv, hf, ha, hi]
            · have hab := absorb_notEnds E.hash me i₀ σ toH he'
              simp only [withAdv, hf, ha, hi, hab]
              exact ih .unit σ I' (vD ++ toD.toList) ws' r' hn

/-- A batch that finishes the script: the model run returns the same, with the same store and the
batch's instructions as its trace. -/
theorem batch_finished {α : Type} (s : Script α) : ∀ (σ : Store) (I : Ideal) (vD : List Release) ws a,
    nextBatch E.hash me σ s = ⟨ws, .finished a⟩ → (withAdv E me adv s σ I vD).result.isSome →
    (withAdv E me adv s σ I vD).result = some a ∧ (withAdv E me adv s σ I vD).store = σ ∧
      (withAdv E me adv s σ I vD).trace = ws.map InstrP.skel := by
  induction s with
  | done a =>
    intro σ I vD ws a' h _
    simp only [nextBatch, Batch.mk.injEq, Pending.finished.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  | abort r => intro σ I vD ws a h; simp [nextBatch] at h
  | step i₀ k₀ ih =>
    intro σ I vD ws a h hres
    rcases hf : fill E.hash me σ i₀ with _ | w
    · simp [nextBatch, hf] at h
    · by_cases he : i₀.endsBatch = true
      · simp [nextBatch, hf, he] at h
      · have he' : i₀.endsBatch = false := by simpa using he
        rcases hn : nextBatch E.hash me σ (k₀ .unit) with ⟨ws', rest⟩
        cases rest with
        | aborted r => simp [nextBatch, hf, he', hn] at h
        | waiting i' k' => simp [nextBatch, hf, he', hn] at h
        | finished a' =>
          simp only [nextBatch, hf, he', hn, Bool.false_eq_true, if_false, Batch.mk.injEq,
            Pending.finished.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases ha : adv.act (vD ++ w.early.toList) i₀.skel with _ | part
          · simp [withAdv, hf, ha] at hres
          · rcases hi : idealStep E me w part I with _ | ⟨I', toH, toD⟩
            · simp [withAdv, hf, ha, hi] at hres
            · have hab := absorb_notEnds E.hash me i₀ σ toH he'
              simp only [withAdv, hf, ha, hi, hab] at hres ⊢
              obtain ⟨h1, h2, h3⟩ := ih .unit σ I' (vD ++ toD.toList) ws' a' hn hres
              refine ⟨h1, h2, ?_⟩
              rw [h3, List.map_cons, fill_skel E.hash me σ i₀ w hf]

/-- **One batch that waits for a reply, in the model.** If the model run returns, it ran the batch's
instructions (its trace starts with them), released to the honest party `pre` (the batch's program
openings) and `toI` (the last instruction's release, if any: one per instruction that releases to
it), and continued with the last instruction's reply, `after`. -/
theorem batch_waiting {α : Type} (s : Script α) : ∀ (σ : Store) (I : Ideal) (vD : List Release) ws i k,
    nextBatch E.hash me σ s = ⟨ws, .waiting i k⟩ → (withAdv E me adv s σ I vD).result.isSome →
    ∃ (pre : List Release) (toI : Option Release) (I' : Ideal) (vD' : List Release),
      toI.isSome = i.releasesTo me ∧ (pre ++ toI.toList).length = itemCount me ws ∧
      (withAdv E me adv s σ I vD).viewH = pre ++ toI.toList ++ (after E me adv i k σ toI I' vD').viewH ∧
      (withAdv E me adv s σ I vD).trace = ws.map InstrP.skel ++ (after E me adv i k σ toI I' vD').trace ∧
      (withAdv E me adv s σ I vD).result = (after E me adv i k σ toI I' vD').result ∧
      (withAdv E me adv s σ I vD).store = (after E me adv i k σ toI I' vD').store := by
  induction s with
  | done a => intro σ I vD ws i k h; simp [nextBatch] at h
  | abort r => intro σ I vD ws i k h; simp [nextBatch] at h
  | step i₀ k₀ ih =>
    intro σ I vD ws i k h hres
    rcases hf : fill E.hash me σ i₀ with _ | w
    · simp [nextBatch, hf] at h
    · rcases ha : adv.act (vD ++ w.early.toList) i₀.skel with _ | part
      · simp [withAdv, hf, ha] at hres
      · rcases hi : idealStep E me w part I with _ | ⟨I', toH, toD⟩
        · simp [withAdv, hf, ha, hi] at hres
        · have htoH := idealStep_toH E me w part I I' toH toD hi
          have hrel := releasesTo_fill E me σ i₀ w hf
          by_cases he : i₀.endsBatch = true
          · simp only [nextBatch, hf, he, if_true, Batch.mk.injEq, Pending.waiting.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            refine ⟨[], toH, I', vD ++ toD.toList, by rw [htoH, hrel], ?_, ?_, ?_, ?_, ?_⟩
            · simp only [List.nil_append]
              rw [count_one me w toH htoH, itemCount_cons]
              simp [itemCount]
            · simp [withAdv, hf, ha, hi, after]
            · simp [withAdv, hf, ha, hi, after, fill_skel E.hash me σ i₀ w hf]
            · simp [withAdv, hf, ha, hi, after]
            · simp [withAdv, hf, ha, hi, after]
          · have he' : i₀.endsBatch = false := by simpa using he
            rcases hn : nextBatch E.hash me σ (k₀ .unit) with ⟨ws', rest⟩
            cases rest with
            | aborted r => simp [nextBatch, hf, he', hn] at h
            | finished a => simp [nextBatch, hf, he', hn] at h
            | waiting i' k' =>
              simp only [nextBatch, hf, he', hn, Bool.false_eq_true, if_false, Batch.mk.injEq,
                Pending.waiting.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              have hab := absorb_notEnds E.hash me i₀ σ toH he'
              have hres' : (withAdv E me adv (k₀ .unit) σ I' (vD ++ toD.toList)).result.isSome := by
                simpa [withAdv, hf, ha, hi, hab] using hres
              obtain ⟨pre, toI, I'', vD'', h1, h2, h3, h4, h5, h6⟩ :=
                ih .unit σ I' (vD ++ toD.toList) ws' _ _ hn hres'
              refine ⟨toH.toList ++ pre, toI, I'', vD'', h1, ?_, ?_, ?_, ?_, ?_⟩
              · rw [itemCount_cons, ← h2, ← count_one me w toH htoH]
                simp only [List.length_append]
                omega
              · simp only [withAdv, hf, ha, hi, hab]
                rw [h3]
                simp [List.append_assoc]
              · simp only [withAdv, hf, ha, hi, hab]
                rw [h4, List.map_cons, fill_skel E.hash me σ i₀ w hf]
                rfl
              · simp only [withAdv, hf, ha, hi, hab]
                exact h5
              · simp only [withAdv, hf, ha, hi, hab]
                exact h6

/-- **The controller sends exactly the batches the model says.** For any adversary, store and
engine state, if the honest party's model run of `s` returns `a`, then the runner's pure core, fed
the values the model released to that party (`viewH`, as the worker's reply items), with enough
fuel, sends batches whose instructions are exactly the model run's trace, in order, and returns `a`
with the model's final store. -/
theorem drive_model {α : Type} : ∀ (fuel : Nat) (s : Script α) (σ : Store) (I : Ideal) (vD : List Release) (a : α),
    (withAdv E me adv s σ I vD).result = some a → (withAdv E me adv s σ I vD).trace.length < fuel →
    (drive E.hash me fuel s σ ((withAdv E me adv s σ I vD).viewH.map (·.datum))).2 =
        (some a, (withAdv E me adv s σ I vD).store) ∧
      (drive E.hash me fuel s σ ((withAdv E me adv s σ I vD).viewH.map (·.datum))).1.flatten.map InstrP.skel =
        (withAdv E me adv s σ I vD).trace
  | 0, _, _, _, _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | fuel + 1, s, σ, I, vD, a, hr, hl => by
    have hsome : (withAdv E me adv s σ I vD).result.isSome := by rw [hr]; rfl
    rcases hn : nextBatch E.hash me σ s with ⟨ws, rest⟩
    cases rest with
    | aborted r =>
      have := batch_aborted E me adv s σ I vD ws r hn
      rw [hr] at this
      cases this
    | finished a' =>
      obtain ⟨h1, h2, h3⟩ := batch_finished E me adv s σ I vD ws a' hn hsome
      rw [hr] at h1
      cases h1
      simp only [drive, hn]
      refine ⟨by rw [h2], ?_⟩
      rw [h3]
      split
      · next he => simp [List.isEmpty_iff.mp he]
      · simp
    | waiting i k =>
      obtain ⟨pre, toI, I', vD', h1, h2, h3, h4, h5, h6⟩ := batch_waiting E me adv s σ I vD ws i k hn hsome
      have hne := nextBatch_waiting_ne E.hash me σ s ws i k hn
      have hds : (withAdv E me adv s σ I vD).viewH.map (·.datum) =
          (pre ++ toI.toList).map (·.datum) ++ (after E me adv i k σ toI I' vD').viewH.map (·.datum) := by
        rw [h3]; simp
      have hlen : ((pre ++ toI.toList).map (·.datum)).length = itemCount me ws := by simpa using h2
      have htake : ((withAdv E me adv s σ I vD).viewH.map (·.datum)).take (itemCount me ws) =
          (pre ++ toI.toList).map (·.datum) := by
        rw [hds, ← hlen, List.take_left']
        rfl
      have hdrop : ((withAdv E me adv s σ I vD).viewH.map (·.datum)).drop (itemCount me ws) =
          (after E me adv i k σ toI I' vD').viewH.map (·.datum) := by
        rw [hds, ← hlen, List.drop_left']
        rfl
      have hge : ¬ ((withAdv E me adv s σ I vD).viewH.map (·.datum)).length < itemCount me ws := by
        rw [hds, List.length_append, hlen]; omega
      have hres := resume_eq E.hash me i σ pre toI h1
      have hr' : (after E me adv i k σ toI I' vD').result = some a := by rw [← h5, hr]
      have hl' : (after E me adv i k σ toI I' vD').trace.length < fuel := by
        rw [h4, List.length_append, List.length_map] at hl
        have : 0 < ws.length := List.length_pos_iff.mpr hne
        omega
      obtain ⟨ih1, ih2⟩ := drive_model fuel _ _ I' vD' a hr' hl'
      have ih1' : (drive E.hash me fuel (k (absorb E.hash me i σ toI).1) (absorb E.hash me i σ toI).2
          ((after E me adv i k σ toI I' vD').viewH.map (·.datum))).2 =
          (some a, (after E me adv i k σ toI I' vD').store) := ih1
      have ih2' : (drive E.hash me fuel (k (absorb E.hash me i σ toI).1) (absorb E.hash me i σ toI).2
          ((after E me adv i k σ toI I' vD').viewH.map (·.datum))).1.flatten.map InstrP.skel =
          (after E me adv i k σ toI I' vD').trace := ih2
      simp only [drive, hn, hge, if_false, htake, hres, hdrop]
      refine ⟨by simp [ih1', h6], ?_⟩
      simp only [List.flatten_cons, List.map_append]
      rw [ih2', h4]

end Model

/-! ## The runner (IO glue) -/

/-- This party's private store as the runner keeps it, per slot (`Slots.store`: the `Store` `fill`
reads). Written only through `Secret.stash`. -/
structure Slots where
  bits : Std.HashMap Nat Bits := {}
  elems : Std.HashMap Nat (List F) := {}
  bytes : Std.HashMap Nat Bytes := {}

def Slots.store (m : Slots) : Store :=
  { bits := fun j => m.bits.getD j [], elems := fun j => m.elems.getD j [], bytes := fun j => m.bytes.getD j [] }

/-- The slots over a base store (a slot written here hides the base's; TEST: the vector tests'
fixed stores, `Runner.start`'s `base`). -/
def Slots.over (m : Slots) (base : Store) : Store :=
  { bits := fun j => m.bits[j]?.getD (base.bits j), elems := fun j => m.elems[j]?.getD (base.elems j),
    bytes := fun j => m.bytes[j]?.getD (base.bytes j) }

/-! ### J13: releasing slots

A script's private inputs live in store slots the runner hands out (`Runner.fresh`, a counter that
only grows). Once the script that read them has finished, the IO side RELEASES them
(`Runner.release`, used by the selection: the J1 supply after each operation, the commitment
nonces and values, the key and credential shares, the conversions' and the offset agreement's
contributions). Why a released slot is not read again:
  * `fresh` never hands it out again (`Ledger`: every slot handed out is at or above the counter,
    every released slot below it: `Ledger.fresh_not_released`, preserved by every step);
  * the joined scripts read only the slots handed to them for that run, each once (J1:
    `JoinOnce.openFirst_reads_once`, `session_reads_once`, `refreshOps_reads_once`);
  * and if a script still named a released slot, `fill` would read the base store's empty value
    there (`release_reads_base`), which no input's skeleton accepts (`Wire.payloadOk`: a payload
    must have the declared width): the batch is unusable for this party and both reject it (design
    note item 4) — it fails closed, it never reads an old secret. -/

/-- Erase slots `ns` from the store. -/
def Slots.release (m : Slots) (ns : List Nat) : Slots :=
  { bits := ns.foldl (fun t n => t.erase n) m.bits, elems := ns.foldl (fun t n => t.erase n) m.elems,
    bytes := ns.foldl (fun t n => t.erase n) m.bytes }

theorem foldl_erase {β : Type} (ns : List Nat) (t : Std.HashMap Nat β) (s : Nat) :
    (ns.foldl (fun t n => t.erase n) t)[s]? = if s ∈ ns then none else t[s]? := by
  induction ns generalizing t with
  | nil => simp
  | cons n ns ih =>
    simp only [List.foldl_cons, ih, Std.HashMap.getElem?_erase, List.mem_cons]
    by_cases h1 : s ∈ ns
    · simp [h1]
    · by_cases h2 : s = n
      · subst h2; simp
      · have h3 : (n == s) = false := by simp; omega
        simp [h1, h2, h3]

theorem foldl_erase_self {β : Type} (ns : List Nat) (t : Std.HashMap Nat β) (s : Nat) (hs : s ∈ ns) :
    (ns.foldl (fun t n => t.erase n) t)[s]? = none := by
  rw [foldl_erase]; simp [hs]

/-- **A released slot reads as the base store** (empty in a session). -/
theorem release_reads_base (m : Slots) (base : Store) (ns : List Nat) (s : Nat) (hs : s ∈ ns) :
    ((m.release ns).over base).bits s = base.bits s ∧ ((m.release ns).over base).elems s = base.elems s ∧
      ((m.release ns).over base).bytes s = base.bytes s := by
  simp [Slots.over, Slots.release, foldl_erase_self ns _ s hs]

/-- The slot ledger: the next fresh slot and the released ones (a model of `Runner.next` and the
releases). -/
structure Ledger where
  next : Nat
  released : List Nat

/-- Every released slot is below the counter. -/
def Ledger.Inv (l : Ledger) : Prop := ∀ s ∈ l.released, s < l.next

def Ledger.fresh (l : Ledger) : Nat × Ledger := (l.next, { l with next := l.next + 1 })

/-- Release slots handed out before (below the counter). -/
def Ledger.release (l : Ledger) (ns : List Nat) : Ledger :=
  { l with released := l.released ++ ns.filter (· < l.next) }

/-- **`fresh` never hands out a released slot**, and keeps the ledger's invariant. -/
theorem Ledger.fresh_not_released (l : Ledger) (h : l.Inv) : l.fresh.1 ∉ l.released ∧ l.fresh.2.Inv := by
  refine ⟨fun hm => by have := h _ hm; simp [Ledger.fresh] at this, fun s hs => ?_⟩
  have := h s hs
  simp [Ledger.fresh]; omega

theorem Ledger.release_inv (l : Ledger) (ns : List Nat) (h : l.Inv) : (l.release ns).Inv := by
  intro s hs
  simp only [Ledger.release, List.mem_append, List.mem_filter, decide_eq_true_eq] at hs
  rcases hs with hs | ⟨_, hs⟩
  · exact h s hs
  · exact hs

/-- **The runner**: the session's one script state and this party's store (module doc). -/
structure Runner where
  me : Party
  /-- SHA-256 (`Env.hash`: commitments). -/
  hash : Bytes → Bytes
  /-- The flow context whose pipe carries op 93 (`Legacy.call`, no connection selected). -/
  worker : Flow.Worker
  /-- The session's public script state: the contact table (its `ctr`: THE counters), the mask
  pool, the J1 supply. -/
  state : IO.Ref Receive.St
  slots : IO.Ref Slots
  /-- The next fresh store slot. -/
  next : IO.Ref Nat
  /-- `Channels.random`: this party's fresh randomness. -/
  random : Nat → IO (Secret Bytes)
  /-- The kernels the worker loaded (its manifest's names). -/
  loaded : Bytes → Bool
  /-- The V3 programs the worker loaded: their mask counts. -/
  programMasks : Bytes → Option Nat
  /-- The most batches one script may take. -/
  bound : Nat := 1000000
  /-- What the store holds before anything was stashed (empty in a session; TEST: a fixed store). -/
  base : Store := {}
  /-- Frees a finished script left for the next batch (`Runner.run`: a script's last batch that
  only frees handles is not sent alone; it opens the next batch). -/
  pending : IO.Ref (List Wire)

/-- A batch that only frees handles (`freeBool` / `freeField`): it releases nothing, reads nothing
and gives no reply item. -/
def freesOnly (ws : List Wire) : Bool :=
  ws.all fun w => match w with
    | .freeBool _ => true
    | .freeField _ => true
    | _ => false

theorem itemCount_append_frees (me : Party) (fs ws : List Wire) (h : freesOnly fs = true) :
    itemCount me (fs ++ ws) = itemCount me ws := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [freesOnly, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hf, hfs⟩ := h
    rw [List.cons_append, itemCount_cons, ih hfs]
    cases f <;> simp_all [InstrP.releasesTo]

namespace Runner

def get {α : Type} (r : IO.Ref α) : M α := (r.get : IO α)
def set {α : Type} (r : IO.Ref α) (a : α) : M Unit := (r.set a : IO Unit)

/-- A runner for this party (`me`), from its flow context; the state starts empty (the counters at
0, no mask pool: `Masks.generate` fills it, stage S10). -/
def start (w : Flow.Worker) (me : Party) (loaded : Bytes → Bool) (programMasks : Bytes → Option Nat)
    (base : Store := {}) (first : Nat := 1) : IO Runner := do
  return { me, hash := TlsMpc.TlsWire.hash, worker := { w with connection := none }, state := ← IO.mkRef {},
           slots := ← IO.mkRef {}, next := ← IO.mkRef first, random := w.random, loaded, programMasks, base,
           pending := ← IO.mkRef [] }

/-- One batch on the pipe (op 93): the pending frees (`pending`) and then `ws`, encoded, out; the
reply items in (as many as `itemCount`; the frees give none, `itemCount_append_frees`). The bytes are
`encodeBatch` / `decodeReplies` of them, computed by `encodeBatchArray` / `decodeRepliesFast`
(`encodeBatchArray_eq`: the array holds exactly `encodeBatch all`, sent by `Rpc.callArray`, which
writes those bytes; `decodeRepliesFast_eq`). -/
def batch (r : Runner) (ws : List Wire) : M (List Datum) := do
  let fs ← get r.pending
  set r.pending []
  let all := fs ++ ws
  let reply ← Flow.Legacy.callArray r.worker .batch (encodeBatchArray all)
  let some items := decodeRepliesFast reply | throw "undecodable batch reply"
  insist (items.length == itemCount r.me all) "batch reply count"
  return items

/-- **Run a script** (the IO loop of `drive`): batch by batch, `nextBatch` on this party's store,
op 93, `resume` on the reply items; an `openBoolTo`'s bits go into its slot (the one store write of a
script, decision D1). An abort is an error. A finished script's last batch that only frees handles
(`freesOnly`) is not sent on its own: it is kept in `pending` and sent at the head of the next batch
(the same instructions in the same order, one pipe operation and one agreement fewer; the handles
are released in the engines one batch later). Any other last batch, and the pending frees with it,
is sent at once. -/
def run (r : Runner) {α : Type} (s : Script α) : M α := loop r.bound s
where
  loop : Nat → Script α → M α
  | 0, _ => throw "script batch bound"
  | n + 1, s => do
    let m ← get r.slots
    let σ := m.over r.base
    match nextBatch r.hash r.me σ s with
    | ⟨_, .aborted reason⟩ => throw s!"script aborted: {reason}"
    | ⟨ws, .finished a⟩ =>
      unless ws.isEmpty do
        if freesOnly ws then
          set r.pending ((← get r.pending) ++ ws)
        else
          let _ ← r.batch ws
      return a
    | ⟨ws, .waiting i k⟩ =>
      let items ← r.batch ws
      let rs := resume r.hash r.me i σ items
      match i with
      | .openBoolTo _ _ _ dst => set r.slots { m with bits := m.bits.insert dst (rs.2.bits dst) }
      | _ => pure ()
      loop n (k rs.1)

/-- A fresh store slot. -/
def fresh (r : Runner) : M Nat := do
  let n ← get r.next
  set r.next (n + 1)
  return n

def stashBits (r : Runner) (v : Secret Bits) : M Nat := do
  let n ← r.fresh
  set r.slots (v.stash (fun b m => { m with bits := m.bits.insert n b }) (← get r.slots))
  return n

def stashBytes (r : Runner) (v : Secret Bytes) : M Nat := do
  let n ← r.fresh
  set r.slots (v.stash (fun b m => { m with bytes := m.bytes.insert n b }) (← get r.slots))
  return n

def stashElems (r : Runner) (v : Secret (List F)) : M Nat := do
  let n ← r.fresh
  set r.slots (v.stash (fun e m => { m with elems := m.elems.insert n e }) (← get r.slots))
  return n

/-- **J13: release slots** whose script has finished (module section "releasing slots"). -/
def release (r : Runner) (ns : List Nat) : M Unit := do
  set r.slots ((← get r.slots).release ns)

/-- Run a script, then release the slots it was given. -/
def runReleasing (r : Runner) {α : Type} (s : Script α) (ns : List Nat) : M α := do
  let a ← r.run s
  r.release ns
  return a

/-- A bit slot's content (what was opened to this party alone), kept secret. -/
def takeBits (r : Runner) (n : Nat) : M (Secret Bits) := do
  return Secret.hide (((← get r.slots).over r.base).bits n)

def randomM (r : Runner) (n : Nat) : M (Secret Bytes) := (r.random n : IO (Secret Bytes))

/-- A block of `k` Boolean ids from THE counters (the contact table's `ctr`). -/
def allocB (r : Runner) (k : Nat) : M Nat := do
  let st ← get r.state
  set r.state { st with table := (st.table.alloc k).2 }
  return (st.table.alloc k).1

/-- A block of `k` field ids from the same counters. -/
def allocF (r : Runner) (k : Nat) : M Nat := do
  let st ← get r.state
  set r.state { st with table := { st.table with ctr := (st.table.ctr.allocF k).2 } }
  return st.table.ctr.field

/-- A word mask from the session's pool (each handed out once, P-CUT (h)). -/
def takeWord (r : Runner) : M Conv.WordMask := do
  let st ← get r.state
  let some (m, p) := st.pool.takeWord | throw "mask pool"
  set r.state { st with pool := p }
  return m

/-- The contact table, inside the one state. -/
def table (r : Runner) : SendBackend.TableRef where
  get := return (← get r.state).table
  set t := do set r.state { (← get r.state) with table := t }

/-! ### The backends' runner interfaces, as views of the one runner -/

/-- S12 / S13 (`TlsBackend.Runner`). -/
def tls (r : Runner) : TlsBackend.Runner where
  me := r.me
  hash := r.hash
  run := r.run
  allocB := r.allocB
  stashBits := r.stashBits
  stashBytes := r.stashBytes
  slot := r.fresh
  take := r.takeBits
  random := r.randomM

/-- S11's flows' needs beyond S12's runner (`JoinBackend.FieldRunner`, J2). -/
def field (r : Runner) : JoinBackend.FieldRunner where
  allocF := r.allocF
  stashElems := r.stashElems
  takeWord := r.takeWord

/-- S14 (`ReceiveBackend.Runner`): the same state reference. -/
def receive (r : Runner) : ReceiveBackend.Runner where
  me := r.me
  run := r.run
  state := r.state
  stashBits := r.stashBits
  stashBytes := r.stashBytes
  stashElems := r.stashElems
  random := r.randomM
  loaded := r.loaded
  programMasks := r.programMasks
  release := r.release

/-- J1: fresh slots for the element counts `cs` (one new slot per count). -/
def supply (r : Runner) (cs : List Nat) : M (List (Nat × Nat)) := ReceiveBackend.supplyOf r.receive cs

end Runner

end TlsMpc.Node.Flows.Runner
