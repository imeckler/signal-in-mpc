import TlsMpc.Node.Flows.Join

/-!
# J1: no slot of fresh randomness is read twice by the joined receive and refresh flows

STACK_NOTES.md J1. The masks of a `program` instruction (its `D` rows' `b·m` openings) and of a
masked quotient (`z·m`) are each party's FRESH field-element contributions, input from a store slot
(`fieldInput … .elements … slot`; decision D1: randomness is put in the store before a script runs).
The engine's `check` refuses a repeated mask HANDLE (masks are consumed), but two inputs from ONE
slot make two handles with the same values: two openings `z₁·m`, `z₂·m` with the same `m` reveal
`z₁ / z₂`. Before the fix, S14's op 50 ran its two agreements with one `Join.AgreeSlots.masks` slot.

The fix (`Receive.St.slots`, `Receive.Gen.takeSlot`): every field-element input of the receive flows
reads a slot TAKEN from the state's supply, which removes it. This file proves the consequence for
every run, on every branch:

  * `readsAlong s rs`: the store slots the field-element inputs of script `s` read along the replies
    `rs` (as `Script.skeletons`, the instructions a run reaches).
  * `Once U Q seen s`: along every branch each slot read is in `U` and not read before (`seen`: the
    slots read so far); `Once.reads`: then the reads along ANY replies are pairwise distinct and in
    `U` (`(seen ++ readsAlong s rs).Nodup`).
  * For the state-threaded scripts (`Receive.Gen`): `OnceG U g` (from every state whose supply,
    together with what was read, has no slot twice and lies in `U`), `KeepsG g` (reads nothing,
    leaves the supply as it was), and the step that takes a slot then reads it (`takeSlot_bind`).
  * **`openFirst_reads_once`, `session_reads_once`** (ops 50, 51 with the joined curve
    `Join.receiveCurve`): every field-element slot the run reads is a slot of the supply it started
    with, and no slot is read twice, whatever the replies (so whatever the peer and the engines do).
    In particular op 50's two agreements and its `xeddsa-check` read three different slots.
  * **`refreshOps_reads_once`** (S15's curve operations, `Join.refreshOps`): the same for each of
    `lift`, `check`, `agree`, within the call's own supply; `RefreshBackend` gives each call a
    supply of new slots, so the calls of a step share none.

The other joins were checked for the same pattern (STACK_NOTES.md section 2): S12's
`JoinBackend.keyAgreement` and S13's `JoinBackend.sendCurve` stash a NEW mask slot on every call
(`fr.stashElems (← elems r k)` inside `agree` / `ephemeral`), so each quotient / offset sum has its
own; S15's `refreshOps` gave one word-mask pool to its three calls (fixed: `Join.RefreshCurve` has
one pool per call, `Join.split_disjoint`) and named its programs' mask slots (now taken).

No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Flows.JoinOnce

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees every_seq every_seqs every_openThen)
open TlsMpc.Node.Flows.Receive (Gen St Job)
open TlsMpc.Node.Flows.Run (isLocal openFieldThen sayThen every_openFieldThen every_sayThen)

/-! ## Reads of field-element slots, along a run -/

/-- The store slot a field-element input reads (the only reads of fresh mask contributions; a
`coins` input carries swap-bit shares, which P-BITS never masks an opening with). -/
def elemSlot? : Instr → Option Nat
  | .fieldInput _ _ .elements _ slot => some slot
  | _ => none

/-- The instruction reads no field-element slot. -/
def NoRead (i : Instr) : Prop := elemSlot? i = none

theorem noRead_local (i : Instr) (h : isLocal i = true) : NoRead i := by
  cases i <;> simp_all [isLocal, NoRead, elemSlot?]

/-- The slots the field-element inputs read along the replies `rs` (the instructions a run of `s`
reaches with these replies, as `Script.skeletons`). -/
def readsAlong {α : Type} : Script α → List Reply → List Nat
  | .done _, _ => []
  | .abort _, _ => []
  | .step i _, [] => (elemSlot? i).toList
  | .step i k, r :: rs => (elemSlot? i).toList ++ readsAlong (k r) rs

/-- **Along every branch, every slot read is in `U` and read once.** `seen`: the slots read so
far; `Q`: what holds at a leaf, with the slots read on the way. -/
inductive Once (U : List Nat) {α : Type} (Q : List Nat → α → Prop) : List Nat → Script α → Prop
  | done {seen : List Nat} {a : α} : Q seen a → Once U Q seen (.done a)
  | abort {seen : List Nat} (r : String) : Once U Q seen (.abort r)
  | step {seen : List Nat} {i : Instr} {k : Reply → Script α} :
      (∀ s, elemSlot? i = some s → s ∉ seen ∧ s ∈ U) →
      (∀ r, Once U Q (seen ++ (elemSlot? i).toList) (k r)) → Once U Q seen (.step i k)

theorem nodup_snoc {l : List Nat} {x : Nat} (h : l.Nodup) (hx : x ∉ l) : (l ++ [x]).Nodup :=
  List.nodup_append.mpr ⟨h, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
    fun a ha b hb e => by simp at hb; subst hb; subst e; exact hx ha⟩

theorem nodup_take_one {seen rest : List Nat} {s : Nat} (h : (seen ++ s :: rest).Nodup) : (seen ++ [s]).Nodup :=
  List.Nodup.sublist (List.sublist_append_left (seen ++ [s]) rest) (by simpa using h)

theorem nodup_skip_one {seen rest : List Nat} {s : Nat} (h : (seen ++ s :: rest).Nodup) : (seen ++ rest).Nodup :=
  List.Nodup.sublist (List.Sublist.append_left (List.sublist_cons_self s rest) seen) h

namespace Once

variable {U : List Nat} {α β : Type}

theorem nodup_step {seen : List Nat} {i : Instr} (hs : seen.Nodup)
    (hi : ∀ s, elemSlot? i = some s → s ∉ seen ∧ s ∈ U) : (seen ++ (elemSlot? i).toList).Nodup := by
  rcases h : elemSlot? i with _ | x
  · simpa using hs
  · simpa using nodup_snoc hs (hi x h).1

/-- **The reads of every run are distinct and in `U`.** -/
theorem reads {Q : List Nat → α → Prop} {seen : List Nat} {s : Script α} (h : Once U Q seen s) :
    seen.Nodup → ∀ rs, (seen ++ readsAlong s rs).Nodup ∧ ∀ x ∈ readsAlong s rs, x ∈ U := by
  induction h with
  | done _ => intro hs rs; cases rs <;> simp [readsAlong, hs]
  | abort r => intro hs rs; cases rs <;> simp [readsAlong, hs]
  | @step seen i k hi _ ih =>
    intro hs rs
    have hn := nodup_step hs hi
    have hu : ∀ x ∈ (elemSlot? i).toList, x ∈ U := by
      intro x hx
      rcases h : elemSlot? i with _ | y
      · rw [h] at hx; cases hx
      · rw [h] at hx; simp at hx; subst hx; exact (hi _ h).2
    cases rs with
    | nil => exact ⟨by simpa [readsAlong] using hn, by simpa [readsAlong] using hu⟩
    | cons r rs =>
      obtain ⟨h1, h2⟩ := ih r hn rs
      refine ⟨by simpa [readsAlong, List.append_assoc] using h1, fun x hx => ?_⟩
      simp only [readsAlong, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hu x hx
      · exact h2 x hx

theorem bind {Q : List Nat → α → Prop} {R : List Nat → β → Prop} {seen : List Nat} {s : Script α}
    {f : α → Script β} (h : Once U Q seen s) (hf : ∀ seen' a, Q seen' a → Once U R seen' (f a)) :
    Once U R seen (s.bind f) := by
  induction h with
  | done hq => exact hf _ _ hq
  | abort r => exact .abort r
  | step hi _ ih => exact .step hi ih

theorem mono {Q Q' : List Nat → α → Prop} {seen : List Nat} {s : Script α} (h : Once U Q seen s)
    (hq : ∀ seen' a, Q seen' a → Q' seen' a) : Once U Q' seen s := by
  induction h with
  | done h => exact .done (hq _ _ h)
  | abort r => exact .abort r
  | step hi _ ih => exact .step hi ih

/-- A script that reads no slot keeps `seen`. -/
theorem of_every {Q : List Nat → α → Prop} {seen : List Nat} {s : Script α} (h : Every NoRead s)
    (hq : ∀ a, Q seen a) : Once U Q seen s := by
  induction h with
  | done a => exact .done (hq a)
  | abort r => exact .abort r
  | step i k hi _ ih =>
    have hi' : elemSlot? i = none := hi
    refine .step (fun x hx => by rw [hi'] at hx; cases hx) (fun r => ?_)
    rw [hi', Option.toList_none, List.append_nil]
    exact ih r

theorem filterMap_cons (i : Instr) (is : List Instr) :
    (i :: is).filterMap elemSlot? = (elemSlot? i).toList ++ is.filterMap elemSlot? := by
  rcases h : elemSlot? i with _ | x <;> simp [List.filterMap_cons, h]

/-- **A block of unit-reply instructions**: its reads (`is.filterMap elemSlot?`), then `k`. -/
theorem seqs {Q : List Nat → α → Prop} {k : Script α} : ∀ (is : List Instr) {seen : List Nat},
    (seen ++ is.filterMap elemSlot?).Nodup → (∀ x ∈ is.filterMap elemSlot?, x ∈ U) →
    Once U Q (seen ++ is.filterMap elemSlot?) k → Once U Q seen (Contacts.seqs is k)
  | [], seen, _, _, hk => by simpa using hk
  | i :: is, seen, hn, hu, hk => by
    rw [filterMap_cons] at hn hu hk
    refine .step (fun x hx => ⟨?_, hu x (by simp [hx])⟩) (fun r => ?_)
    · intro hs
      rw [hx] at hn
      have := (List.nodup_append.mp hn).2.2
      exact this x hs x (by simp) rfl
    · cases r with
      | unit =>
        exact seqs is (by simpa [List.append_assoc] using hn)
          (fun x hx => hu x (List.mem_append_right _ hx)) (by simpa [List.append_assoc] using hk)
      | bits _ => exact .abort _
      | elems _ => exact .abort _
      | exchanged _ _ => exact .abort _

end Once

/-! ## Scripts that read no slot -/

/-- Every instruction on every branch reads no field-element slot. -/
abbrev NoReads {α : Type} (s : Script α) : Prop := Every NoRead s

theorem noReads_seqs {α : Type} {k : Script α} (hk : NoReads k) (is : List Instr) (h : ∀ i ∈ is, NoRead i) :
    NoReads (Contacts.seqs is k) := every_seqs hk is h

theorem noReads_locals {α : Type} {k : Script α} (hk : NoReads k) (is : List Instr)
    (h : ∀ i ∈ is, isLocal i = true) : NoReads (Contacts.seqs is k) :=
  every_seqs hk is (fun i hi => noRead_local i (h i hi))

theorem w2f_noReads (n0 f0 : Nat) (u : BoolH) (m : Conv.WordMask) : NoReads (Convert.wordToField n0 f0 u m) := by
  unfold Convert.wordToField
  refine every_seqs (every_openThen (P := NoRead) rfl fun c => ?_) _ (fun i hi => ?_)
  · unfold Convert.w2fRest
    split
    · refine every_sayThen rfl fun r => ?_
      split
      · exact noReads_locals (Every.done _) _ (Convert.w2fTail_local n0 f0 m _)
      · exact Every.abort _
    · exact Every.abort _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rfl

theorem f2w_noReads (n0 f0 : Nat) (v : FieldH) (m : Conv.WordMask) : NoReads (Convert.fieldToWord n0 f0 v m) := by
  unfold Convert.fieldToWord
  refine every_seq rfl (every_openFieldThen rfl fun cs => ?_)
  unfold Convert.f2wRest
  split
  · refine every_sayThen rfl fun r => ?_
    split
    · exact noReads_locals (Every.done _) _ (Convert.f2wTail_local n0 f0 m _)
    · exact Every.abort _
  · exact Every.abort _

theorem b2f_noReads (n0 f0 : Nat) (x : BoolH) (ps : List Conv.BitPair) : NoReads (Convert.bitsToField n0 f0 x ps) := by
  unfold Convert.bitsToField
  refine every_seqs (every_openThen (P := NoRead) rfl fun o => ?_) _ (fun i hi => ?_)
  · split
    · exact noReads_locals (Every.done _) _ (Convert.b2fTail_local n0 f0 o ps)
    · exact Every.abort _
  · simp only [Convert.b2fBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl

/-- P-BITS inputs COINS (the swap-bit shares), not elements: no slot of fresh masks is read. -/
theorem bits_noReads (f0 n slot : Nat) : NoReads (Convert.sharedBits f0 n slot) := by
  unfold Convert.sharedBits
  refine every_seq rfl (every_seq rfl (every_openFieldThen rfl fun z => ?_))
  split
  · exact every_seq rfl (Every.done _)
  · exact Every.abort _

/-! ## Scripts that read one given slot at most once -/

/-- `t` reads at most the slot `s`, once. -/
def ReadsAtMost {α : Type} (s : Nat) (t : Script α) : Prop :=
  ∀ (U seen : List Nat), (seen ++ [s]).Nodup → s ∈ U →
    Once U (fun seen' _ => seen' = seen ∨ seen' = seen ++ [s]) seen t

theorem readsAtMost_of_noReads {α : Type} (s : Nat) {t : Script α} (h : NoReads t) : ReadsAtMost s t :=
  fun _ _ _ _ => Once.of_every h (fun _ => Or.inl rfl)

/-- A block whose reads are `[s]` (or none), then a script that reads nothing. -/
theorem readsAtMost_seqs {α : Type} (s : Nat) {k : Script α} (hk : NoReads k) (is : List Instr)
    (h : is.filterMap elemSlot? = [s] ∨ is.filterMap elemSlot? = []) : ReadsAtMost s (Contacts.seqs is k) := by
  intro U seen hn hs
  rcases h with h | h
  · refine Once.seqs is (by rw [h]; exact hn) (by rw [h]; simpa using hs) ?_
    rw [h]
    exact Once.of_every hk (fun _ => Or.inr rfl)
  · refine Once.seqs is (by rw [h]; simpa using (List.nodup_append.mp hn).1) (by rw [h]; simp) ?_
    rw [h]
    exact Once.of_every hk (fun _ => Or.inl (List.append_nil _))

theorem filterMap_none {is : List Instr} (h : ∀ i ∈ is, NoRead i) : is.filterMap elemSlot? = [] :=
  List.filterMap_eq_nil_iff.mpr h

/-- A block that reads nothing, then `k`. -/
theorem Once.seqs_noRead {U : List Nat} {α : Type} {Q : List Nat → α → Prop} {k : Script α} {seen : List Nat}
    (is : List Instr) (h : ∀ i ∈ is, NoRead i) (hs : seen.Nodup) (hk : Once U Q seen k) :
    Once U Q seen (Contacts.seqs is k) := by
  have e := filterMap_none h
  exact Once.seqs is (by rw [e]; simpa using hs) (by rw [e]; simp) (by rw [e, List.append_nil]; exact hk)

theorem sharedBlock_reads (f k slot : Nat) :
    (Curve.sharedBlock f k slot).filterMap elemSlot? = [slot] := by
  simp [Curve.sharedBlock, elemSlot?, List.filterMap_map, Function.comp_def]

/-- **A masked quotient round reads its mask slot once** (S11's `quotientMany`). -/
theorem quotientMany_reads (f slot : Nat) (pairs : List (FieldH × FieldH)) :
    ReadsAtMost slot (Curve.quotientMany f slot pairs) := by
  unfold Curve.quotientMany
  dsimp only
  split
  · exact readsAtMost_of_noReads _ (Every.done _)
  · refine readsAtMost_seqs slot (every_openFieldThen (P := NoRead) rfl fun fl => ?_) _ (Or.inl ?_)
    · split
      · refine noReads_seqs (Every.done _) _ (fun i hi => ?_)
        simp only [Curve.freeFs, List.mem_append, List.mem_map] at hi
        rcases hi with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
      · exact Every.abort _
    · simp [List.filterMap_append, sharedBlock_reads, elemSlot?]

/-- **S11's ladder agreements read their quotient-mask slot once.** -/
theorem agree_reads (f slot : Nat) (jobs : List (List FieldH × FieldH)) : ReadsAtMost slot (Curve.agree f slot jobs) := by
  unfold Curve.agree
  dsimp only
  split
  · exact readsAtMost_of_noReads _ (Every.done _)
  · split
    · intro U seen hn hs
      refine Once.seqs_noRead _ (fun i hi => ?_) (List.nodup_append.mp hn).1 (quotientMany_reads _ slot _ U seen hn hs)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> rfl
    · exact readsAtMost_of_noReads _ (Every.abort _)

/-! ## The state-threaded scripts -/

/-- The supply's slots. -/
def supply (st : St) : List Nat := st.slots.map Prod.fst

/-- What was read and what is left to take have no slot twice, and the supply lies in `U`. -/
def Inv (U seen : List Nat) (st : St) : Prop := (seen ++ supply st).Nodup ∧ ∀ x ∈ supply st, x ∈ U

/-- **From every state satisfying the invariant, every run reads each slot once, from `U`, and
leaves the invariant.** -/
def OnceG (U : List Nat) {α : Type} (g : Gen α) : Prop :=
  ∀ seen st, Inv U seen st → Once U (fun seen' p => Inv U seen' p.2) seen (g st)

/-- Reads nothing and leaves the supply as it was. -/
def KeepsG {α : Type} (g : Gen α) : Prop :=
  ∀ (U seen : List Nat) (st : St), Once U (fun seen' p => seen' = seen ∧ p.2.slots = st.slots) seen (g st)

/-- After the slot `s` was taken (so it is in no later supply): reads it at most once, nothing else
of the supply. -/
def OnceWithG (U : List Nat) (s : Nat) {α : Type} (g : Gen α) : Prop :=
  ∀ seen st, (seen ++ s :: supply st).Nodup → s ∈ U → (∀ x ∈ supply st, x ∈ U) →
    Once U (fun seen' p => Inv U seen' p.2) seen (g st)

/-- Reads at most the slot `s`, once, and leaves the supply as it was. -/
def ReadsAtMostG (s : Nat) {α : Type} (g : Gen α) : Prop :=
  ∀ (U seen : List Nat) (st : St), (seen ++ [s]).Nodup → s ∈ U →
    Once U (fun seen' p => (seen' = seen ∨ seen' = seen ++ [s]) ∧ p.2.slots = st.slots) seen (g st)

section Gen

variable {α β : Type}

theorem bind_apply (x : Gen α) (f : α → Gen β) (st : St) :
    (x >>= f) st = Script.bind (x st) (fun p => f p.1 p.2) := rfl

namespace KeepsG

theorem pure (a : α) : KeepsG (Pure.pure a : Gen α) := fun _ _ _ => .done ⟨rfl, rfl⟩

theorem bind {x : Gen α} {f : α → Gen β} (hx : KeepsG x) (hf : ∀ a, KeepsG (f a)) : KeepsG (x >>= f) := by
  intro U seen st
  rw [bind_apply]
  refine (hx U seen st).bind fun seen' p hp => ?_
  obtain ⟨rfl, hs⟩ := hp
  exact (hf p.1 U seen' p.2).mono fun _ _ h => ⟨h.1, h.2.trans hs⟩

theorem lift {s : Script α} (h : NoReads s) : KeepsG (Receive.Gen.lift s) := by
  intro U seen st
  show Once U _ seen (Script.bind s fun a => .done (a, st))
  exact (Once.of_every h (Q := fun seen' _ => seen' = seen) (fun _ => rfl)).bind fun _ _ h => .done ⟨h, rfl⟩

theorem fail (r : String) : KeepsG (Receive.Gen.fail r : Gen α) := lift (Every.abort r)

theorem ite {c : Prop} [Decidable c] {x y : Gen α} (hx : KeepsG x) (hy : KeepsG y) : KeepsG (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem allocB (k : Nat) : KeepsG (Receive.Gen.allocB k) := fun _ _ _ => .done ⟨rfl, rfl⟩
theorem allocF (k : Nat) : KeepsG (Receive.Gen.allocF k) := fun _ _ _ => .done ⟨rfl, rfl⟩

theorem takeWord : KeepsG Receive.Gen.takeWord := by
  intro U seen st
  unfold Receive.Gen.takeWord
  split
  · exact .done ⟨rfl, rfl⟩
  · exact .abort _

theorem takeBits (k : Nat) : KeepsG (Receive.Gen.takeBits k) := by
  intro U seen st
  unfold Receive.Gen.takeBits
  split
  · exact .done ⟨rfl, rfl⟩
  · exact .abort _

theorem instrs {is : List Instr} (h : ∀ i ∈ is, NoRead i) : KeepsG (Receive.Gen.instrs is) :=
  lift (noReads_seqs (Every.done _) is h)

theorem freeAll (hs : List BoolH) : KeepsG (Receive.Gen.freeAll hs) := by
  refine instrs fun i hi => ?_
  simp only [frees, List.mem_map] at hi
  obtain ⟨_, _, rfl⟩ := hi
  rfl

theorem freeFields (hs : List FieldH) : KeepsG (Receive.Gen.freeFields hs) := by
  refine instrs fun i hi => ?_
  simp only [Receive.freeFieldsI, List.mem_map] at hi
  obtain ⟨_, _, rfl⟩ := hi
  rfl

end KeepsG

namespace OnceG

theorem of_keeps {U : List Nat} {g : Gen α} (h : KeepsG g) : OnceG U g := by
  intro seen st hinv
  refine (h U seen st).mono fun seen' p hp => ?_
  obtain ⟨rfl, hs⟩ := hp
  simpa [Inv, supply, hs] using hinv

theorem pure {U : List Nat} (a : α) : OnceG U (Pure.pure a : Gen α) := of_keeps (KeepsG.pure a)

theorem bind {U : List Nat} {x : Gen α} {f : α → Gen β} (hx : OnceG U x) (hf : ∀ a, OnceG U (f a)) :
    OnceG U (x >>= f) := by
  intro seen st hinv
  rw [bind_apply]
  exact (hx seen st hinv).bind fun seen' p hp => hf p.1 seen' p.2 hp

theorem ite {U : List Nat} {c : Prop} [Decidable c] {x y : Gen α} (hx : OnceG U x) (hy : OnceG U y) :
    OnceG U (if c then x else y) := by
  split
  · exact hx
  · exact hy

/-- **Take a slot from the supply, then read it at most once.** -/
theorem takeSlot_bind {U : List Nat} (count : Nat) {f : Nat → Gen β} (hf : ∀ s, OnceWithG U s (f s)) :
    OnceG U (Receive.Gen.takeSlot count >>= f) := by
  intro seen st hinv
  rw [bind_apply]
  unfold Receive.Gen.takeSlot
  split
  · next s k rest heq =>
    split
    · have hsup : supply st = s :: supply { st with slots := rest } := by simp [supply, heq]
      obtain ⟨hn, hu⟩ := hinv
      rw [hsup] at hn hu
      exact hf s seen { st with slots := rest } hn (hu s (by simp))
        (fun x hx => hu x (by simp [hx]))
    · exact .abort _
  · exact .abort _

end OnceG

namespace OnceWithG

theorem keeps_bind {U : List Nat} {s : Nat} {x : Gen α} {f : α → Gen β} (hx : KeepsG x)
    (hf : ∀ a, OnceWithG U s (f a)) : OnceWithG U s (x >>= f) := by
  intro seen st hn hs hu
  rw [bind_apply]
  refine (hx U seen st).bind fun seen' p hp => ?_
  obtain ⟨rfl, hsl⟩ := hp
  have e : supply p.2 = supply st := by simp [supply, hsl]
  exact hf p.1 seen' p.2 (by rw [e]; exact hn) hs (by rw [e]; exact hu)

theorem read_bind {U : List Nat} {s : Nat} {x : Gen α} {f : α → Gen β} (hx : ReadsAtMostG s x)
    (hf : ∀ a, KeepsG (f a)) : OnceWithG U s (x >>= f) := by
  intro seen st hn hs hu
  rw [bind_apply]
  refine (hx U seen st (nodup_take_one hn) hs).bind fun seen' p hp => ?_
  refine (hf p.1 U seen' p.2).mono fun seen'' q hq => ?_
  obtain ⟨rfl, hq2⟩ := hq
  obtain ⟨hseen, hp2⟩ := hp
  have e : supply q.2 = supply st := by simp [supply, hq2, hp2]
  refine ⟨?_, by rw [e]; exact hu⟩
  rw [e]
  rcases hseen with rfl | rfl
  · exact nodup_skip_one hn
  · simpa [List.append_assoc] using hn

end OnceWithG

namespace ReadsAtMostG

theorem lift {s : Nat} {t : Script α} (h : ReadsAtMost s t) : ReadsAtMostG s (Receive.Gen.lift t) := by
  intro U seen st hn hs
  show Once U _ seen (Script.bind t fun a => .done (a, st))
  exact (h U seen hn hs).bind fun _ _ h => .done ⟨h, rfl⟩

theorem instrs {s : Nat} {is : List Instr} (h : is.filterMap elemSlot? = [s] ∨ is.filterMap elemSlot? = []) :
    ReadsAtMostG s (Receive.Gen.instrs is) :=
  lift (readsAtMost_seqs s (Every.done _) is h)

/-- Read at most `s`, then something that reads nothing. -/
theorem bind_keeps {s : Nat} {x : Gen α} {f : α → Gen β} (hx : ReadsAtMostG s x) (hf : ∀ a, KeepsG (f a)) :
    ReadsAtMostG s (x >>= f) := by
  intro U seen st hn hs
  rw [bind_apply]
  refine (hx U seen st hn hs).bind fun seen' p hp => ?_
  refine (hf p.1 U seen' p.2).mono fun _ _ hq => ?_
  exact ⟨hq.1 ▸ hp.1, hq.2.trans hp.2⟩

end ReadsAtMostG

end Gen

/-! ## The receive pieces -/

section Pieces

open TlsMpc.Node.Flows.Receive

theorem stage_keeps (name : Bytes) (parts : List BoolH) (widths : List Nat) : KeepsG (stage name parts widths) := by
  refine KeepsG.bind (KeepsG.allocB _) fun n => KeepsG.bind (KeepsG.instrs fun i hi => ?_) fun _ => KeepsG.pure _
  simp only [stageInstrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hi
  rcases hi with (h | h) | h | h
  · rcases h with rfl | rfl <;> rfl
  · obtain ⟨_, _, rfl⟩ := h; rfl
  · subst h; rfl
  · subst h; rfl

theorem openFree_keeps (h : BoolH) (l : Label) : KeepsG (openFree h l) :=
  KeepsG.lift (every_openThen rfl fun _ => noReads_seqs (Every.done _) _ (by simp [NoRead, elemSlot?]))

theorem publicBits_keeps (b : Bits) : KeepsG (publicBits b) :=
  KeepsG.bind (KeepsG.allocB _) fun _ => KeepsG.bind (KeepsG.instrs (by simp [NoRead, elemSlot?])) fun _ => KeepsG.pure _

theorem inputA_keeps (slot width : Nat) : KeepsG (inputA slot width) :=
  KeepsG.bind (KeepsG.allocB _) fun _ => KeepsG.bind (KeepsG.instrs (by simp [NoRead, elemSlot?])) fun _ => KeepsG.pure _

theorem join_keeps (parts : List BoolH) : KeepsG (Receive.join parts) :=
  KeepsG.bind (KeepsG.allocB _) fun _ => KeepsG.bind (KeepsG.instrs (by simp [NoRead, elemSlot?])) fun _ => KeepsG.pure _

theorem cut_keeps (h : BoolH) (lo hi : Nat) : KeepsG (cut h lo hi) :=
  KeepsG.bind (KeepsG.allocB _) fun _ => KeepsG.bind (KeepsG.instrs (by simp [NoRead, elemSlot?])) fun _ => KeepsG.pure _

theorem publicField_keeps (v : TlsMpc.FieldDag.F) : KeepsG (publicField v) :=
  KeepsG.bind (KeepsG.allocF _) fun _ => KeepsG.bind (KeepsG.instrs (by simp [NoRead, elemSlot?])) fun _ => KeepsG.pure _

theorem toField_keeps (u : BoolH) : KeepsG (toField u) :=
  KeepsG.bind KeepsG.takeWord fun m => KeepsG.bind (KeepsG.allocB _) fun n =>
    KeepsG.bind (KeepsG.allocF _) fun f => KeepsG.lift (w2f_noReads n f u m)

theorem toWord_keeps (v : FieldH) : KeepsG (toWord v) :=
  KeepsG.bind KeepsG.takeWord fun m => KeepsG.bind (KeepsG.allocB _) fun n =>
    KeepsG.bind (KeepsG.allocF _) fun f => KeepsG.lift (f2w_noReads n f v m)

theorem toFieldBits_keeps (x : BoolH) (k : Nat) : KeepsG (toFieldBits x k) :=
  KeepsG.bind (KeepsG.takeBits k) fun ps => KeepsG.bind (KeepsG.allocB _) fun n =>
    KeepsG.bind (KeepsG.allocF _) fun f => KeepsG.lift (b2f_noReads n f x ps)

theorem refuse_keeps {α : Type} (hs : List BoolH) (fs : List FieldH) : KeepsG (refuse hs fs : Gen (Option α)) :=
  KeepsG.bind (KeepsG.freeAll hs) fun _ => KeepsG.bind (KeepsG.freeFields fs) fun _ => KeepsG.pure _

theorem programInstrs_reads (f : Nat) (name : Bytes) (ins : List FieldH) (outs masks slot : Nat) (l : Label) :
    (programInstrs f name ins outs masks slot l).filterMap elemSlot? = [slot] ∨
      (programInstrs f name ins outs masks slot l).filterMap elemSlot? = [] := by
  by_cases h : masks = 0
  · right
    subst h
    simp [programInstrs, elemSlot?, List.filterMap_map, Function.comp_def]
  · left
    simp [programInstrs, h, elemSlot?, List.filterMap_map, Function.comp_def]

/-- **A program step reads one slot it took from the supply** (or none, without masks). -/
theorem programStep_once {U : List Nat} (name : Bytes) (ins : List FieldH) (outs masks : Nat) (l : Label) :
    OnceG U (programStep name ins outs masks l) := by
  unfold programStep maskSlot
  split
  · next hm =>
    refine OnceG.of_keeps (KeepsG.bind (KeepsG.pure _) fun slot =>
      KeepsG.bind (KeepsG.allocF _) fun f => KeepsG.bind (KeepsG.instrs ?_) fun _ => KeepsG.pure _)
    refine List.filterMap_eq_nil_iff.mp ?_
    subst hm
    simp [programInstrs, elemSlot?, List.filterMap_map, Function.comp_def]
  · exact OnceG.takeSlot_bind _ fun s => OnceWithG.keeps_bind (KeepsG.allocF _) fun f =>
      OnceWithG.read_bind (ReadsAtMostG.instrs (programInstrs_reads _ _ _ _ _ _ _)) fun _ => KeepsG.pure _

end Pieces

/-! ## The curve parameter -/

/-- **A curve parameter that reads each slot once** (from the supply). -/
structure CurveOnce (cv : Receive.Curve) : Prop where
  agree : ∀ U jobs, OnceG U (cv.agree jobs)
  signature : ∀ U x y bits, OnceG U (cv.signature x y bits)
  baseCheck : ∀ U b, OnceG U (cv.baseCheck b)

theorem withPrograms_once (agree : List Job → Gen (List BoolH)) (kinds : List TlsMpc.Node.RevealKind)
    (hagree : ∀ jobs st, Reveals kinds (agree jobs st)) (pm : Receive.ProgramMasks)
    (h : ∀ U jobs, OnceG U (agree jobs)) : CurveOnce (Receive.Curve.withPrograms agree kinds hagree pm) where
  agree := h
  signature U _ _ _ := OnceG.bind (programStep_once _ _ _ _ _) fun _ => OnceG.pure _
  baseCheck U _ := OnceG.bind (programStep_once _ _ _ _ _) fun _ =>
    OnceG.bind (programStep_once _ _ _ _ _) fun _ => OnceG.bind (OnceG.of_keeps (KeepsG.freeFields _)) fun _ =>
      OnceG.pure _

/-! ## The joined agreements -/

section Agree

open TlsMpc.Node.Flows.Join

theorem jobBits_keeps (sl : AgreeSlots) (j : Job) : KeepsG (jobBits sl j) :=
  KeepsG.bind (KeepsG.allocF _) fun f => KeepsG.bind (KeepsG.lift (bits_noReads f 252 _)) fun _ =>
    KeepsG.bind (KeepsG.freeFields _) fun _ => KeepsG.pure _

theorem jobPoint_keeps (p : Receive.Point) : KeepsG (jobPoint p) := by
  cases p with
  | handle h => exact KeepsG.pure _
  | base => exact KeepsG.bind (publicField_keeps _) fun _ => KeepsG.pure _

theorem jobsIn_keeps (sl : AgreeSlots) : ∀ jobs, KeepsG (jobsIn sl jobs)
  | [] => KeepsG.pure _
  | j :: js => by
    unfold jobsIn
    exact KeepsG.bind (jobBits_keeps sl j) fun _ => KeepsG.bind (jobPoint_keeps _) fun _ =>
      KeepsG.bind (jobsIn_keeps sl js) fun _ => KeepsG.pure _

theorem wordsOf_keeps : ∀ rs, KeepsG (wordsOf rs)
  | [] => KeepsG.pure _
  | r :: rs => by
    unfold wordsOf
    exact KeepsG.bind (toWord_keeps _) fun _ => KeepsG.bind (wordsOf_keeps rs) fun _ => KeepsG.pure _

theorem agreeTail_keeps (made : List FieldH) (f n : Nat) (rs : List (FieldH × Bool)) : KeepsG (agreeTail made f n rs) := by
  unfold agreeTail
  exact KeepsG.ite (KeepsG.fail _) (KeepsG.bind (wordsOf_keeps rs) fun _ =>
    KeepsG.bind (KeepsG.freeFields _) fun _ => KeepsG.pure _)

/-- **The joined agreements take their quotient-mask slot from the supply and read it once.** -/
theorem receiveAgree_once (U : List Nat) (sl : AgreeSlots) (jobs : List Job) : OnceG U (receiveAgree sl jobs) := by
  unfold receiveAgree
  refine OnceG.ite (OnceG.pure _) ?_
  refine OnceG.bind (OnceG.of_keeps (jobsIn_keeps sl jobs)) fun ins => ?_
  refine OnceG.takeSlot_bind _ fun slot => OnceWithG.keeps_bind (KeepsG.allocF _) fun f => ?_
  exact OnceWithG.read_bind (ReadsAtMostG.lift (agree_reads f slot ins.1)) fun rs => agreeTail_keeps _ _ _ _

theorem receiveCurve_once (sl : AgreeSlots) (pm : Receive.ProgramMasks) : CurveOnce (receiveCurve sl pm) :=
  withPrograms_once _ _ _ pm fun U jobs => receiveAgree_once U sl jobs

end Agree

/-! ## Ops 50 and 51 -/

section Ops

open TlsMpc.Node.Flows.Receive

variable (cv : Curve) (hcv : CurveOnce cv) (loaded : Bytes → Bool)

theorem firstPrekey_once (U : List Nat) (us ct ce ve : List BoolH) (oursH : BoolH) (senderF : FieldH) (n : Nat) :
    OnceG U (firstPrekey loaded us ct ce ve oursH senderF n) := by
  refine OnceG.of_keeps ?_
  unfold firstPrekey
  dsimp only
  refine KeepsG.ite (refuse_keeps _ _) ?_
  refine KeepsG.bind (stage_keeps _ _ _) fun ps => ?_
  refine KeepsG.bind (openFree_keeps _ _) fun flags => ?_
  split
  · exact refuse_keeps _ _
  · refine KeepsG.ite (refuse_keeps _ _) ?_
    refine KeepsG.bind (stage_keeps _ _ _) fun po => ?_
    refine KeepsG.bind (KeepsG.freeAll _) fun _ => ?_
    refine KeepsG.bind (join_keeps _) fun ids => ?_
    refine KeepsG.bind (KeepsG.freeAll _) fun _ => ?_
    refine KeepsG.bind (openFree_keeps _ _) fun _ => ?_
    refine KeepsG.bind (toField_keeps _) fun _ => ?_
    refine KeepsG.bind (toField_keeps _) fun _ => ?_
    exact KeepsG.bind (KeepsG.freeAll _) fun _ => KeepsG.pure _

include hcv in
theorem firstCertificate_once (U : List Nat) (fi : FirstIn) (us ct : List BoolH) (oursH : BoolH) (senderF : FieldH)
    (c0 c1 cert : Nat) (shape : Contacts.B8) (msg : Nat) :
    OnceG U (firstCertificate cv loaded fi us ct oursH senderF c0 c1 cert shape msg) := by
  unfold firstCertificate
  split
  · exact OnceG.of_keeps (refuse_keeps _ _)
  · split
    · exact OnceG.of_keeps (refuse_keeps _ _)
    · refine OnceG.ite (OnceG.of_keeps (refuse_keeps _ _)) ?_
      refine OnceG.bind (OnceG.of_keeps (publicBits_keeps _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (publicBits_keeps _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (publicBits_keeps _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (publicBits_keeps _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (stage_keeps _ _ _)) fun ce => ?_
      refine OnceG.bind (OnceG.of_keeps (KeepsG.freeAll _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (join_keeps _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (KeepsG.freeAll _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (toFieldBits_keeps _ _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (KeepsG.freeAll _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (publicField_keeps _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (publicField_keeps _)) fun _ => ?_
      refine OnceG.bind (hcv.signature U _ _ _) fun r => ?_
      refine OnceG.bind (OnceG.of_keeps (KeepsG.freeFields _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (toWord_keeps _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (toWord_keeps _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (KeepsG.freeFields _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (publicBits_keeps _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (stage_keeps _ _ _)) fun _ => ?_
      refine OnceG.bind (OnceG.of_keeps (KeepsG.freeAll _)) fun _ => ?_
      exact firstPrekey_once loaded U _ _ _ _ _ _ _

include hcv in
theorem firstContent_once (U : List Nat) (fi : FirstIn) (us um : List BoolH) (oursH : BoolH) (senderF : FieldH)
    (u : Nat) (prefix_ : Contacts.B8) : OnceG U (firstContent cv loaded fi us um oursH senderF u prefix_) := by
  unfold firstContent
  dsimp only
  split
  · exact OnceG.of_keeps (refuse_keeps _ _)
  · refine OnceG.ite (OnceG.of_keeps (refuse_keeps _ _)) ?_
    refine OnceG.bind (OnceG.of_keeps (stage_keeps _ _ _)) fun cs => ?_
    refine OnceG.bind (OnceG.of_keeps (openFree_keeps _ _)) fun _ => ?_
    split
    · refine OnceG.ite (OnceG.of_keeps (refuse_keeps _ _)) ?_
      refine OnceG.ite (OnceG.of_keeps (refuse_keeps _ _)) ?_
      refine OnceG.bind (OnceG.of_keeps (stage_keeps _ _ _)) fun ct => ?_
      refine OnceG.bind (OnceG.of_keeps (KeepsG.freeAll _)) fun _ => ?_
      exact firstCertificate_once cv hcv loaded U fi _ _ _ _ _ _ _ _ _
    · exact OnceG.of_keeps (refuse_keeps _ _)

include hcv in
/-- **Op 50 reads each slot once, from the supply** (for any curve parameter that does). -/
theorem openFirst_once (U : List Nat) (fi : FirstIn) (env : BoolH) (size : Nat) :
    OnceG U (openFirst cv loaded fi env size) := by
  unfold openFirst
  refine OnceG.ite (OnceG.of_keeps (refuse_keeps _ _)) ?_
  refine OnceG.bind (OnceG.of_keeps (stage_keeps _ _ _)) fun ep => ?_
  refine OnceG.bind (OnceG.of_keeps (toField_keeps _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (KeepsG.freeAll _)) fun _ => ?_
  refine OnceG.bind (hcv.agree U _) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (KeepsG.freeFields _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (publicBits_keeps _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (stage_keeps _ _ _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (KeepsG.freeAll _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (toField_keeps _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (KeepsG.freeAll _)) fun _ => ?_
  refine OnceG.bind (hcv.agree U _) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (stage_keeps _ _ _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (KeepsG.freeAll _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (openFree_keeps _ _)) fun _ => ?_
  exact firstContent_once cv hcv loaded U fi _ _ _ _ _ _

theorem sessionRest_keeps (cert ct : Nat) (se : List BoolH) (status : Bits) :
    KeepsG (sessionRest loaded cert ct se status) := by
  unfold sessionRest
  dsimp only
  refine KeepsG.ite (refuse_keeps _ _) ?_
  refine KeepsG.ite (refuse_keeps _ _) ?_
  refine KeepsG.bind (stage_keeps _ _ _) fun tx => ?_
  refine KeepsG.bind (openFree_keeps _ _) fun _ => ?_
  refine KeepsG.ite (refuse_keeps _ _) ?_
  refine KeepsG.bind (join_keeps _) fun _ => ?_
  refine KeepsG.bind (KeepsG.freeAll _) fun _ => ?_
  refine KeepsG.bind (openFree_keeps _ _) fun _ => ?_
  split
  · exact refuse_keeps _ _
  refine KeepsG.ite (refuse_keeps _ _) ?_
  refine KeepsG.bind (stage_keeps _ _ _) fun _ => ?_
  refine KeepsG.bind (KeepsG.freeAll _) fun _ => ?_
  refine KeepsG.bind (openFree_keeps _ _) fun _ => ?_
  refine KeepsG.ite (refuse_keeps _ _) ?_
  refine KeepsG.bind (cut_keeps _ _ _) fun _ => ?_
  exact KeepsG.bind (KeepsG.freeAll _) fun _ => KeepsG.pure _

include hcv in
/-- **Op 51 reads each slot once, from the supply** (for any curve parameter that does). -/
theorem session_once (U : List Nat) (a : Arrival) (sp : SessionPublic) (ss : SessionSecrets) :
    OnceG U (session cv loaded a sp ss) := by
  unfold session
  dsimp only
  refine OnceG.bind (hcv.baseCheck U _) fun r => ?_
  obtain ⟨bv, tx, ty⟩ := r
  dsimp only
  refine OnceG.bind (OnceG.of_keeps (toWord_keeps _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (toWord_keeps _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (toWord_keeps _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (KeepsG.freeFields _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (inputA_keeps _ _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (publicBits_keeps _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (publicBits_keeps _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (publicBits_keeps _)) fun _ => ?_
  refine OnceG.bind (hcv.agree U _) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (KeepsG.freeFields _)) fun _ => ?_
  refine OnceG.of_keeps ?_
  refine KeepsG.ite (refuse_keeps _ _) ?_
  refine KeepsG.bind (stage_keeps _ _ _) fun _ => ?_
  refine KeepsG.bind (openFree_keeps _ _) fun _ => ?_
  split
  · exact refuse_keeps _ _
  · split
    · exact refuse_keeps _ _
    · split
      · exact refuse_keeps _ _
      · refine KeepsG.ite (refuse_keeps _ _) ?_
        refine KeepsG.bind (stage_keeps _ _ _) fun _ => ?_
        refine KeepsG.bind (KeepsG.freeAll _) fun _ => ?_
        refine KeepsG.bind (openFree_keeps _ _) fun _ => ?_
        exact sessionRest_keeps loaded _ _ _ _

end Ops

/-! ## The headline theorems -/

/-- From a state whose supply has no slot twice, a run reads each slot at most once, from the supply. -/
theorem reads_of_onceG {α : Type} {g : Gen α} (st : St) (hg : OnceG (supply st) g) (h : (supply st).Nodup) :
    ∀ rs, (readsAlong (g st) rs).Nodup ∧ ∀ x ∈ readsAlong (g st) rs, x ∈ supply st := by
  intro rs
  have := (hg [] st ⟨by simpa using h, fun _ hx => hx⟩).reads List.nodup_nil rs
  simpa using this

/-- **J1 for op 50, joined.** Whatever the replies (so whatever the peer and the engines do), the
field-element slots a run of the joined `openFirst` reads are slots of the supply it started with,
none twice: its two agreements and its `xeddsa-check` read three different slots of fresh
contributions. -/
theorem openFirst_reads_once (sl : Join.AgreeSlots) (pm : Receive.ProgramMasks) (loaded : Bytes → Bool)
    (fi : Receive.FirstIn) (env : BoolH) (size : Nat) (st : St) (h : (supply st).Nodup) :
    ∀ rs, (readsAlong (Receive.openFirst (Join.receiveCurve sl pm) loaded fi env size st) rs).Nodup ∧
      ∀ x ∈ readsAlong (Receive.openFirst (Join.receiveCurve sl pm) loaded fi env size st) rs, x ∈ supply st :=
  reads_of_onceG st (openFirst_once _ (receiveCurve_once sl pm) loaded _ fi env size) h

/-- **J1 for op 51, joined**: the same for the session (`xeddsa-recover`, `receive-torsion`, the six
or seven agreements). -/
theorem session_reads_once (sl : Join.AgreeSlots) (pm : Receive.ProgramMasks) (loaded : Bytes → Bool)
    (a : Receive.Arrival) (sp : Receive.SessionPublic) (ss : Receive.SessionSecrets) (st : St)
    (h : (supply st).Nodup) :
    ∀ rs, (readsAlong (Receive.session (Join.receiveCurve sl pm) loaded a sp ss st) rs).Nodup ∧
      ∀ x ∈ readsAlong (Receive.session (Join.receiveCurve sl pm) loaded a sp ss st) rs, x ∈ supply st :=
  reads_of_onceG st (session_once _ (receiveCurve_once sl pm) loaded _ a sp ss) h

/-! ## S15's curve operations -/

section Refresh

open TlsMpc.Node.Flows.Join

theorem liftG_once (U : List Nat) (pm : Receive.ProgramMasks) (point : BoolH) : OnceG U (liftG pm point) := by
  unfold liftG
  refine OnceG.bind (OnceG.of_keeps (toField_keeps _)) fun u => ?_
  refine OnceG.bind (programStep_once _ _ _ _ _) fun r => ?_
  refine OnceG.of_keeps ?_
  refine KeepsG.bind (toWord_keeps _) fun _ => ?_
  refine KeepsG.bind (toWord_keeps _) fun _ => ?_
  refine KeepsG.bind (toWord_keeps _) fun _ => ?_
  exact KeepsG.bind (KeepsG.freeFields _) fun _ => KeepsG.pure _

theorem checkG_once (U : List Nat) (pm1 pm2 : Receive.ProgramMasks) (x y ec pq : BoolH) :
    OnceG U (checkG pm1 pm2 x y ec pq) := by
  unfold checkG
  refine OnceG.bind (OnceG.of_keeps (toField_keeps _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (toField_keeps _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (toFieldBits_keeps _ _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (toFieldBits_keeps _ _)) fun _ => ?_
  refine OnceG.bind (OnceG.bind (programStep_once _ _ _ _ _) fun _ => OnceG.pure _) fun _ => ?_
  refine OnceG.bind (OnceG.bind (programStep_once _ _ _ _ _) fun _ => OnceG.pure _) fun _ => ?_
  refine OnceG.of_keeps ?_
  refine KeepsG.bind (toWord_keeps _) fun _ => ?_
  refine KeepsG.bind (toWord_keeps _) fun _ => ?_
  refine KeepsG.bind (toWord_keeps _) fun _ => ?_
  refine KeepsG.bind (toWord_keeps _) fun _ => ?_
  exact KeepsG.bind (KeepsG.freeFields _) fun _ => KeepsG.pure _

theorem optField_keeps (o : Option BoolH) : KeepsG (optField o) := by
  cases o with
  | none => exact KeepsG.pure _
  | some o => exact KeepsG.bind (toField_keeps _) fun _ => KeepsG.pure _

theorem agreeG_once (U : List Nat) (sl : AgreeSlots) (ip sp : BoolH) (o : Option BoolH) :
    OnceG U (agreeG sl ip sp o) := by
  unfold agreeG
  refine OnceG.bind (OnceG.of_keeps (toField_keeps _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (toField_keeps _)) fun _ => ?_
  refine OnceG.bind (OnceG.of_keeps (optField_keeps _)) fun _ => ?_
  refine OnceG.bind (receiveAgree_once U sl _) fun _ => ?_
  exact OnceG.of_keeps (KeepsG.bind (KeepsG.freeFields _) fun _ => KeepsG.pure _)

theorem runAt_reads {α : Type} {g : Gen α} (c : Counters) (pool : Conv.MaskPool) (slots : List (Nat × Nat))
    (hg : OnceG (slots.map Prod.fst) g) (h : (slots.map Prod.fst).Nodup) :
    ∀ rs, (readsAlong (runAt c pool slots g) rs).Nodup ∧
      ∀ x ∈ readsAlong (runAt c pool slots g) rs, x ∈ slots.map Prod.fst := by
  intro rs
  have h0 := hg [] { table := { ctr := c }, pool := pool, slots := slots } ⟨by simpa [supply] using h, fun _ hx => hx⟩
  have h1 : Once (slots.map Prod.fst) (fun (_ : List Nat) (_ : α) => True) [] (runAt c pool slots g) := by
    unfold runAt
    exact h0.bind fun _ _ _ => Once.done trivial
  have := h1.reads List.nodup_nil rs
  simpa using this

/-- **J1 for S15's joined curve operations**: each of `lift`, `check` and `agree` reads only slots of
its own supply (`liftSlots`, `checkSlots`, `agreeSlots`), none twice, on every run. -/
theorem refreshOps_reads_once (rc : RefreshCurve) (c : Counters) :
    ((rc.liftSlots.map Prod.fst).Nodup → ∀ p rs,
      (readsAlong ((refreshOps rc).lift c p) rs).Nodup ∧
        ∀ x ∈ readsAlong ((refreshOps rc).lift c p) rs, x ∈ rc.liftSlots.map Prod.fst) ∧
    ((rc.checkSlots.map Prod.fst).Nodup → ∀ x y ec pq rs,
      (readsAlong ((refreshOps rc).check c x y ec pq) rs).Nodup ∧
        ∀ s ∈ readsAlong ((refreshOps rc).check c x y ec pq) rs, s ∈ rc.checkSlots.map Prod.fst) ∧
    ((rc.agreeSlots.map Prod.fst).Nodup → ∀ ip sp o rs,
      (readsAlong ((refreshOps rc).agree c ip sp o) rs).Nodup ∧
        ∀ s ∈ readsAlong ((refreshOps rc).agree c ip sp o) rs, s ∈ rc.agreeSlots.map Prod.fst) :=
  ⟨fun h p => runAt_reads c _ _ (liftG_once _ rc.recover p) h,
   fun h x y ec pq => runAt_reads c _ _ (checkG_once _ rc.check1 rc.check2 x y ec pq) h,
   fun h ip sp o => runAt_reads c _ _ (agreeG_once _ rc.agree ip sp o) h⟩

end Refresh

end TlsMpc.Node.Flows.JoinOnce
