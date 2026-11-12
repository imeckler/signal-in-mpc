import TlsMpc.Node.Flows.Contacts

/-!
# The contact table: `Contacts.key/seal/open/openDevices/evict/assign` (ops 36, 38, 37, 63, 40, 52)

REORGANIZATION_PLAN.md stage S9. The C++ keeps `std::map<ContactId, Conversation>` inside the
worker (`service_kernels.h` line 144): per contact the storage key's wires, the loaded state's
wires (a record, or a device list), and derived caches (recipient point, static agreement, offset
table). Here that table is LEAN-SIDE PUBLIC STATE: contact ids, handle ids, sizes and device kinds
are all public (handles carry no bytes; the kinds are stored in the clear and every send's length
shows them, `PublicServiceController.lean` line 435). The wires themselves stay in the engines'
handle table (Rust `handles.rs`).

Each operation is a `Step`: the script both parties run (agreed batch by batch), and the table it
leaves once the script returned. Arguments the C++ refuses with `need(...)` (the session ends)
make the script abort here. The table carries the session's handle counters (`Counters`,
Engine.lean); each step allocates its block of handle ids from them (`Table.alloc`), and
`Table.next` is the next free Boolean id.

  op 36 `opKey`: frees the contact's previous key (the C++ overwrote it), then `keyScript`; the
    entry (created if absent, as `conversations[id]` does) gets the new key.
  op 38 `opSeal`: needs key and state; `sealScript` on them. Reply check ‖ ciphertext.
  op 37 / op 63 `opOpen`: needs key and no state; `kinds` [0] and 319 bytes for op 37, a device
    list for op 63 (1 to 6 kinds, each 0, 1 or 2; the ciphertext 319 bytes per device, plus 1616
    for kinds 1 and 2, `service_kernels.h` line 986). Frees the derived caches (the C++ reset
    them), then `openScript`. Accepted: the state is the opened content as ONE handle with its kinds;
    the per-device split of the C++ (`content.slice` per device) is public arithmetic on the kinds
    that a later flow performs with `slice` when it needs a device's record (`deviceSpans`). The
    seal of op 38 then seals exactly this content, as the C++'s `entries(c)` does (the devices'
    records in order, each followed by its pending block if any).
  op 40 `opEvict`: the entry must exist; frees key, state and caches; the entry stays, empty.
  op 52 `opAssign`: the entry `from` must exist and is removed; if `to` exists the moved entry's
    handles are freed and the reply is false (the C++ replies 0 and drops it), otherwise it is
    entered under `to` and the reply is true.

PROVED: T3 for each step against any adversary (`opKey_disclosure`, `opSeal_disclosure`,
`opOpen_disclosure`, `opEvict_disclosure`, `opAssign_disclosure`): key, evict and assign release
nothing; seal releases at most the sealed blob of the entry's key and state; open at most the
`accepted` byte. `frees_wf`: freeing a duplicate-free list of live handles is well formed.
In the reveal list's vocabulary (Engine/Reveal.lean): `opKey_reveals`, `opSeal_reveals`,
`opOpen_reveals`, `opEvict_reveals`, `opAssign_reveals` (the kinds each step declares: none,
`sealedBlob`, `blobAccepted`, none, none) and `opSeal_viewD_kinds`, `opOpen_viewD_kinds`.
THE TABLE INVARIANT `Table.Inv c t` (in the shell's context `c`): the counter is fresh (no id
from `t.next` on was ever defined), contact ids are distinct, each entry's handles are distinct
and no handle belongs to two entries, every table handle is below the counter and live, keys have
the key's marks (480 private bits), states the marks of their size (8·size private bits) and
valid device kinds. `Table.Inv.empty`: it holds at session start. Every step preserves it:
`opKey_inv`, `opSeal_inv`, `opOpen_inv`, `opEvict_inv`, `opAssign_inv` (the step's script is well
formed from `c`, and at every leaf the invariant holds for the table it commits, in the context
the script left); so `opKey_wf`, `opSeal_wf`, `opOpen_wf`, `opAssign_wf` (and `opEvict_wf`).
-/

namespace TlsMpc.Node.Flows.Contacts

open TlsMpc.Node.Engine

/-- One contact's entry. `size`: the state's byte length; `kinds`: its device kinds. -/
structure Entry where
  key : Option BoolH := none
  state : Option BoolH := none
  size : Nat := 0
  kinds : List Nat := []
  derived : List BoolH := []

/-- Every handle the entry holds. -/
def Entry.handles (e : Entry) : List BoolH := e.key.toList ++ e.state.toList ++ e.derived

/-- The contact table (public) and the session's handle counters. -/
structure Table where
  entries : List (Nat × Entry) := []
  ctr : Counters := {}

/-- An operation: the script both parties run, and the table after it. -/
structure Step (α : Type) where
  script : Script α
  commit : α → Table

namespace Table
/-- The session's next free Boolean handle id. -/
def next (t : Table) : Nat := t.ctr.bool
def find? (t : Table) (id : Nat) : Option Entry := t.entries.lookup id
def put (t : Table) (id : Nat) (e : Entry) : Table :=
  { t with entries := (id, e) :: t.entries.filter (·.1 != id) }
def erase (t : Table) (id : Nat) : Table := { t with entries := t.entries.filter (·.1 != id) }
/-- A block of `k` Boolean handle ids from the session counter (`Counters.allocB`): its first id,
and the table with the counter past the block. -/
def alloc (t : Table) (k : Nat) : Nat × Table := ((t.ctr.allocB k).1, { t with ctr := (t.ctr.allocB k).2 })

@[simp] theorem alloc_fst (t : Table) (k : Nat) : (t.alloc k).1 = t.next := rfl
@[simp] theorem next_alloc (t : Table) (k : Nat) : (t.alloc k).2.next = t.next + k := rfl
@[simp] theorem entries_alloc (t : Table) (k : Nat) : (t.alloc k).2.entries = t.entries := rfl
@[simp] theorem next_put (t : Table) (id : Nat) (e : Entry) : (t.put id e).next = t.next := rfl
@[simp] theorem next_erase (t : Table) (id : Nat) : (t.erase id).next = t.next := rfl
end Table

/-- The stored size of a device of kind `k` (`service_kernels.h`: CONTACT 319, PENDING 1616). -/
def deviceBytes (k : Nat) : Nat := if k = 0 then 319 else 319 + 1616

def kindsOk (kinds : List Nat) (size : Nat) : Prop :=
  kinds ≠ [] ∧ kinds.length ≤ 6 ∧ (∀ k ∈ kinds, k ≤ 2) ∧ size = (kinds.map deviceBytes).sum

instance (kinds : List Nat) (size : Nat) : Decidable (kindsOk kinds size) := by
  unfold kindsOk; infer_instance

/-- Byte spans of each device's record and pending block inside a device list's content. -/
def deviceSpans : Nat → List Nat → List ((Nat × Nat) × Option (Nat × Nat))
  | _, [] => []
  | at_, k :: ks =>
    if k = 0 then ((at_, 319), none) :: deviceSpans (at_ + 319) ks
    else ((at_, 319), some (at_ + 319, 1616)) :: deviceSpans (at_ + 319 + 1616) ks

/-- **Op 36.** -/
def opKey (t : Table) (id slot : Nat) : Step BoolH :=
  let e := (t.find? id).getD {}
  { script := seqs (frees e.key.toList) (keyScript (t.alloc 4).1 slot)
    commit := fun h => (t.alloc 4).2.put id { e with key := some h } }

/-- **Op 38.** Reply: check ‖ ciphertext. -/
def opSeal (t : Table) (id : Nat) (version : B8) : Step B8 :=
  match t.find? id with
  | some e =>
    match e.key, e.state with
    | some k, some s => { script := sealScript (t.alloc 3).1 k s e.size version, commit := fun _ => (t.alloc 3).2 }
    | _, _ => { script := .abort "contact seal unavailable", commit := fun _ => t }
  | none => { script := .abort "contact seal unavailable", commit := fun _ => t }

/-- **Ops 37 and 63.** Reply: whether the state was loaded (the C++'s 255 / 0). -/
def opOpen (t : Table) (id : Nat) (kinds : List Nat) (version check ct : B8) : Step (Option BoolH) :=
  match t.find? id with
  | some e =>
    match e.key, e.state with
    | some k, none =>
      if kindsOk kinds ct.length then
        { script := seqs (frees e.derived) (openScript (t.alloc 5).1 k version check ct)
          commit := fun r =>
            match r with
            | some h => (t.alloc 5).2.put id { e with state := some h, size := ct.length, kinds := kinds, derived := [] }
            | none => (t.alloc 5).2.put id { e with derived := [] } }
      else { script := .abort "contact open unavailable", commit := fun _ => t }
    | _, _ => { script := .abort "contact open unavailable", commit := fun _ => t }
  | none => { script := .abort "contact open unavailable", commit := fun _ => t }

/-- **Op 40.** -/
def opEvict (t : Table) (id : Nat) : Step Unit :=
  match t.find? id with
  | some e => { script := seqs (frees e.handles) (.done ()), commit := fun _ => t.put id {} }
  | none => { script := .abort "contact evict unavailable", commit := fun _ => t }

/-- **Op 52.** Reply: whether the contact now has the id `to`. -/
def opAssign (t : Table) (fromId toId : Nat) : Step Bool :=
  match t.find? fromId with
  | some e =>
    let t' := t.erase fromId
    match t'.find? toId with
    | some _ => { script := seqs (frees e.handles) (.done false), commit := fun _ => t' }
    | none => { script := .done true, commit := fun _ => t'.put toId e }
  | none => { script := .abort "contact assign unavailable", commit := fun _ => t }

/-! ## T3 per operation -/

section Disclosure

variable (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)

theorem frees_plain (hs : List BoolH) : ∀ i ∈ frees hs, plain i = true := by
  intro i hi
  simp only [frees, List.mem_map] at hi
  obtain ⟨h, -, rfl⟩ := hi
  rfl

theorem frees_silent (hs : List BoolH) : ∀ i ∈ frees hs, i.label? = none := by
  intro i hi
  simp only [frees, List.mem_map] at hi
  obtain ⟨h, -, rfl⟩ := hi
  rfl

/-- Freeing handles other than `x` leaves `x`'s value. -/
theorem runPlain_frees (x : Nat) : ∀ (hs : List BoolH) (I I' : Ideal), runPlain E (frees hs) I = some I' →
    (∀ h ∈ hs, h.id ≠ x) → I'.bools x = I.bools x
  | [], I, I', hr, _ => by
    simp only [frees, List.map_nil, runPlain, Option.some.injEq] at hr
    subst hr
    rfl
  | h :: hs, I, I', hr, hne => by
    simp only [frees, List.map_cons, runPlain, plainStep, idealStep, blankWire, InstrP.map] at hr
    rw [runPlain_frees x hs _ I' hr (fun g hg => hne g (by simp [hg]))]
    have hx : x ≠ h.id := fun e => hne h (by simp) e.symm
    simp [Ideal.dropBool, hx]

/-- **T3 for op 36.** Nothing is released. -/
theorem opKey_disclosure (t : Table) (id slot : Nat) :
    (withAdv E me adv (opKey t id slot).script σ I vD).viewD = [] ∧
      (withAdv E me adv (opKey t id slot).script σ I vD).viewH = [] :=
  silent_view E me adv _ (Silent.seqs (keyScript_silent _ _) _ (frees_silent _)) σ I vD

/-- **T3 for op 40.** Nothing is released. -/
theorem opEvict_disclosure (t : Table) (id : Nat) :
    (withAdv E me adv (opEvict t id).script σ I vD).viewD = [] ∧
      (withAdv E me adv (opEvict t id).script σ I vD).viewH = [] := by
  unfold opEvict
  split
  · exact silent_view E me adv _ (Silent.seqs (Silent.done _) _ (frees_silent _)) σ I vD
  · exact silent_view E me adv _ (Silent.abort _) σ I vD

/-- **T3 for op 52.** Nothing is released. -/
theorem opAssign_disclosure (t : Table) (fromId toId : Nat) :
    (withAdv E me adv (opAssign t fromId toId).script σ I vD).viewD = [] ∧
      (withAdv E me adv (opAssign t fromId toId).script σ I vD).viewH = [] := by
  unfold opAssign
  split
  · simp only
    split
    · exact silent_view E me adv _ (Silent.seqs (Silent.done _) _ (frees_silent _)) σ I vD
    · exact silent_view E me adv _ (Silent.done _) σ I vD
  · exact silent_view E me adv _ (Silent.abort _) σ I vD

/-- **T3 for op 38.** At most the sealed blob of the entry's key and state handles. -/
theorem opSeal_disclosure (hE : Loaded E) (t : Table) (id : Nat) (version : B8) (e : Entry) (k s : BoolH)
    (kv sv : Bits) (he : t.find? id = some e) (hk : e.key = some k) (hs : e.state = some s)
    (hkn : k.id < t.next) (hsn : s.id < t.next) (hkv : I.bools k.id = some kv) (hsv : I.bools s.id = some sv) :
    (withAdv E me adv (opSeal t id version).script σ I vD).viewD <+:
      [⟨sealedBlob, .bits (bitsOf (kernelOut (HybridKernel.contactSeal e.size) (bytesOf (kv ++ (bitsOf version ++ sv)))))⟩] := by
  simp only [opSeal, he, hk, hs]
  exact seal_disclosure E me adv σ I vD hE t.next k s e.size version kv sv hkn hsn hkv hsv

/-- **T3 for ops 37 and 63.** At most the `accepted` byte (see `open_released_byte`). The derived
caches freed first release nothing. -/
theorem opOpen_disclosure (hE : Loaded E) (t : Table) (id : Nat) (kinds : List Nat) (version check ct : B8)
    (e : Entry) (k : BoolH) (kv : Bits) (he : t.find? id = some e) (hk : e.key = some k) (hs : e.state = none)
    (hkn : k.id < t.next) (hkv : I.bools k.id = some kv)
    (hd : ∀ h ∈ e.derived, h.id ≠ k.id) :
    (withAdv E me adv (opOpen t id kinds version check ct).script σ I vD).viewD <+:
      [⟨blobAccepted, .bits ((bitsOf (kernelOut (HybridKernel.contactOpen ct.length)
        (bytesOf (kv ++ bitsOf (version ++ ct ++ check))))).take 8)⟩] := by
  simp only [opOpen, he, hk, hs]
  split
  · refine viewD_seqs E me adv _ σ _ _ (frees_plain _) I vD (fun I' hI' => ?_)
    -- freeing the caches leaves the key's value
    have hkv' : I'.bools k.id = some kv := by
      rw [runPlain_frees E k.id e.derived I I' hI' hd, hkv]
    exact open_disclosure E me adv σ I' vD hE t.next k version check ct kv hkn hkv'
  · simp [withAdv]

/-! ### The same in the reveal list's vocabulary (Engine/Reveal.lean): the kinds each step declares -/

theorem opKey_reveals (t : Table) (id slot : Nat) : Reveals keyKinds (opKey t id slot).script :=
  (Silent.seqs (keyScript_silent _ _) _ (frees_silent _)).reveals _

theorem opSeal_reveals (t : Table) (id : Nat) (version : B8) : Reveals sealKinds (opSeal t id version).script := by
  unfold opSeal
  split
  · split
    · exact sealScript_reveals _ _ _ _ _
    · exact Every.abort _
  · exact Every.abort _

theorem opOpen_reveals (t : Table) (id : Nat) (kinds : List Nat) (version check ct : B8) :
    Reveals openKinds (opOpen t id kinds version check ct).script := by
  unfold opOpen
  split
  · split
    · split
      · exact every_seqs (openScript_reveals _ _ _ _ _) _ (labelIn_of_none (frees_silent _))
      · exact Every.abort _
    · exact Every.abort _
  · exact Every.abort _

theorem opEvict_reveals (t : Table) (id : Nat) : Reveals [] (opEvict t id).script := by
  unfold opEvict
  split
  · exact (Silent.seqs (Silent.done _) _ (frees_silent _)).reveals _
  · exact Every.abort _

theorem opAssign_reveals (t : Table) (fromId toId : Nat) : Reveals [] (opAssign t fromId toId).script := by
  unfold opAssign
  split
  · simp only
    split
    · exact (Silent.seqs (Silent.done _) _ (frees_silent _)).reveals _
    · exact Every.done _
  · exact Every.abort _

/-- **T3 for op 38 on the table, in the reveal list's vocabulary**: only `ofKind .sealedBlob`. -/
theorem opSeal_viewD_kinds (t : Table) (id : Nat) (version : B8) :
    ∀ r ∈ (withAdv E me adv (opSeal t id version).script σ I vD).viewD, ∃ k ∈ sealKinds, r.label = Label.ofKind k :=
  viewD_kinds E me adv _ _ (opSeal_reveals t id version) σ I vD

/-- **T3 for ops 37 and 63 on the table, in the reveal list's vocabulary**: only `ofKind .blobAccepted`. -/
theorem opOpen_viewD_kinds (t : Table) (id : Nat) (kinds : List Nat) (version check ct : B8) :
    ∀ r ∈ (withAdv E me adv (opOpen t id kinds version check ct).script σ I vD).viewD,
      ∃ k ∈ openKinds, r.label = Label.ofKind k :=
  viewD_kinds E me adv _ _ (opOpen_reveals t id kinds version check ct) σ I vD

end Disclosure

/-! ## Well-formedness of the frees -/

theorem frees_wf {α : Type} (sigs : Bytes → Option Sig) (a : α) :
    ∀ (hs : List BoolH) (c : Ctx), (hs.map (·.id)).Nodup → (∀ h ∈ hs, (c.bool? h).isSome = true) →
      WF sigs c (seqs (frees hs) (.done a))
  | [], c, _, _ => WF.done _ _
  | h :: hs, c, hn, hl => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    refine WF_seq sigs c _ _ _ (check_freeBool' sigs (hl h (by simp))) ?_
    refine frees_wf sigs a hs _ hn.2 (fun g hg => ?_)
    have hne : g.id ≠ h.id := fun e => hn.1 ⟨g, hg, e⟩
    rw [bool?_drop_of_ne _ _ _ hne]
    exact hl g (by simp [hg])

/-- Op 40 is well formed when the entry's handles are live and distinct. -/
theorem opEvict_wf (sigs : Bytes → Option Sig) (c : Ctx) (t : Table) (id : Nat) (e : Entry)
    (he : t.find? id = some e) (hn : (e.handles.map (·.id)).Nodup)
    (hl : ∀ h ∈ e.handles, (c.bool? h).isSome = true) : WF sigs c (opEvict t id).script := by
  simp only [opEvict, he]
  exact frees_wf sigs () e.handles c hn hl

/-! ## The table invariant, preserved by every step -/

/-- The signatures of the contact kernels, as `check` sees them (`Loaded.sigsOk`). -/
structure SigsOk (sigs : Bytes → Option Sig) : Prop where
  key : sigs keyName = some ⟨512, keyMarks⟩
  sealing : ∀ size, 0 < size → size ≤ 16384 → sigs (sealName size) = some ⟨8 * (68 + size), sealMarks size⟩
  opening : ∀ size, 0 < size → size ≤ 16384 → sigs (openName size) = some ⟨8 * (84 + size), openMarks size⟩

theorem Loaded.sigsOk {E : Env} (hE : Loaded E) : SigsOk E.sigs :=
  ⟨hE.sigs_key, hE.sigs_seal, hE.sigs_open⟩

theorem Entry.mem_key {e : Entry} {k : BoolH} (h : e.key = some k) : k ∈ e.handles := by
  simp [Entry.handles, h]

theorem Entry.mem_state {e : Entry} {s : BoolH} (h : e.state = some s) : s ∈ e.handles := by
  simp [Entry.handles, h]

/-- **The table invariant** in the shell's context `c` (see the header). -/
structure Table.Inv (c : Ctx) (t : Table) : Prop where
  fresh : Fresh c t.next
  ids : (t.entries.map (·.1)).Nodup
  nodup : ∀ p ∈ t.entries, (p.2.handles.map (·.id)).Nodup
  sep : ∀ p ∈ t.entries, ∀ q ∈ t.entries, ∀ h ∈ p.2.handles, ∀ g ∈ q.2.handles, h.id = g.id → p.1 = q.1
  below : ∀ p ∈ t.entries, ∀ h ∈ p.2.handles, h.id < t.next
  live : ∀ p ∈ t.entries, ∀ h ∈ p.2.handles, (c.bool? h).isSome = true
  key : ∀ p ∈ t.entries, ∀ k, p.2.key = some k → c.bool? k = some ⟨keyMarks, false⟩
  state : ∀ p ∈ t.entries, ∀ s, p.2.state = some s →
    c.bool? s = some ⟨List.replicate (8 * p.2.size) .never, false⟩ ∧ kindsOk p.2.kinds p.2.size

theorem Table.mem_put {t : Table} {id : Nat} {e : Entry} {p : Nat × Entry} :
    p ∈ (t.put id e).entries ↔ p = (id, e) ∨ (p ∈ t.entries ∧ p.1 ≠ id) := by
  simp [Table.put, List.mem_filter]

theorem Table.mem_erase {t : Table} {id : Nat} {p : Nat × Entry} :
    p ∈ (t.erase id).entries ↔ p ∈ t.entries ∧ p.1 ≠ id := by
  simp [Table.erase, List.mem_filter]

theorem lookup_mem {id : Nat} {e : Entry} : ∀ {l : List (Nat × Entry)}, l.lookup id = some e → (id, e) ∈ l
  | [], h => by simp [List.lookup] at h
  | (a, b) :: l, h => by
    by_cases hk : id = a
    · subst hk
      simp [List.lookup] at h
      subst h
      simp
    · have hb : (id == a) = false := by simpa using hk
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem Table.find_mem {t : Table} {id : Nat} {e : Entry} (h : t.find? id = some e) : (id, e) ∈ t.entries :=
  lookup_mem h

namespace Table.Inv

/-- Handles of different entries have different ids. -/
theorem ne_of_other {c : Ctx} {t : Table} (hI : t.Inv c) {p q : Nat × Entry} (hp : p ∈ t.entries)
    (hq : q ∈ t.entries) (hne : p.1 ≠ q.1) {h g : BoolH} (hh : h ∈ p.2.handles) (hg : g ∈ q.2.handles) :
    h.id ≠ g.id :=
  fun e => hne (hI.sep p hp q hq h hh g hg e)

/-- At session start (empty context, empty table). -/
theorem empty : Table.Inv {} {} where
  fresh := fun _ _ h => by simp at h
  ids := by simp
  nodup := by simp
  sep := by simp
  below := by simp
  live := by simp
  key := by simp
  state := by simp

/-- **Entry `id` replaced by `e'`**, in a context `c'` that keeps the other entries' handles and
gives `e'`'s handles the invariant's facts. -/
theorem put {c c' : Ctx} {t t' : Table} {id : Nat} {e' : Entry} (hI : t.Inv c)
    (he : t'.entries = t.entries) (hn : t.next ≤ t'.next) (hf : Fresh c' t'.next)
    (hold : ∀ p ∈ t.entries, p.1 ≠ id → ∀ g ∈ p.2.handles, c'.bool? g = c.bool? g)
    (hsep : ∀ h ∈ e'.handles, ∀ p ∈ t.entries, p.1 ≠ id → ∀ g ∈ p.2.handles, g.id ≠ h.id)
    (hbelow : ∀ h ∈ e'.handles, h.id < t'.next)
    (hnd : (e'.handles.map (·.id)).Nodup)
    (hlive : ∀ h ∈ e'.handles, (c'.bool? h).isSome = true)
    (hkey : ∀ k, e'.key = some k → c'.bool? k = some ⟨keyMarks, false⟩)
    (hstate : ∀ s, e'.state = some s →
      c'.bool? s = some ⟨List.replicate (8 * e'.size) .never, false⟩ ∧ kindsOk e'.kinds e'.size) :
    (t'.put id e').Inv c' where
  fresh := hf
  ids := by
    simp only [Table.put, List.map_cons, List.nodup_cons, he]
    refine ⟨by simp [List.mem_filter], ?_⟩
    exact hI.ids.sublist ((List.filter_sublist).map _)
  nodup := by
    intro p hp
    rcases Table.mem_put.mp hp with rfl | ⟨hp, _⟩
    · exact hnd
    · rw [he] at hp
      exact hI.nodup p hp
  sep := by
    intro p hp q hq h hh g hg hhg
    rcases Table.mem_put.mp hp with rfl | ⟨hp, hpi⟩ <;> rcases Table.mem_put.mp hq with rfl | ⟨hq, hqi⟩
    · rfl
    · rw [he] at hq
      exact absurd hhg.symm (hsep h hh q hq hqi g hg)
    · rw [he] at hp
      exact absurd hhg (hsep g hg p hp hpi h hh)
    · rw [he] at hp hq
      exact hI.sep p hp q hq h hh g hg hhg
  below := by
    intro p hp h hh
    rcases Table.mem_put.mp hp with rfl | ⟨hp, _⟩
    · exact hbelow h hh
    · rw [he] at hp
      exact Nat.lt_of_lt_of_le (hI.below p hp h hh) hn
  live := by
    intro p hp h hh
    rcases Table.mem_put.mp hp with rfl | ⟨hp, hpi⟩
    · exact hlive h hh
    · rw [he] at hp
      rw [hold p hp hpi h hh]
      exact hI.live p hp h hh
  key := by
    intro p hp k hk
    rcases Table.mem_put.mp hp with rfl | ⟨hp, hpi⟩
    · exact hkey k hk
    · rw [he] at hp
      rw [hold p hp hpi k (Entry.mem_key hk)]
      exact hI.key p hp k hk
  state := by
    intro p hp s hs
    rcases Table.mem_put.mp hp with rfl | ⟨hp, hpi⟩
    · exact hstate s hs
    · rw [he] at hp
      rw [hold p hp hpi s (Entry.mem_state hs)]
      exact hI.state p hp s hs

/-- **Entry `id` removed.** -/
theorem erase {c c' : Ctx} {t t' : Table} {id : Nat} (hI : t.Inv c)
    (he : t'.entries = t.entries) (hn : t.next ≤ t'.next) (hf : Fresh c' t'.next)
    (hold : ∀ p ∈ t.entries, p.1 ≠ id → ∀ g ∈ p.2.handles, c'.bool? g = c.bool? g) :
    (t'.erase id).Inv c' where
  fresh := hf
  ids := by
    simp only [Table.erase, he]
    exact hI.ids.sublist ((List.filter_sublist).map _)
  nodup := fun p hp => by
    rw [Table.mem_erase, he] at hp
    exact hI.nodup p hp.1
  sep := fun p hp q hq => by
    rw [Table.mem_erase, he] at hp hq
    exact hI.sep p hp.1 q hq.1
  below := fun p hp h hh => by
    rw [Table.mem_erase, he] at hp
    exact Nat.lt_of_lt_of_le (hI.below p hp.1 h hh) hn
  live := fun p hp h hh => by
    rw [Table.mem_erase, he] at hp
    rw [hold p hp.1 hp.2 h hh]
    exact hI.live p hp.1 h hh
  key := fun p hp k hk => by
    rw [Table.mem_erase, he] at hp
    rw [hold p hp.1 hp.2 k (Entry.mem_key hk)]
    exact hI.key p hp.1 k hk
  state := fun p hp s hs => by
    rw [Table.mem_erase, he] at hp
    rw [hold p hp.1 hp.2 s (Entry.mem_state hs)]
    exact hI.state p hp.1 s hs

/-- **Entries unchanged**, the counter advanced, the table's handles kept. -/
theorem keep {c c' : Ctx} {t t' : Table} (hI : t.Inv c)
    (he : t'.entries = t.entries) (hn : t.next ≤ t'.next) (hf : Fresh c' t'.next)
    (hold : ∀ p ∈ t.entries, ∀ g ∈ p.2.handles, c'.bool? g = c.bool? g) : t'.Inv c' where
  fresh := hf
  ids := by rw [he]; exact hI.ids
  nodup := fun p hp => by rw [he] at hp; exact hI.nodup p hp
  sep := fun p hp q hq => by rw [he] at hp hq; exact hI.sep p hp q hq
  below := fun p hp h hh => by rw [he] at hp; exact Nat.lt_of_lt_of_le (hI.below p hp h hh) hn
  live := fun p hp h hh => by rw [he] at hp; rw [hold p hp h hh]; exact hI.live p hp h hh
  key := fun p hp k hk => by
    rw [he] at hp; rw [hold p hp k (Entry.mem_key hk)]; exact hI.key p hp k hk
  state := fun p hp s hs => by
    rw [he] at hp; rw [hold p hp s (Entry.mem_state hs)]; exact hI.state p hp s hs

end Table.Inv

/-- After freeing `hs`, a handle whose id is none of theirs keeps its entry. -/
theorem bool?_after_frees {c c' : Ctx} {hs : List BoolH}
    (h1 : ∀ g : BoolH, c'.bool? g = if g.id ∈ hs.map (·.id) then none else c.bool? g) {g : BoolH}
    (hg : ∀ h ∈ hs, g.id ≠ h.id) : c'.bool? g = c.bool? g := by
  rw [h1 g]
  have : g.id ∉ hs.map (·.id) := by
    simp only [List.mem_map, not_exists, not_and]
    exact fun h hh e => hg h hh e.symm
  simp [this]

/-- **Op 36 preserves the invariant** (and is well formed). -/
theorem opKey_inv (sigs : Bytes → Option Sig) (hs : SigsOk sigs) (c : Ctx) (t : Table) (id slot : Nat)
    (hI : t.Inv c) : WFP sigs (fun c' h => ((opKey t id slot).commit h).Inv c') c (opKey t id slot).script := by
  have hmem : ∀ h ∈ ((t.find? id).getD {}).handles, (id, (t.find? id).getD {}) ∈ t.entries := by
    intro h hh
    cases hf : t.find? id with
    | none => simp [hf, Entry.handles] at hh
    | some e => simpa using Table.find_mem hf
  show WFP sigs (fun c' h => ((t.alloc 4).2.put id { (t.find? id).getD {} with key := some h }).Inv c') c
    (seqs (frees ((t.find? id).getD {}).key.toList) (keyScript (t.alloc 4).1 slot))
  generalize (t.find? id).getD {} = e at hmem ⊢
  -- the entry's handles: the old key, then the rest
  have hnde : ((e.key.toList ++ (e.state.toList ++ e.derived)).map (·.id)).Nodup := by
    by_cases hne : e.handles = []
    · have : e.key.toList ++ (e.state.toList ++ e.derived) = [] := by
        simpa [Entry.handles, List.append_assoc] using hne
      rw [this]
      simp
    · obtain ⟨h, hh⟩ := List.exists_mem_of_ne_nil _ hne
      have := hI.nodup _ (hmem h hh)
      simpa [Entry.handles, List.append_assoc] using this
  rw [List.map_append, List.nodup_append] at hnde
  obtain ⟨hndk, hndr, hdis⟩ := hnde
  have hrest : ∀ h ∈ e.state.toList ++ e.derived, h ∈ e.handles := fun h hh => by
    simp only [Entry.handles, List.mem_append] at hh ⊢
    rcases hh with hh | hh
    · exact Or.inl (Or.inr hh)
    · exact Or.inr hh
  have hkeyh : ∀ h ∈ e.key.toList, h ∈ e.handles := fun h hh => by
    simp only [Entry.handles, List.mem_append]
    exact Or.inl (Or.inl hh)
  refine frees_wfp sigs _ _ c (by simpa using hndk) (fun h hh => hI.live _ (hmem h (hkeyh h hh)) h (hkeyh h hh))
    (fun c1 h1 h2 => ?_)
  refine (keyScript_wfp sigs c1 (t.alloc 4).1 slot (hI.fresh.of_seenB h2) hs.key).mono (fun c2 h hp => ?_)
  obtain ⟨rfl, hk2, hlow, hf2⟩ := hp
  -- a handle below the counter that is not the old key keeps its entry
  have hback : ∀ g : BoolH, g.id < t.next → (∀ k ∈ e.key.toList, g.id ≠ k.id) → c2.bool? g = c.bool? g :=
    fun g hg hk => by rw [hlow g hg, bool?_after_frees h1 hk]
  have hold : ∀ p ∈ t.entries, p.1 ≠ id → ∀ g ∈ p.2.handles, c2.bool? g = c.bool? g := by
    intro p hp hpi g hg
    refine hback g (hI.below p hp g hg) (fun k hk => ?_)
    exact hI.ne_of_other hp (hmem k (hkeyh k hk)) hpi hg (hkeyh k hk)
  have hrestne : ∀ g ∈ e.state.toList ++ e.derived, ∀ k ∈ e.key.toList, g.id ≠ k.id := by
    intro g hg k hk e'
    exact hdis k.id (List.mem_map_of_mem hk) g.id (List.mem_map_of_mem hg) e'.symm
  have hH : ({ e with key := some ⟨(t.alloc 4).1 + 3⟩ } : Entry).handles =
      ⟨(t.alloc 4).1 + 3⟩ :: (e.state.toList ++ e.derived) := by
    simp [Entry.handles]
  refine Table.Inv.put hI rfl (by simp) hf2 hold ?_ ?_ ?_ ?_ ?_ ?_
  · intro h hh p hp hpi g hg
    rw [hH, List.mem_cons] at hh
    rcases hh with rfl | hh
    · have := hI.below p hp g hg
      simp only [Table.alloc_fst]
      omega
    · exact hI.ne_of_other hp (hmem h (hrest h hh)) hpi hg (hrest h hh)
  · intro h hh
    rw [hH, List.mem_cons] at hh
    rcases hh with rfl | hh
    · simp
    · have := hI.below _ (hmem h (hrest h hh)) h (hrest h hh)
      simp only [Table.next_alloc]
      omega
  · rw [hH, List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, hndr⟩
    obtain ⟨g, hg, he⟩ := List.mem_map.mp hm
    have := hI.below _ (hmem g (hrest g hg)) g (hrest g hg)
    simp only [Table.alloc_fst] at he
    omega
  · intro h hh
    rw [hH, List.mem_cons] at hh
    rcases hh with rfl | hh
    · rw [hk2]; rfl
    · rw [hback h (hI.below _ (hmem h (hrest h hh)) h (hrest h hh)) (hrestne h hh)]
      exact hI.live _ (hmem h (hrest h hh)) h (hrest h hh)
  · intro k hk
    simp only [Option.some.injEq] at hk
    subst hk
    exact hk2
  · intro s hs'
    have hs'' : e.state = some s := by simpa using hs'
    have hsm : s ∈ e.state.toList ++ e.derived := by simp [hs'']
    rw [hback s (hI.below _ (hmem s (hrest s hsm)) s (hrest s hsm)) (hrestne s hsm)]
    exact hI.state _ (hmem s (hrest s hsm)) s hs''

theorem opKey_wf (sigs : Bytes → Option Sig) (hs : SigsOk sigs) (c : Ctx) (t : Table) (id slot : Nat)
    (hI : t.Inv c) : WF sigs c (opKey t id slot).script :=
  (opKey_inv sigs hs c t id slot hI).wf

/-- **Op 38 preserves the invariant** (and is well formed). -/
theorem opSeal_inv (sigs : Bytes → Option Sig) (hs : SigsOk sigs) (c : Ctx) (t : Table) (id : Nat)
    (version : B8) (hI : t.Inv c) :
    WFP sigs (fun c' r => ((opSeal t id version).commit r).Inv c') c (opSeal t id version).script := by
  unfold opSeal
  cases hf : t.find? id with
  | none => exact WFP.abort _ _
  | some e =>
    have hm := Table.find_mem hf
    dsimp only
    cases hk : e.key with
    | none => exact WFP.abort _ _
    | some k =>
      cases hst : e.state with
      | none => exact WFP.abort _ _
      | some s =>
        dsimp only
        obtain ⟨hsv, _⟩ := hI.state _ hm s hst
        refine (sealScript_wfp sigs c (t.alloc 3).1 k s e.size version keyMarks _ hI.fresh
          (hI.below _ hm k (Entry.mem_key hk)) (hI.below _ hm s (Entry.mem_state hst)) (hI.key _ hm k hk) hsv
          (by simp only [keyMarks, List.length_replicate]) (by simp only [List.length_replicate])
          (hs.sealing e.size)).mono (fun c' r hp => ?_)
        obtain ⟨hlow, hf'⟩ := hp
        exact Table.Inv.keep hI rfl (by simp) hf' (fun p hp g hg => hlow g (hI.below p hp g hg))

theorem opSeal_wf (sigs : Bytes → Option Sig) (hs : SigsOk sigs) (c : Ctx) (t : Table) (id : Nat)
    (version : B8) (hI : t.Inv c) : WF sigs c (opSeal t id version).script :=
  (opSeal_inv sigs hs c t id version hI).wf

/-- **Ops 37 and 63 preserve the invariant** (and are well formed). -/
theorem opOpen_inv (sigs : Bytes → Option Sig) (hs : SigsOk sigs) (c : Ctx) (t : Table) (id : Nat)
    (kinds : List Nat) (version check ct : B8) (hI : t.Inv c) :
    WFP sigs (fun c' r => ((opOpen t id kinds version check ct).commit r).Inv c') c
      (opOpen t id kinds version check ct).script := by
  unfold opOpen
  cases hf : t.find? id with
  | none => exact WFP.abort _ _
  | some e =>
    have hm := Table.find_mem hf
    dsimp only
    cases hk : e.key with
    | none => exact WFP.abort _ _
    | some k =>
      cases hst : e.state with
      | some s => exact WFP.abort _ _
      | none =>
        dsimp only
        split
        · next hko =>
          have hhe : e.handles = k :: e.derived := by simp [Entry.handles, hk, hst]
          have hnde := hI.nodup _ hm
          simp only [hhe, List.map_cons, List.nodup_cons] at hnde
          have hdm : ∀ h ∈ e.derived, h ∈ e.handles := fun h hh => by rw [hhe]; exact List.mem_cons_of_mem _ hh
          refine frees_wfp sigs _ e.derived c hnde.2 (fun h hh => hI.live _ hm h (hdm h hh)) (fun c1 h1 h2 => ?_)
          have hkd : ∀ h ∈ e.derived, k.id ≠ h.id := fun h hh e' => hnde.1 (e' ▸ List.mem_map_of_mem hh)
          have hkc1 : c1.bool? k = some ⟨keyMarks, false⟩ := by
            rw [bool?_after_frees h1 hkd]
            exact hI.key _ hm k hk
          have hkn : k.id < t.next := hI.below _ hm k (Entry.mem_key hk)
          refine (openScript_wfp sigs c1 (t.alloc 5).1 k version check ct keyMarks (hI.fresh.of_seenB h2) hkn hkc1
            (by simp only [keyMarks, List.length_replicate]) (hs.opening ct.length)).mono (fun c2 r hp => ?_)
          obtain ⟨hlow, hf2, hres⟩ := hp
          have hold : ∀ p ∈ t.entries, p.1 ≠ id → ∀ g ∈ p.2.handles, c2.bool? g = c.bool? g := by
            intro p hp hpi g hg
            rw [hlow g (hI.below p hp g hg)]
            exact bool?_after_frees h1 (fun h hh => hI.ne_of_other hp hm hpi hg (hdm h hh))
          have hk2 : c2.bool? k = some ⟨keyMarks, false⟩ := by rw [hlow k hkn]; exact hkc1
          cases r with
          | some h =>
            obtain ⟨rfl, hs2⟩ := hres h rfl
            dsimp only
            have hH : Entry.handles
                { key := some k, state := some ⟨(t.alloc 5).1 + 4⟩, size := ct.length, kinds := kinds, derived := [] } =
                [k, ⟨(t.alloc 5).1 + 4⟩] := by
              simp [Entry.handles]
            refine Table.Inv.put hI rfl (by simp) hf2 hold ?_ ?_ ?_ ?_ ?_ ?_
            · intro h hh p hp hpi g hg
              rw [hH] at hh
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
              rcases hh with rfl | rfl
              · exact hI.ne_of_other hp hm hpi hg (Entry.mem_key hk)
              · have := hI.below p hp g hg
                simp only [Table.alloc_fst]
                omega
            · intro h hh
              rw [hH] at hh
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
              simp only [Table.next_alloc]
              rcases hh with rfl | rfl
              · omega
              · simp
            · rw [hH]
              simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
                or_false, List.nodup_nil, not_false_eq_true, and_true, Table.alloc_fst]
              omega
            · intro h hh
              rw [hH] at hh
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
              rcases hh with rfl | rfl
              · rw [hk2]; rfl
              · rw [hs2]; rfl
            · intro k' hk'
              simp only [Option.some.injEq] at hk'
              subst hk'
              exact hk2
            · intro s hs'
              simp only [Option.some.injEq] at hs'
              subst hs'
              exact ⟨hs2, hko⟩
          | none =>
            dsimp only
            have hH : Entry.handles
                { key := some k, state := none, size := e.size, kinds := e.kinds, derived := [] } = [k] := by
              simp [Entry.handles]
            refine Table.Inv.put hI rfl (by simp) hf2 hold ?_ ?_ ?_ ?_ ?_ ?_
            · intro h hh p hp hpi g hg
              rw [hH] at hh
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
              subst hh
              exact hI.ne_of_other hp hm hpi hg (Entry.mem_key hk)
            · intro h hh
              rw [hH] at hh
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
              subst hh
              simp only [Table.next_alloc]
              omega
            · rw [hH]
              simp
            · intro h hh
              rw [hH] at hh
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
              subst hh
              rw [hk2]; rfl
            · intro k' hk'
              simp only [Option.some.injEq] at hk'
              subst hk'
              exact hk2
            · intro s hs'
              simp at hs'
        · exact WFP.abort _ _

theorem opOpen_wf (sigs : Bytes → Option Sig) (hs : SigsOk sigs) (c : Ctx) (t : Table) (id : Nat)
    (kinds : List Nat) (version check ct : B8) (hI : t.Inv c) :
    WF sigs c (opOpen t id kinds version check ct).script :=
  (opOpen_inv sigs hs c t id kinds version check ct hI).wf

/-- **Op 40 preserves the invariant.** -/
theorem opEvict_inv (sigs : Bytes → Option Sig) (c : Ctx) (t : Table) (id : Nat) (hI : t.Inv c) :
    WFP sigs (fun c' r => ((opEvict t id).commit r).Inv c') c (opEvict t id).script := by
  unfold opEvict
  cases hf : t.find? id with
  | none => exact WFP.abort _ _
  | some e =>
    have hm := Table.find_mem hf
    dsimp only
    refine frees_wfp sigs _ e.handles c (hI.nodup _ hm) (fun h hh => hI.live _ hm h hh)
      (fun c1 h1 h2 => WFP.done _ _ ?_)
    refine Table.Inv.put hI rfl (Nat.le_refl _) (hI.fresh.of_seenB h2) (fun p hp hpi g hg => ?_)
      (by simp [Entry.handles]) (by simp [Entry.handles]) (by simp [Entry.handles]) (by simp [Entry.handles])
      (by simp) (by simp)
    exact bool?_after_frees h1 (fun h hh => hI.ne_of_other hp hm hpi hg hh)

/-- **Op 52 preserves the invariant** (and is well formed). -/
theorem opAssign_inv (sigs : Bytes → Option Sig) (c : Ctx) (t : Table) (fromId toId : Nat) (hI : t.Inv c) :
    WFP sigs (fun c' r => ((opAssign t fromId toId).commit r).Inv c') c (opAssign t fromId toId).script := by
  unfold opAssign
  cases hf : t.find? fromId with
  | none => exact WFP.abort _ _
  | some e =>
    have hm := Table.find_mem hf
    dsimp only
    cases ht : (t.erase fromId).find? toId with
    | some _ =>
      dsimp only
      refine frees_wfp sigs _ e.handles c (hI.nodup _ hm) (fun h hh => hI.live _ hm h hh)
        (fun c1 h1 h2 => WFP.done _ _ ?_)
      exact Table.Inv.erase hI rfl (Nat.le_refl _) (hI.fresh.of_seenB h2)
        (fun p hp hpi g hg => bool?_after_frees h1 (fun h hh => hI.ne_of_other hp hm hpi hg hh))
    | none =>
      dsimp only
      refine WFP.done _ _ ?_
      have hI1 : (t.erase fromId).Inv c := Table.Inv.erase hI rfl (Nat.le_refl _) hI.fresh (fun _ _ _ _ _ => rfl)
      refine Table.Inv.put hI1 rfl (Nat.le_refl _) hI.fresh (fun _ _ _ _ _ => rfl) ?_ (hI.below _ hm)
        (hI.nodup _ hm) (hI.live _ hm) (hI.key _ hm) (hI.state _ hm)
      intro h hh p hp hpi g hg
      rw [Table.mem_erase] at hp
      exact hI.ne_of_other hp.1 hm hp.2 hg hh

theorem opAssign_wf (sigs : Bytes → Option Sig) (c : Ctx) (t : Table) (fromId toId : Nat) (hI : t.Inv c) :
    WF sigs c (opAssign t fromId toId).script :=
  (opAssign_inv sigs c t fromId toId hI).wf

end TlsMpc.Node.Flows.Contacts
