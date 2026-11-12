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
make the script abort here. The session's next free Boolean handle id is `Table.next`.

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

/-- The contact table (public) and the session's next free Boolean handle id. -/
structure Table where
  entries : List (Nat × Entry) := []
  next : Nat := 0

/-- An operation: the script both parties run, and the table after it. -/
structure Step (α : Type) where
  script : Script α
  commit : α → Table

namespace Table
def find? (t : Table) (id : Nat) : Option Entry := t.entries.lookup id
def put (t : Table) (id : Nat) (e : Entry) : Table :=
  { t with entries := (id, e) :: t.entries.filter (·.1 != id) }
def erase (t : Table) (id : Nat) : Table := { t with entries := t.entries.filter (·.1 != id) }
def bump (t : Table) (k : Nat) : Table := { t with next := t.next + k }
end Table

def frees (hs : List BoolH) : List Instr := hs.map .freeBool

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
  { script := seqs (frees e.key.toList) (keyScript t.next slot)
    commit := fun h => (t.put id { e with key := some h }).bump 4 }

/-- **Op 38.** Reply: check ‖ ciphertext. -/
def opSeal (t : Table) (id : Nat) (version : B8) : Step B8 :=
  match t.find? id with
  | some e =>
    match e.key, e.state with
    | some k, some s => { script := sealScript t.next k s e.size version, commit := fun _ => t.bump 3 }
    | _, _ => { script := .abort "contact seal unavailable", commit := fun _ => t }
  | none => { script := .abort "contact seal unavailable", commit := fun _ => t }

/-- **Ops 37 and 63.** Reply: whether the state was loaded (the C++'s 255 / 0). -/
def opOpen (t : Table) (id : Nat) (kinds : List Nat) (version check ct : B8) : Step (Option BoolH) :=
  match t.find? id with
  | some e =>
    match e.key, e.state with
    | some k, none =>
      if kindsOk kinds ct.length then
        { script := seqs (frees e.derived) (openScript t.next k version check ct)
          commit := fun r =>
            match r with
            | some h => (t.put id { e with state := some h, size := ct.length, kinds := kinds, derived := [] }).bump 5
            | none => (t.put id { e with derived := [] }).bump 5 }
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

end TlsMpc.Node.Flows.Contacts
