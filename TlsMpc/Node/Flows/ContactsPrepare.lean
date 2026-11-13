import TlsMpc.Node.Flows.Join

/-!
# Op 66's contact-table glue (`Curve.prepareContacts`, non-hinted) and the account's sender key

STACK_NOTES F32, J12. Replaces `service_kernels.h` `prepare` (58-64) and `prepare_batch` (163-177)
on the non-hinted path (the path the joins use: `Join.ephemeralWord` runs S11's `offsetStep` on an
`offsetPrepare` state; the hinted `prepare_hinted` / S11's `Staged` `prepareContacts` stay J3):

  * per contact (one after the other, as the C++'s non-hinted loop): the contact's record (the
    first 319 bytes of its state: the record, or the first device's record of a device list, the
    C++'s `c.record`) after the account's certificate is the `conversation` of
    `signal-conversation-view CERT`; its `recipient` output (the contact's identity key as the
    255-bit word) goes to the field engine (`Receive.toField`, P-W2F, a word mask from the pool);
    the offset agreement is prepared on it (S11's `Curve.offsetPrepare`: the table program, its
    checks opened, K₀ by commit-then-open); the static agreement X25519(identity, recipient) is
    `Join.receiveAgree` on the account's identity swap-bit HANDLES (J8: no coins) and the recipient;
    the recipient field handle and the view's other output are freed;
  * the results are kept as the C++ keeps them in the contact (`c.static_agreement`, `c.offset`):
    the static word joins the entry's `derived` cache (so the table invariant covers it, and ops 37,
    40, 52, 63 free it like every derived cache); the offset state (field handles) is kept next to
    the table under the contact id (`Cache`), valid only while its static word is in the entry's
    `derived` (`prepared?`): an evict or a re-open frees `derived`, so a stale cache entry is never
    used (handle ids are never reused, Engine.lean D12);
  * the status byte per contact (`statusByte`): 255 prepared, 1 not loaded (no entry or no
    state). The C++'s 0 (a key that is not a curve point) is `hinted` only; without it a refused key
    stops the session (the script aborts on the opened checks), as the C++'s non-hinted path does.
  * `senderPublicG` (J12): the account's sender key word, the C++'s
    `agreement_word(identity, 9)` (line 62): `Join.receiveAgree` on the identity's swap-bit handles
    and the base point.

PROVED: `prepareOneG_reveals` (kinds `prepareKinds`: P-W2F's masked word, P-OFFSET's, the joined
agreements'; `prepareStatus` is the controller's name for the status bytes, computed from public
data, never a label on the wire), `senderPublicG_reveals`, `prepareKinds_registered`;
`prepareStatus_iff` (255 exactly when the contact is prepared), `commit_prepared` (after the commit
the contact is prepared, with exactly the results of its run), `commit_other` (no other contact's
preparation changes), `commit_inv` (the commit keeps the contact table's invariant, given what the
script leaves in the engine context: the new word live, fresh and below the counter, the other
handles untouched).
-/

namespace TlsMpc.Node.Flows.ContactsPrepare

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.Receive (Gen RevealsG Job)
open TlsMpc.Node.Flows.Join (AgreeSlots receiveAgree receiveAgreeKinds receiveAgree_reveals)
open TlsMpc.Node (RevealKind)

/-- The `view` kernel's name (`service_kernels.h` line 150: `signal-conversation-view CERT`). -/
def viewName (cert : Nat) : Bytes := ascii ("signal-conversation-view " ++ toString cert)

/-- Its outputs: the recipient's key as the 255-bit word, the request id (8 bytes). -/
def viewOut : List Nat := [255, 64]

/-- A contact record's bytes (`service_kernels.h` CONTACT). -/
def recordBytes : Nat := 319

/-- Field ids `offsetPrepare` uses from its block start (`Curve.prepOuts 0` + its 1531 outputs). -/
def prepIds : Nat := Curve.prepOuts 0 + 1531

/-- What op 66 keeps per contact. -/
structure Prepared where
  static : BoolH
  offset : Curve.OffsetState

/-- The offset states next to the table, by contact id. -/
abbrev Cache := List (Nat × Prepared)

/-- **A contact is prepared** when its cache entry's static word is in its entry's `derived` cache. -/
def prepared? (t : Table) (cache : Cache) (id : Nat) : Option Prepared :=
  match t.find? id, cache.lookup id with
  | some e, some p => if p.static ∈ e.derived then some p else none
  | _, _ => none

/-- **The status byte** of `prepare_batch`: 255 prepared, 1 otherwise (not loaded). -/
def statusByte (t : Table) (cache : Cache) (id : Nat) : Nat := if (prepared? t cache id).isSome then 255 else 1

/-- **The per-contact status means "prepared"**. -/
theorem prepareStatus_iff (t : Table) (cache : Cache) (id : Nat) :
    statusByte t cache id = 255 ↔ ∃ p, prepared? t cache id = some p := by
  unfold statusByte
  cases h : prepared? t cache id <;> simp

/-- Whether the contact needs a run (loaded, not prepared): its state handle. -/
def needs (t : Table) (cache : Cache) (id : Nat) : Option BoolH :=
  match prepared? t cache id with
  | some _ => none
  | none => (t.find? id).bind (·.state)

/-! ## The script of one contact -/

/-- The recipient word: the `view` kernel on certificate ‖ record (the state's first 319 bytes). -/
def recipientG (cert : BoolH) (certLen : Nat) (state : BoolH) : Gen BoolH := do
  let rec ← Receive.cut state 0 (8 * recordBytes)
  let conv ← Receive.join [cert, rec]
  let o ← Receive.stage (viewName certLen) [conv] viewOut
  Receive.Gen.freeAll [rec, conv, Receive.at! o 1]
  pure (Receive.at! o 0)

/-- **One contact's preparation**: recipient word, P-W2F, the offset agreement (`os`: its store
slots, fresh for this run), the static agreement on the identity's swap-bit handles (`sl`). -/
def prepareOneG (hash : Bytes → Bytes) (me : Party) (cert : BoolH) (certLen : Nat) (sl : AgreeSlots)
    (os : Curve.OffsetSlots) (state : BoolH) : Gen Prepared := do
  let w ← recipientG cert certLen state
  let u ← Receive.toField w
  Receive.Gen.freeAll [w]
  let f ← Receive.Gen.allocF prepIds
  let offset ← Receive.Gen.lift (Curve.offsetPrepare hash me f os u)
  let ws ← receiveAgree sl [⟨.identity, .handle u⟩]
  Receive.Gen.freeFields [u]
  match ws with
  | [s] => pure ⟨s, offset⟩
  | _ => Receive.Gen.fail "static agreement"

/-- **The account's sender key word** (J12): X25519(identity, 9) as the 255-bit word. -/
def senderPublicG (sl : AgreeSlots) : Gen BoolH := do
  let ws ← receiveAgree sl [⟨.identity, .base⟩]
  match ws with
  | [w] => pure w
  | _ => Receive.Gen.fail "sender key"

/-! ## The commit -/

/-- The table and cache after contact `id`'s run returned `p`. -/
def commit (t : Table) (cache : Cache) (id : Nat) (p : Prepared) : Table × Cache :=
  match t.find? id with
  | some e => (t.put id { e with derived := e.derived ++ [p.static] }, (id, p) :: cache.filter (·.1 != id))
  | none => (t, cache)

theorem lookup_cons_self (id : Nat) (p : Prepared) (cache : Cache) :
    ((id, p) :: cache.filter (·.1 != id)).lookup id = some p := by
  simp [List.lookup]

theorem find_put_self (t : Table) (id : Nat) (e : Entry) : (t.put id e).find? id = some e := by
  simp [Table.put, Table.find?, List.lookup]

/-- **After the commit the contact is prepared, with its run's results.** -/
theorem commit_prepared (t : Table) (cache : Cache) (id : Nat) (p : Prepared) (e : Entry) (he : t.find? id = some e) :
    prepared? (commit t cache id p).1 (commit t cache id p).2 id = some p := by
  simp only [commit, he, prepared?, find_put_self, lookup_cons_self]
  simp

theorem find_put_other (t : Table) (id id' : Nat) (e : Entry) (h : id' ≠ id) : (t.put id e).find? id' = t.find? id' := by
  simp only [Table.put, Table.find?, List.lookup]
  have hb : (id' == id) = false := by simpa using h
  simp only [hb]
  induction t.entries with
  | nil => simp [List.lookup]
  | cons q qs ih =>
    obtain ⟨k, v⟩ := q
    by_cases hk : k = id
    · subst hk
      have hb' : (id' == k) = false := by simpa using h
      simp [List.filter_cons, List.lookup, hb', ih]
    · by_cases hk' : id' = k
      · subst hk'
        simp [List.filter_cons, hk, List.lookup]
      · have hb'' : (id' == k) = false := by simpa using hk'
        simp [List.filter_cons, hk, List.lookup, hb'', ih]

theorem lookup_filter_other (cache : Cache) (id id' : Nat) (h : id' ≠ id) :
    (cache.filter (·.1 != id)).lookup id' = cache.lookup id' := by
  induction cache with
  | nil => simp [List.lookup]
  | cons q qs ih =>
    obtain ⟨k, v⟩ := q
    by_cases hk : k = id
    · subst hk
      have hb : (id' == k) = false := by simpa using h
      simp [List.filter_cons, List.lookup, hb, ih]
    · by_cases hk' : id' = k
      · subst hk'
        simp [List.filter_cons, hk, List.lookup]
      · have hb : (id' == k) = false := by simpa using hk'
        simp [List.filter_cons, hk, List.lookup, hb, ih]

/-- **The commit changes no other contact's preparation.** -/
theorem commit_other (t : Table) (cache : Cache) (id id' : Nat) (p : Prepared) (h : id' ≠ id) :
    prepared? (commit t cache id p).1 (commit t cache id p).2 id' = prepared? t cache id' := by
  unfold commit
  cases he : t.find? id with
  | none => rfl
  | some e =>
    simp only [prepared?, find_put_other t id id' _ h]
    have hl : ((id, p) :: cache.filter (·.1 != id)).lookup id' = cache.lookup id' := by
      have hb : (id' == id) = false := by simpa using h
      simp only [List.lookup, hb]
      exact lookup_filter_other cache id id' h

    rw [hl]

/-- **The commit keeps the contact table's invariant** (`Contacts.Table.Inv`), in the context `c'`
the run left, when: the new static word is live in `c'`, was not an id of the table before (at or
above the old counter) and is below the new one; every other table handle keeps its entry; the
new counter is fresh in `c'`. (That the run leaves `c'` so is the run's well-formedness: the
joined scripts' WF is open, F44.) -/
theorem commit_inv {c c' : Ctx} (t t' : Table) (cache : Cache) (id : Nat) (p : Prepared) (e : Entry)
    (hI : t.Inv c) (he : t.find? id = some e) (hent : t'.entries = t.entries) (hn : t.next ≤ t'.next)
    (hf : Fresh c' t'.next)
    (hold : ∀ q ∈ t.entries, ∀ g ∈ q.2.handles, c'.bool? g = c.bool? g)
    (hnew : t.next ≤ p.static.id) (hbelow : p.static.id < t'.next) (hlive : (c'.bool? p.static).isSome = true) :
    (commit t' cache id p).1.Inv c' := by
  have hm := Table.find_mem he
  have he' : t'.find? id = some e := by simp only [Table.find?, hent]; exact he
  simp only [commit, he']
  have hH : ({ e with derived := e.derived ++ [p.static] } : Entry).handles = e.handles ++ [p.static] := by
    simp [Entry.handles, List.append_assoc]
  refine Table.Inv.put hI hent hn hf (fun q hq _ g hg => hold q hq g hg) ?_ ?_ ?_ ?_ ?_ ?_
  · intro h hh q hq hqi g hg
    rw [hH, List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | rfl
    · exact hI.ne_of_other hq hm hqi hg hh
    · have := hI.below q hq g hg
      omega
  · intro h hh
    rw [hH, List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | rfl
    · have := hI.below _ hm h hh
      omega
    · exact hbelow
  · rw [hH, List.map_append, List.nodup_append]
    refine ⟨hI.nodup _ hm, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
    have := hI.below _ hm g hg
    omega
  · intro h hh
    rw [hH, List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | rfl
    · rw [hold _ hm h hh]; exact hI.live _ hm h hh
    · exact hlive
  · intro k hk
    have hk' : e.key = some k := hk
    rw [hold _ hm k (Entry.mem_key hk')]
    exact hI.key _ hm k hk'
  · intro s hs
    have hs' : e.state = some s := hs
    rw [hold _ hm s (Entry.mem_state hs')]
    exact hI.state _ hm s hs'

/-! ## The reveal list -/

def prepareKinds : List RevealKind := [.maskedWord] ++ Curve.offsetKinds ++ receiveAgreeKinds

theorem prepareKinds_registered : ∀ k ∈ prepareKinds, k ∈ Label.kinds := by decide

theorem recipientG_reveals (cert : BoolH) (certLen : Nat) (state : BoolH) :
    RevealsG prepareKinds (recipientG cert certLen state) := by
  unfold recipientG
  refine RevealsG.bind (Receive.cut_reveals _ _ _) fun _ => ?_
  refine RevealsG.bind (Receive.join_reveals _) fun _ => ?_
  refine RevealsG.bind (Receive.stage_reveals _ _ _) fun _ => ?_
  exact RevealsG.bind (Receive.RevealsG.freeAll _) fun _ => RevealsG.pure _

/-- **T3 for one contact's preparation in the reveal list's vocabulary.** -/
theorem prepareOneG_reveals (hash : Bytes → Bytes) (me : Party) (cert : BoolH) (certLen : Nat) (sl : AgreeSlots)
    (os : Curve.OffsetSlots) (state : BoolH) :
    RevealsG prepareKinds (prepareOneG hash me cert certLen sl os state) := by
  unfold prepareOneG
  refine RevealsG.bind (recipientG_reveals _ _ _) fun w => ?_
  refine RevealsG.bind (Receive.toField_reveals (by decide) _) fun u => ?_
  refine RevealsG.bind (Receive.RevealsG.freeAll _) fun _ => ?_
  refine RevealsG.bind (RevealsG.allocF _) fun f => ?_
  refine RevealsG.bind (RevealsG.lift ((Curve.offsetPrepare_reveals hash me f os u).mono (by decide))) fun _ => ?_
  refine RevealsG.bind (fun st => (receiveAgree_reveals sl _ st).mono (by decide)) fun ws => ?_
  refine RevealsG.bind (Receive.RevealsG.freeFields _) fun _ => ?_
  split
  · exact RevealsG.pure _
  · exact RevealsG.fail _

theorem senderPublicG_reveals (sl : AgreeSlots) : RevealsG receiveAgreeKinds (senderPublicG sl) := by
  unfold senderPublicG
  refine RevealsG.bind (fun st => receiveAgree_reveals sl _ st) fun ws => ?_
  split
  · exact RevealsG.pure _
  · exact RevealsG.fail _

end TlsMpc.Node.Flows.ContactsPrepare
