import TlsMpc.Node.Flows.Upgrade
import TlsMpc.Node.Flows.Account
import TlsMpc.Node.Flows.ContactsWrite
import TlsMpc.Node.Flows.Inversion
import TlsMpc.Node.Flows.Tls
import TlsMpc.Node.Flows.Send

/-!
# The script flows against the reveal list and the pipe: one place for the registry checks

REORGANIZATION_PLAN.md 4.3 and 5.4, stage S9 reconciled with stage S6. No I/O; no emitter imports
this module.

  * `declared`: the kinds each script flow declares (`Reveals`, Engine/Reveal.lean), and
    `declared_registered` (by `decide`): every one is in the label registry `Label.kinds`
    (Engine/Labels.lean), so every label a release instruction of a script flow carries is
    `Label.ofKind` of a kind, and is in `Label.all`.
  * `script_flows_reveal`: the flows' `Reveals` facts in one statement; `viewD_registered`: in any
    run of such a script, every release the adversary receives carries a label of `Label.all`.
  * The Lean sender emits only `Wire.Bounded` instructions for the existing flows (ids and labels
    below 2^64; Engine/Reveal.lean `nextBatch_bounded`): `joint_bounded`, `publicUpgrade_bounded`
    (in their files), and here `keyScript_bounded`, `sealScript_bounded`, `openScript_bounded`,
    `writeScript_bounded`, `account_sealScript_bounded`, `account_opSeal_bounded`, and on the
    contact table (handle ids from `Table.Inv`, the counter below 2^64 − 5) `opKey_bounded`,
    `opSeal_bounded`, `opOpen_bounded`, `opEvict_bounded`, `opAssign_bounded`, `opWrite_bounded`.
  * Stage S13 (the send scripts, Flows/Send.lean): `s13_flows_reveal`; `send_sealScript_bounded` (op
    41), `requestScript_bounded` (op 42), `requestCtrScript_bounded` (the request's record phase), with
    `joinName_length`, `sealName_lt`, `widthsName_lt`. Ops 61 and 62 (device lists): not shown
    (S13_NOTES.md).
-/

namespace TlsMpc.Node.Flows.Registry

open TlsMpc.Node.Engine TlsMpc.Node.Flows TlsMpc.Node.Flows.Contacts
open TlsMpc.Node (RevealKind)

/-! ## The kinds each script flow declares -/

/-- The kinds each script flow declares (`Reveals`): its name, and its list. -/
def declared : List (String × List RevealKind) :=
  [("Random.joint", Random.jointKinds), ("Upgrade.publicUpgrade", Random.jointKinds),
   ("Contacts.key", keyKinds), ("Contacts.seal", sealKinds), ("Contacts.open", openKinds),
   ("Contacts.write", writeKinds), ("Contacts.evict", []), ("Contacts.assign", []),
   ("Account.key", keyKinds), ("Account.seal", sealKinds),
   -- stage S10
   ("Random.challenge", Random.jointKinds), ("Masks.generate", Masks.generateKinds),
   ("Convert.wordToField", Convert.w2fKinds), ("Convert.fieldToWord", Convert.f2wKinds),
   ("Convert.bitsToField", Convert.b2fKinds), ("Convert.sharedBits", Convert.bitsKinds),
   ("Inversion.quotient", Inversion.inversionKinds), ("Account.open", Account.openKinds55),
   -- stage S12
   ("Ghash.keyShare", Ghash.ghashKinds), ("Ghash.round", Ghash.ghashKinds),
   ("Tls.sealCtr", Tls.sealKinds), ("Tls.sealClass", Tls.sealKinds), ("Tls.tag", Tls.sealKinds),
   ("Tls.open", Tls.openKinds), ("Tls.parser", []), ("Tls.update", []), ("Tls.reveal", Tls.revealKinds),
   ("Tls.range", Tls.revealKinds), ("Tls.public", []), ("Tls.drop", []), ("Tls.derive", []),
   ("Tls.openHandshake", Tls.handshakeKinds), ("Tls.verify", Tls.handshakeKinds),
   ("Tls.finish", Tls.handshakeKinds), ("Tls.agree", []),
   -- stage S13
   ("Send.seal", Send.sealKinds), ("Send.devices", Send.sealKinds), ("Send.request", []),
   ("Send.requestDevices", []), ("Send.requestCtr", Send.requestSealKinds)]

/-- **The registry check**: every kind a script flow declares is one of the label registry's
kinds (`Label.kinds`), whose labels are `Label.all`. -/
theorem declared_registered : ∀ p ∈ declared, ∀ k ∈ p.2, k ∈ Label.kinds := by decide

/-- **Every script flow declares its kinds** (on every branch, for every argument). -/
theorem script_flows_reveal :
    (∀ hash me nonce value, Reveals Random.jointKinds (Random.joint hash me nonce value)) ∧
    (∀ hash me nonce value, Reveals Random.jointKinds (Upgrade.publicUpgrade hash me nonce value)) ∧
    (∀ n slot, Reveals keyKinds (keyScript n slot)) ∧
    (∀ n key state size version, Reveals sealKinds (sealScript n key state size version)) ∧
    (∀ n key version check ct, Reveals openKinds (openScript n key version check ct)) ∧
    (∀ hash me nonceSlot valueSlot used n key state size,
      Reveals writeKinds (writeScript hash me nonceSlot valueSlot used n key state size)) ∧
    (∀ t id slot, Reveals keyKinds (opKey t id slot).script) ∧
    (∀ t id version, Reveals sealKinds (opSeal t id version).script) ∧
    (∀ t id kinds version check ct, Reveals openKinds (opOpen t id kinds version check ct).script) ∧
    (∀ t id, Reveals [] (opEvict t id).script) ∧
    (∀ t fromId toId, Reveals [] (opAssign t fromId toId).script) ∧
    (∀ t id hash me nonceSlot valueSlot used,
      Reveals writeKinds (opWrite t id hash me nonceSlot valueSlot used).script) ∧
    (∀ a slot, Reveals keyKinds (Account.keyStep a slot).1) ∧
    (∀ a n version, Reveals sealKinds (Account.opSeal a n version).1) ∧
    (∀ a version, Reveals sealKinds (Account.sealStep a version).1) :=
  ⟨Random.joint_reveals, Upgrade.publicUpgrade_reveals, keyScript_reveals, sealScript_reveals,
    openScript_reveals, writeScript_reveals, opKey_reveals, opSeal_reveals, opOpen_reveals,
    opEvict_reveals, opAssign_reveals, opWrite_reveals, Account.keyStep_reveals, Account.opSeal_reveals,
    Account.sealStep_reveals⟩

/-- **Every S10 script flow declares its kinds** (on every branch, for every argument). -/
theorem s10_flows_reveal :
    (∀ hash me nonce value dom n, Reveals Random.jointKinds (Random.challenge hash me nonce value dom n)) ∧
    (∀ p b f hash me s, Reveals Masks.generateKinds (Masks.generate p b f hash me s)) ∧
    (∀ n0 f0 u m, Reveals Convert.w2fKinds (Convert.wordToField n0 f0 u m)) ∧
    (∀ n0 f0 v m, Reveals Convert.f2wKinds (Convert.fieldToWord n0 f0 v m)) ∧
    (∀ n0 f0 x ps, Reveals Convert.b2fKinds (Convert.bitsToField n0 f0 x ps)) ∧
    (∀ f0 n slot, Reveals Convert.bitsKinds (Convert.sharedBits f0 n slot)) ∧
    (∀ f0 slot x z, Reveals Inversion.inversionKinds (Inversion.quotientScript f0 slot x z)) ∧
    (∀ a n f pool hinted version check ct,
      Reveals Account.openKinds55 (Account.openStep a n f pool hinted version check ct)) :=
  ⟨Random.challenge_reveals, Masks.generate_reveals, Convert.w2f_reveals, Convert.f2w_reveals,
    Convert.b2f_reveals, Convert.bits_reveals, Inversion.quotient_reveals, Account.openStep_reveals⟩

/-- **Every S12 script flow declares its kinds** (on every branch, for every argument). -/
theorem s12_flows_reveal :
    (∀ n traffic maskSlot dst, Reveals Ghash.ghashKinds (Ghash.keyShareScript n traffic maskSlot dst)) ∧
    (∀ n c l r m dst, Reveals Ghash.ghashKinds (Ghash.roundScript n c l r m dst)) ∧
    (∀ n traffic content seq kind size padding,
      Reveals Tls.sealKinds (Tls.sealCtrScript n traffic content seq kind size padding)) ∧
    (∀ n traffic content seq size, Reveals Tls.sealKinds (Tls.sealClassScript n traffic content seq size)) ∧
    (∀ n pad halfSlot, Reveals Tls.sealKinds (Tls.tagScript n pad halfSlot)) ∧
    (∀ n parser traffic seq tag record size cap halfSlot,
      Reveals Tls.openKinds (Tls.openScript n parser traffic seq tag record size cap halfSlot)) ∧
    (∀ n, Reveals [] (Tls.parserScript n)) ∧
    (∀ n traffic, Reveals [] (Tls.updateScript n traffic)) ∧
    (∀ n length content cap, Reveals Tls.revealKinds (Tls.revealScript n length content cap)) ∧
    (∀ n bytes lo hi, Reveals Tls.revealKinds (Tls.rangeScript n bytes lo hi)) ∧
    (∀ n bytes, Reveals [] (Tls.publicScript n bytes)) ∧
    (∀ hs, Reveals [] (Tls.dropScript hs)) ∧
    (∀ n agreement hash, Reveals [] (Tls.deriveScript n agreement hash)) ∧
    (∀ n serverHs seq record, Reveals Tls.handshakeKinds (Tls.openHandshakeScript n serverHs seq record)) ∧
    (∀ n serverHs hash message, Reveals Tls.handshakeKinds (Tls.verifyScript n serverHs hash message)) ∧
    (∀ n main clientHs sh ch cert, Reveals Tls.handshakeKinds (Tls.finishScript n main clientHs sh ch cert)) ∧
    (∀ n digest valid, Reveals [] (Tls.agreeScript n digest valid)) :=
  ⟨Ghash.keyShare_reveals, Ghash.round_reveals, Tls.sealCtr_reveals, Tls.sealClass_reveals, Tls.tag_reveals,
    Tls.open_reveals, Tls.parser_reveals, Tls.update_reveals, Tls.reveal_reveals, Tls.range_reveals,
    Tls.public_reveals, Tls.drop_reveals, Tls.derive_reveals, Tls.openHandshake_reveals, Tls.verify_reveals,
    Tls.finish_reveals, Tls.agree_reveals⟩

/-- **Registered labels only**: in any run of a script that declares registered kinds, against any
adversary, every release the adversary receives carries a label of `Label.all`. -/
theorem viewD_registered (E : Env) (me : Party) (adv : Adversary) {α : Type} (ks : List RevealKind)
    (s : Script α) (hs : Reveals ks s) (hk : ∀ k ∈ ks, k ∈ Label.kinds) (σ : Store) (I : Ideal)
    (vD : List Release) : ∀ r ∈ (withAdv E me adv s σ I vD).viewD, r.label ∈ Label.all := by
  intro r hr
  obtain ⟨k, hk', e⟩ := viewD_kinds E me adv ks s hs σ I vD r hr
  exact (Label.mem_all_iff _).mpr ⟨k, hk k hk', e⟩

/-! ## The sender's wires fit the pipe -/

theorem big_lt_B64 : (4294967296 : Nat) < B64 := by decide

theorem length_ascii (s : String) : (ascii s).length = s.length := by
  simp [ascii, String.length_toList]

theorem length_toDigitsCore (b : Nat) : ∀ (fuel n : Nat) (ds : List Char),
    (Nat.toDigitsCore b fuel n ds).length ≤ fuel + ds.length
  | 0, _, ds => by simp [Nat.toDigitsCore]
  | fuel + 1, n, ds => by
    simp only [Nat.toDigitsCore]
    split
    · simp only [List.length_cons]
      omega
    · exact Nat.le_trans (length_toDigitsCore b fuel _ _) (by simp only [List.length_cons]; omega)

theorem length_toString (n : Nat) : (toString n).length ≤ n + 1 := by
  show (Nat.repr n).length ≤ n + 1
  simp only [Nat.repr, String.length_ofList, Nat.toDigits]
  have := length_toDigitsCore 10 (n + 1) n []
  simpa using this

theorem length_keyName : keyName.length = 11 := by
  simp only [keyName, length_ascii]
  decide

theorem length_sealName (size : Nat) : (sealName size).length ≤ size + 14 := by
  have h1 := length_toString size
  have h2 : "contact-seal ".length = 13 := by decide
  simp only [sealName, length_ascii, String.length_append]
  omega

theorem length_openName (size : Nat) : (openName size).length ≤ size + 14 := by
  have h1 := length_toString size
  have h2 : "contact-open ".length = 13 := by decide
  simp only [openName, length_ascii, String.length_append]
  omega

theorem length_xorName : Account.xorName.length = 7 := by
  simp only [Account.xorName, length_ascii]
  decide

theorem frees_bounded (hs : List BoolH) (h : ∀ g ∈ hs, g.id < B64) : ∀ i ∈ frees hs, Instr.Bounded i := by
  intro i hi
  simp only [frees, List.mem_map] at hi
  obtain ⟨g, hg, rfl⟩ := hi
  exact h g hg

theorem keyScript_bounded (n slot : Nat) (hn : n + 4 < B64) : Every Instr.Bounded (keyScript n slot) := by
  have hB := big_lt_B64
  have hname := length_keyName
  refine every_seqs (Every.done _) _ ?_
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;>
    simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank] <;> omega

theorem sealScript_bounded (n : Nat) (key state : BoolH) (size : Nat) (version : B8) (hn : n + 3 < B64)
    (hk : key.id < B64) (hs : state.id < B64) : Every Instr.Bounded (sealScript n key state size version) := by
  have hB := big_lt_B64
  have hname := length_sealName size
  unfold sealScript
  split
  · next hc =>
    obtain ⟨hv, -, h1⟩ := hc
    have hvl := versionOk_length version hv
    refine every_seqs (every_openThen ?_ (fun b => every_seqs (Every.done _) _ ?_)) _ ?_
    · simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, sealedBlob, Label.sealedBlob]
      omega
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]
      omega
    · intro i hi
      simp only [sealBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;>
        simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, hvl] <;> omega
  · exact Every.abort _

theorem openScript_bounded (n : Nat) (key : BoolH) (version check ct : B8) (hn : n + 5 < B64)
    (hk : key.id < B64) : Every Instr.Bounded (openScript n key version check ct) := by
  have hB := big_lt_B64
  have hname := length_openName ct.length
  unfold openScript
  split
  · next hc =>
    obtain ⟨hv, hcl, -, h1⟩ := hc
    have hvl := versionOk_length version hv
    refine every_seqs (every_openThen ?_ (fun b => ?_)) _ ?_
    · simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, blobAccepted, Label.blobAccepted]
      omega
    · unfold openRest
      split
      · refine every_seqs (Every.done _) _ ?_
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        subst hi
        simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]
        omega
      · refine every_seqs (Every.done _) _ ?_
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;>
          simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank] <;> omega
    · intro i hi
      simp only [openBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, hvl, hcl] <;> omega
  · exact Every.abort _

theorem writeScript_bounded (hash : Bytes → Bytes) (me : Party) (nonceSlot valueSlot : Nat) (used : List B8)
    (n : Nat) (key state : BoolH) (size : Nat) (hn : n + 3 < B64) (hk : key.id < B64) (hs : state.id < B64) :
    Every Instr.Bounded (writeScript hash me nonceSlot valueSlot used n key state size) := by
  unfold writeScript
  refine Every.bind (Random.joint_bounded hash me nonceSlot valueSlot) (fun j => ?_)
  split
  · exact Every.bind (sealScript_bounded n key state size _ hn hk hs) (fun _ => Every.done _)
  · exact Every.abort _

theorem account_sealScript_bounded (n : Nat) (key scalar cred cert : BoolH) (certLen : Nat) (version : B8)
    (hn : n + 4 < B64) (hk : key.id < B64) (hs : scalar.id < B64) (hc : cred.id < B64) (ht : cert.id < B64) :
    Every Instr.Bounded (Account.sealScript n key scalar cred cert certLen version) := by
  have hB := big_lt_B64
  have hname := length_sealName (Account.contentBytes certLen)
  unfold Account.sealScript
  split
  · next hcond =>
    obtain ⟨hv, h1⟩ := hcond
    have hvl := versionOk_length version hv
    refine every_seqs (every_openThen ?_ (fun b => every_seqs (Every.done _) _ ?_)) _ ?_
    · simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, sealedBlob, Label.sealedBlob]
      omega
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]
      omega
    · intro i hi
      simp only [Account.accountBlock, sealBlock, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, hvl] <;> omega
  · exact Every.abort _

theorem mem_interleave (w j : Nat) (h : j ∈ Account.interleave w) : j < 2 * w := by
  simp only [Account.interleave, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at h
  obtain ⟨i, hi, h⟩ := h
  omega

theorem length_flatMap_two (f : Nat → List Nat) (hf : ∀ i, (f i).length = 2) :
    ∀ m, ((List.range m).flatMap f).length = 2 * m
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_two f hf m]
    simp [hf] <;> omega

theorem length_interleave (w : Nat) : (Account.interleave w).length = 2 * w :=
  length_flatMap_two _ (fun _ => rfl) w

theorem combineBlock_bounded (n : Nat) (ca cb : BoolH) (hn : n + 3 < B64) (ha : ca.id < B64) (hb : cb.id < B64) :
    ∀ i ∈ Account.combineBlock n ca cb, Instr.Bounded i := by
  have hB := big_lt_B64
  have hname := length_xorName
  have hl := length_interleave (8 * Account.credentialBytes)
  have hc : Account.credentialBytes = 38 := rfl
  intro i hi
  simp only [Account.combineBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]
    omega
  · simp only [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]
    refine ⟨by omega, by omega, by omega, fun j hj => ?_⟩
    have := mem_interleave _ j hj
    omega
  all_goals simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]
  all_goals omega

theorem account_opSeal_bounded (a : Account.State) (n : Nat) (version : B8) (hn : n + 7 < B64)
    (hh : ∀ k s cert len, a.key = some k → a.scalar = some s → a.certificate = some (cert, len) →
      k.id < B64 ∧ s.id < B64 ∧ cert.id < B64)
    (hcr : ∀ cr, a.credentials = some cr → cr.id < B64)
    (hsh : ∀ ca cb, a.shares = some (ca, cb) → ca.id < B64 ∧ cb.id < B64) :
    Every Instr.Bounded (Account.opSeal a n version).1 := by
  unfold Account.opSeal
  cases hk : a.key with
  | none => exact Every.abort _
  | some k =>
    cases hs : a.scalar with
    | none => exact Every.abort _
    | some s =>
      cases ht : a.certificate with
      | none => exact Every.abort _
      | some p =>
        obtain ⟨cert, len⟩ := p
        obtain ⟨h1, h2, h3⟩ := hh k s cert len hk hs ht
        cases hc : a.credentials with
        | some cr => exact account_sealScript_bounded _ _ _ _ _ _ _ (by omega) h1 h2 (hcr cr hc) h3
        | none =>
          cases hsh' : a.shares with
          | none => exact Every.abort _
          | some q =>
            obtain ⟨ca, cb⟩ := q
            obtain ⟨h4, h5⟩ := hsh ca cb hsh'
            exact every_seqs (account_sealScript_bounded _ _ _ _ _ _ _ (by omega) h1 h2
              (by show n + 2 < B64; omega) h3) _ (combineBlock_bounded n ca cb (by omega) h4 h5)

/-! ### On the contact table: handle ids from `Table.Inv`, the counter below 2^64 − 5 -/

theorem entry_bounded {c : Ctx} {t : Table} (hI : t.Inv c) (ht : t.next + 5 < B64) {id : Nat} {e : Entry}
    (he : t.find? id = some e) : ∀ g ∈ e.handles, g.id < B64 := fun g hg => by
  have := hI.below _ (Table.find_mem he) g hg
  omega

theorem opKey_bounded (c : Ctx) (t : Table) (id slot : Nat) (hI : t.Inv c) (ht : t.next + 5 < B64) :
    Every Instr.Bounded (opKey t id slot).script := by
  show Every Instr.Bounded (seqs (frees ((t.find? id).getD {}).key.toList) (keyScript (t.alloc 4).1 slot))
  refine every_seqs (keyScript_bounded _ slot (by simp only [Table.alloc_fst]; omega)) _ (frees_bounded _ ?_)
  intro g hg
  cases hf : t.find? id with
  | none => simp [hf] at hg
  | some e =>
    rw [hf] at hg
    exact entry_bounded hI ht hf g (Entry.mem_key (by simpa using hg))

theorem opSeal_bounded (c : Ctx) (t : Table) (id : Nat) (version : B8) (hI : t.Inv c) (ht : t.next + 5 < B64) :
    Every Instr.Bounded (opSeal t id version).script := by
  unfold opSeal
  cases hf : t.find? id with
  | none => exact Every.abort _
  | some e =>
    dsimp only
    cases hk : e.key with
    | none => exact Every.abort _
    | some k =>
      cases hs : e.state with
      | none => exact Every.abort _
      | some s =>
        exact sealScript_bounded _ k s _ _ (by simp only [Table.alloc_fst]; omega)
          (entry_bounded hI ht hf k (Entry.mem_key hk)) (entry_bounded hI ht hf s (Entry.mem_state hs))

theorem opOpen_bounded (c : Ctx) (t : Table) (id : Nat) (kinds : List Nat) (version check ct : B8)
    (hI : t.Inv c) (ht : t.next + 5 < B64) : Every Instr.Bounded (opOpen t id kinds version check ct).script := by
  unfold opOpen
  cases hf : t.find? id with
  | none => exact Every.abort _
  | some e =>
    dsimp only
    cases hk : e.key with
    | none => exact Every.abort _
    | some k =>
      cases hs : e.state with
      | some s => exact Every.abort _
      | none =>
        dsimp only
        split
        · refine every_seqs (openScript_bounded _ k _ _ _ (by simp only [Table.alloc_fst]; omega)
            (entry_bounded hI ht hf k (Entry.mem_key hk))) _ (frees_bounded _ (fun g hg => ?_))
          exact entry_bounded hI ht hf g (by simp [Entry.handles, hg])
        · exact Every.abort _

theorem opEvict_bounded (c : Ctx) (t : Table) (id : Nat) (hI : t.Inv c) (ht : t.next + 5 < B64) :
    Every Instr.Bounded (opEvict t id).script := by
  unfold opEvict
  cases hf : t.find? id with
  | none => exact Every.abort _
  | some e => exact every_seqs (Every.done _) _ (frees_bounded _ (entry_bounded hI ht hf))

theorem opAssign_bounded (c : Ctx) (t : Table) (fromId toId : Nat) (hI : t.Inv c) (ht : t.next + 5 < B64) :
    Every Instr.Bounded (opAssign t fromId toId).script := by
  unfold opAssign
  cases hf : t.find? fromId with
  | none => exact Every.abort _
  | some e =>
    dsimp only
    split
    · exact every_seqs (Every.done _) _ (frees_bounded _ (entry_bounded hI ht hf))
    · exact Every.done _

theorem opWrite_bounded (c : Ctx) (t : Table) (id : Nat) (hash : Bytes → Bytes) (me : Party)
    (nonceSlot valueSlot : Nat) (used : List B8) (hI : t.Inv c) (ht : t.next + 5 < B64) :
    Every Instr.Bounded (opWrite t id hash me nonceSlot valueSlot used).script := by
  unfold opWrite
  cases hf : t.find? id with
  | none => exact Every.abort _
  | some e =>
    dsimp only
    cases hk : e.key with
    | none => exact Every.abort _
    | some k =>
      cases hs : e.state with
      | none => exact Every.abort _
      | some s =>
        exact writeScript_bounded _ _ _ _ _ _ k s _ (by simp only [Table.alloc_fst]; omega)
          (entry_bounded hI ht hf k (Entry.mem_key hk)) (entry_bounded hI ht hf s (Entry.mem_state hs))

/-! ## Stage S13: the send scripts -/

set_option linter.unusedSimpArgs false

/-- **Every S13 script flow declares its kinds** (on every branch, for every argument). -/
theorem s13_flows_reveal :
    (∀ n a, Reveals Send.sealKinds (Send.sealScript n a)) ∧
    (∀ n a, Reveals Send.sealKinds (Send.devicesScript n a)) ∧
    (∀ n cert state, Reveals [] (Send.requestScript n cert state)) ∧
    (∀ n state ats, Reveals [] (Send.requestDevicesScript n state ats)) ∧
    (∀ n traffic conv seq frame mask name,
      Reveals Send.requestSealKinds (Send.requestCtrScript n traffic conv seq frame mask name)) :=
  ⟨Send.seal_reveals, Send.devices_reveals, Send.request_reveals, Send.requestDevices_reveals,
    Send.requestCtr_reveals⟩

theorem length_intersperse_flatten (sep : Bytes) :
    ∀ (l : List Bytes), ((l.intersperse sep).flatten).length ≤ (l.map List.length).sum + l.length * sep.length
  | [] => by simp
  | [x] => by simp
  | x :: y :: rest => by
    have ih := length_intersperse_flatten sep (y :: rest)
    simp only [List.intersperse_cons_cons, List.flatten_cons, List.length_append, List.map_cons, List.sum_cons,
      List.length_cons] at ih ⊢
    rw [Nat.add_mul] at ⊢
    omega

/-- A kernel name's length: its words' lengths plus the spaces. -/
theorem joinName_length (parts : List String) :
    (Send.joinName parts).length ≤ (parts.map String.length).sum + parts.length := by
  have h := length_intersperse_flatten (ascii " ") (parts.map ascii)
  have hs : (ascii " ").length = 1 := by simp only [length_ascii]; decide
  rw [hs, Nat.mul_one, List.map_map, List.length_map] at h
  have e : (List.map (List.length ∘ ascii) parts) = parts.map String.length := by
    apply List.map_congr_left
    intro p _
    simp [length_ascii]
  rw [e] at h
  exact h

theorem sealName_lt (official : Bool) (cert classes cw pw ew iw : Nat) (h : cert ≤ 1024) (hc : classes ≤ 4)
    (hw : cw ≤ 10 ∧ pw ≤ 10 ∧ ew ≤ 10 ∧ iw ≤ 10) : (Send.sealName official cert classes cw pw ew iw).length < B64 := by
  have hB := big_lt_B64
  have hl := joinName_length [if official then "signal-seal-official" else "signal-seal-built", toString cert,
    toString classes, toString cw, toString pw, toString ew, toString iw]
  have h1 : (if official then "signal-seal-official" else "signal-seal-built").length ≤ 20 := by
    cases official <;> decide
  have := length_toString cert
  have := length_toString classes
  have := length_toString cw
  have := length_toString pw
  have := length_toString ew
  have := length_toString iw
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hl
  show (Send.joinName _).length < B64
  omega

theorem widthsName_lt (cert : Nat) (h : cert ≤ 1024) : (Send.widthsName cert).length < B64 := by
  have hB := big_lt_B64
  have hl := joinName_length ["signal-widths", toString cert]
  have := length_toString cert
  have h1 : "signal-widths".length = 13 := by decide
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, h1] at hl
  show (Send.joinName _).length < B64
  omega

theorem sealBlock_bounded (n : Nat) (a : Send.SealArgs) (name : Bytes) (env : Nat) (hn : n + 8 < B64)
    (hids : a.sender.id < B64 ∧ a.static.id < B64 ∧ a.ephAgreement.id < B64) (hname : name.length < B64)
    (hcert : a.certLen ≤ 1024) (henv : env ≤ Send.maxEnvelope) (htext : a.text.length ≤ 330)
    (hpk : a.ephPublic.length = 32) :
    ∀ i ∈ Send.sealBlock n a name env, Instr.Bounded i := by
  have hB := big_lt_B64
  intro i hi
  simp only [Send.sealBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Send.wordBits, hpk, Send.statusEnd,
      Send.recordFrom, Send.recordEnd, Send.envelopeEnd, Send.convBytes, Send.recordBytes, Send.maxEnvelope] at * <;>
    omega

/-- **Op 41's wires fit the pipe** (`Wire.Bounded` through `nextBatch_bounded`): the ids below 2^64,
every name, width and slice bound small (the certificate at most 1024 bytes, the widths at most 10,
the envelope at most `maxEnvelope`: the script aborts otherwise). -/
theorem send_sealScript_bounded (n : Nat) (a : Send.SealArgs) (hn : n + 8 < B64)
    (hids : a.cert.id < B64 ∧ a.state.id < B64 ∧ a.sender.id < B64 ∧ a.static.id < B64 ∧ a.ephAgreement.id < B64)
    (hpk : a.ephPublic.length = 32) : Every Instr.Bounded (Send.sealScript n a) := by
  have hB := big_lt_B64
  obtain ⟨hc, hs, hd, ht, he⟩ := hids
  unfold Send.sealScript
  split
  · rename_i official classes hcl
    obtain ⟨hT, hcls⟩ := Send.textClass_le hcl
    split
    · rename_i hcert
      refine every_seqs (every_openThen ?_ (fun flags => every_seqs ?_ _ ?_)) _ ?_
      · simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Send.widthsLabel, Send.envelopeLabel, Label.counterWidths, Label.sealedEnvelope, Label.sealedRecord, Label.ofKind]; omega
      · unfold Send.afterWidths
        split
        · rename_i cw pw ew iw hw
          have hw' := Send.widthsOf_le hw
          split
          · rename_i henv
            refine every_seqs (every_openThen ?_ (fun st => ?_)) _
              (sealBlock_bounded n a _ _ hn ⟨hd, ht, he⟩ (sealName_lt _ _ _ _ _ _ _ hcert hcls hw') hcert henv hT hpk)
            · simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Send.widthsLabel, Send.envelopeLabel, Label.counterWidths, Label.sealedEnvelope, Label.sealedRecord, Label.ofKind]; omega
            · unfold Send.afterStatus
              split
              · refine every_seqs (every_openThen ?_ (fun _ => every_seqs (Every.done _) _ ?_)) _ ?_
                · simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Send.widthsLabel, Send.envelopeLabel, Label.counterWidths, Label.sealedEnvelope, Label.sealedRecord, Label.ofKind]; omega
                · intro i hi
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl <;> simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map,
                    InstrP.blank, Send.widthsLabel, Send.envelopeLabel, Label.counterWidths, Label.sealedEnvelope, Label.sealedRecord, Label.ofKind] <;> omega
                · intro i hi
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl
                  simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Send.widthsLabel, Send.envelopeLabel, Label.counterWidths, Label.sealedEnvelope, Label.sealedRecord, Label.ofKind]; omega
              · refine every_seqs (Every.done _) _ ?_
                intro i hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl | rfl <;> simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map,
                  InstrP.blank, Send.widthsLabel, Send.envelopeLabel, Label.counterWidths, Label.sealedEnvelope, Label.sealedRecord, Label.ofKind] <;> omega
          · exact Every.abort _
        · exact Every.abort _
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl
        simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Send.widthsLabel, Send.envelopeLabel, Label.counterWidths, Label.sealedEnvelope, Label.sealedRecord, Label.ofKind]; omega
      · intro i hi
        simp only [Send.widthsBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Send.widthsLabel, Send.envelopeLabel, Label.counterWidths, Label.sealedEnvelope, Label.sealedRecord, Label.ofKind]; omega
        · have := widthsName_lt a.certLen hcert
          simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Send.widthsLabel, Send.envelopeLabel, Label.counterWidths, Label.sealedEnvelope, Label.sealedRecord, Label.ofKind]; omega
    · exact Every.abort _
  · exact Every.abort _

/-- **Op 42's wires fit the pipe.** -/
theorem requestScript_bounded (n : Nat) (cert state : BoolH) (hn : n + 2 < B64) (hc : cert.id < B64)
    (hs : state.id < B64) : Every Instr.Bounded (Send.requestScript n cert state) := by
  have hB := big_lt_B64
  refine every_seqs (Every.done _) _ ?_
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;>
    simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Send.recordBytes] <;> omega

/-- **The request's record phase fits the pipe** (a frame of at most 65 535 bytes, `PublicRequest.build`'s
bound; the kernel's name short). -/
theorem requestCtrScript_bounded (n : Nat) (traffic conv : BoolH) (seq frame mask : B8) (name : Bytes)
    (hn : n + 6 < B64) (ht : traffic.id < B64) (hc : conv.id < B64) (hs : seq.length = 8) (hm : mask.length = 4)
    (hf : frame.length < 65536) (hname : name.length < B64) :
    Every Instr.Bounded (Send.requestCtrScript n traffic conv seq frame mask name) := by
  have hB := big_lt_B64
  refine every_seqs (every_openThen ?_ (fun _ => every_seqs ?_ _ ?_)) _ ?_
  · simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Send.widthsLabel, Send.envelopeLabel, Label.counterWidths, Label.sealedEnvelope, Label.sealedRecord, Label.ofKind]; omega
  · split
    · exact Every.done _
    · exact Every.abort _
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl
    simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Send.widthsLabel, Send.envelopeLabel, Label.counterWidths, Label.sealedEnvelope, Label.sealedRecord, Label.ofKind]; omega
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, hs, hm, Send.innerOf, Send.widthsLabel, Send.envelopeLabel, Label.counterWidths, Label.sealedEnvelope, Label.sealedRecord, Label.ofKind] <;>
      omega

end TlsMpc.Node.Flows.Registry
