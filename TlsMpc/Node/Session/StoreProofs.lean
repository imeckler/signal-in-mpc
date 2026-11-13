import TlsMpc.Node.Session.Store
import TlsMpc.Node.Session.Events

/-!
# P4: the contact store before a send (ORD-1's store half) and a refresh's commit (ORD-2)

About the definitions of `Session/Store.lean` (`kindsOfG`, `setKindsG`, `versionOfG`,
`bumpVersionG`, `sealStateG`, `dbG`, `dbSubmitG`, `dbWriteG`, `storeAdvancedG`, `dbSubmitSoftG`,
`storeSoftG`, `commitScratchG`), whose instances at `SessionM` and `storeReal` ARE the deployed
`kindsOf` … `commitScratch` (`abbrev f := fG storeReal`), run in `Model` at any environment
(`storeModel E`; `Events.lean`, header, for what this says about a real run):

- `storeAdvanced_acked` (the non-recovery path's store, ORD-1): with the database, if it returns,
  the contact's phase went from `sealed` to `pending` (this party's nodes acknowledged a blob sealed
  from the state after the seal); it logs no request, no message seal, no commit;
- `storeSoft_agreed` (the recovery path's store, ORD-1): if it returns `true`, from `sealed` to
  `agreed` (both parties reported their nodes' acknowledgement); same exclusions;
- `storeSoft_version`, `storeAdvanced_version`: the write is version `versionOf + 1`, and the
  session's version moves to it exactly when the store was taken;
- `commitScratch_agreed` (ORD-2): every run keeps `CommitsAgreed`; when it returns `true` the commit
  is the newest event and was preceded by both acknowledgements; when it returns `false`, the
  scratch is dropped and nothing is committed.

No I/O primitive; no emitter imports this module.
-/

namespace TlsMpc.Node.Session.Events
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Node TlsMpc.Node.Session

/-- `insist`, lifted into a session, is `if ok then pure () else throw error`: what the model uses
for `StoreOps.insist` (the deployed `storeReal.insist`). -/
theorem insist_session (b : Bool) (e : String) : (insist b e : SessionM Unit) = (if b then pure () else throw e) := by
  cases b <;> rfl

/-! ### The model of the store operations -/

/-- The environment's answer to each store operation's `i`-th call (the last argument): anything.
Only `requestFile` may read the session state (the deployed one reads `State.jobRequest`). -/
structure StoreEnv where
  dbTry : DbCall → Context → Nat → Except String Bool
  peer : PeerMsg → Context → Nat → Except String PeerMsg
  writeAcknowledged : String → Context → Nat → Except String Bool
  nonce : Context → Nat → Except String Bytes
  contactSeal : Nat → Bytes → Context → Nat → Except String (Opened .sealedBlob Bytes)
  requestFile : Context → State → Nat → Except String String
  scratchSeal : Nat → Bytes → Context → Nat → Except String (Opened .sealedBlob Bytes)
  scratchCommit : Nat → Context → Nat → Except String Unit
  drop : Context → Nat → Except String Unit

/-- The event of an exchange with the other node. -/
def peerEvent (msg : PeerMsg) : Except String PeerMsg → Event
  | .ok reply => .peer msg (some reply)
  | .error _ => .peer msg none

/-- The store operations in the model: each effect logs its event (`insist` is the session's
`insist`, `insist_session`). -/
def storeModel (E : StoreEnv) : StoreOps Model where
  insist b e := if b then pure () else throw e
  dbTry call := Model.atom (E.dbTry call) (fun r => .db call (Model.okOf r))
  peer msg := Model.atom (E.peer msg) (peerEvent msg)
  writeAcknowledged _ n := Model.atom (E.writeAcknowledged n) (fun r => .acked n (Model.okOf r))
  nonce := Model.atom E.nonce (fun _ => .other "nonce")
  contactSeal _ c f := Model.atom (E.contactSeal c f) (fun _ => .blobSeal c)
  requestFile := Model.rbox E.requestFile
  scratchSeal _ c f := Model.atom (E.scratchSeal c f) (fun _ => .scratchSeal c)
  scratchCommit _ c := Model.atom (E.scratchCommit c) (fun _ => .scratchCommit c)
  drop _ := Model.atom E.drop (fun _ => .scratchDrop)

theorem isNone_false {c : Context} (h : c.dbClient.isSome) : c.dbClient.isNone = false := by
  cases hc : c.dbClient <;> simp_all

@[simp] theorem peerEvent_ok (msg reply : PeerMsg) : peerEvent msg (.ok reply) = .peer msg (some reply) := rfl
@[simp] theorem peerEvent_error (msg : PeerMsg) (e : String) : peerEvent msg (.error e) = .peer msg none := rfl
@[simp] theorem peerEvent_request (msg : PeerMsg) (r : Except String PeerMsg) (c : Nat) :
    (peerEvent msg r = .request c) ↔ False := by cases r <;> simp [peerEvent]
@[simp] theorem peerEvent_commit (msg : PeerMsg) (r : Except String PeerMsg) (c : Nat) :
    (peerEvent msg r = .scratchCommit c) ↔ False := by cases r <;> simp [peerEvent]
@[simp] theorem okOf_ok (b : Bool) : Model.okOf (.ok b) = b := rfl
@[simp] theorem okOf_error (e : String) : Model.okOf (.error e) = false := rfl

/-- The automata at the events that do not concern them (the store's bookkeeping events). -/
@[simp] theorem step_db (c : Nat) (ph : Phase) (call : DbCall) (ok : Bool) : step c ph (.db call ok) = ph.settle := by
  cases ph <;> rfl
@[simp] theorem step_other (c : Nat) (ph : Phase) (s : String) : step c ph (.other s) = ph.settle := by
  cases ph <;> rfl
@[simp] theorem agrees_peer_none (msg : PeerMsg) : (Event.peer msg none).agrees = false := by
  unfold Event.agrees; split <;> simp_all
@[simp] theorem step_peer_none (c : Nat) (ph : Phase) (msg : PeerMsg) : step c ph (.peer msg none) = ph.settle := by
  cases ph <;> simp [step, coreStep, Phase.settle]
@[simp] theorem settle_settle (ph : Phase) : ph.settle.settle = ph.settle := by cases ph <;> rfl
@[simp] theorem peerEvent_isRequest (msg : PeerMsg) (r : Except String PeerMsg) : (peerEvent msg r).isRequest = false := by
  cases r <;> rfl
@[simp] theorem peerEvent_isCommit (msg : PeerMsg) (r : Except String PeerMsg) : (peerEvent msg r).isCommit = false := by
  cases r <;> rfl
@[simp] theorem scratchStep_db (c : Nat) (sp : ScratchPhase) (call : DbCall) (ok : Bool) :
    scratchStep c sp (.db call ok) = sp.settle := by cases sp <;> rfl
@[simp] theorem scratchStep_other (c : Nat) (sp : ScratchPhase) (s : String) :
    scratchStep c sp (.other s) = sp.settle := by cases sp <;> rfl
@[simp] theorem scratchStep_peer_none (c : Nat) (sp : ScratchPhase) (msg : PeerMsg) :
    scratchStep c sp (.peer msg none) = sp.settle := by
  cases sp <;> simp [scratchStep, scratchCore, ScratchPhase.settle]
@[simp] theorem scratchSettle_settle (sp : ScratchPhase) : sp.settle.settle = sp.settle := by cases sp <;> rfl

/-- The operations every store twin unfolds to (for `simp only`). -/
macro "store_unfold" : tactic => `(tactic| simp only [storeSoftG, storeAdvancedG, commitScratchG, dbWriteG,
  dbSubmitG, dbSubmitSoftG, storeModel, sealStateG, dbG, kindsOfG, versionOfG, bumpVersionG, setKindsG,
  modifyContactsG])

/-! ### What the store functions keep -/

/-- `storeSoft` logs neither a request nor a commit: it keeps every `Stable` property of the log
(`SendsAgreed`, `SendsAcked`, `CommitsAgreed`), with or without the database. -/
theorem storeSoft_keeps {I : List Event → Prop} (hI : Stable I) (E : StoreEnv) (contact : Nat)
    (c : Context) (st : State) (w : World) (hw : I w.log) :
    Model.wp (storeSoftG (storeModel E) contact) (fun _ _ w' => I w'.log) c st w := by
  store_unfold
  wp_step
  repeat' (split <;> try wp_step)
  all_goals keep_log hI

/-- `storeAdvanced` likewise. -/
theorem storeAdvanced_keeps {I : List Event → Prop} (hI : Stable I) (E : StoreEnv) (contact : Nat)
    (c : Context) (st : State) (w : World) (hw : I w.log) :
    Model.wp (storeAdvancedG (storeModel E) contact) (fun _ _ w' => I w'.log) c st w := by
  store_unfold
  wp_step
  repeat' (split <;> try wp_step)
  all_goals keep_log hI

/-- `commitScratch` logs no request (it may log a commit: ORD-2 below): it keeps every `Stable`
property that a commit keeps (`SendsAgreed`, `SendsAcked`). -/
theorem commitScratch_keeps {I : List Event → Prop} (hI : Stable I)
    (hc : ∀ c l, I l → I (.scratchCommit c :: l)) (E : StoreEnv) (contact : Nat) (kinds : List Nat)
    (c : Context) (st : State) (w : World) (hw : I w.log) :
    Model.wp (commitScratchG (storeModel E) contact kinds) (fun _ _ w' => I w'.log) c st w := by
  store_unfold
  wp_step
  repeat' (split <;> try wp_step)
  all_goals (repeat (first | assumption | apply hc |
    (refine Stable.cons hI ?_ ?_ ?_ <;> try simp [Event.isRequest, Event.isCommit])))

/-! ### ORD-1, the store before a send -/

set_option maxHeartbeats 2000000 in
/-- **`storeSoft` (ORD-1's store, recovery path).** With the database nodes, if it returns `true`
the contact's phase went from `sealed` (a message was just sealed) to `agreed`: after the seal, the
contact's state was sealed for storage (`blobSeal`), this party's nodes acknowledged that write
(`acked`), and the other party reported its nodes' acknowledgement in the very next exchange. -/
theorem storeSoft_agreed (E : StoreEnv) (contact : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hph : phase contact w.log = .sealed) :
    Model.wp (storeSoftG (storeModel E) contact) (fun r _ w' =>
      r = .ok true → phase contact w'.log = .agreed) c st w := by
  have hn := isNone_false hdb
  store_unfold
  wp_step
  simp only [hn, Bool.false_eq_true, ↓reduceIte]
  clear hn hdb
  repeat' (split <;> try wp_step)
  all_goals try (simp; done)
  all_goals simp_all [step, coreStep, Phase.settle, Event.agrees]

set_option maxHeartbeats 2000000 in
/-- **`storeAdvanced` (ORD-1's store, the path without recovery).** With the database nodes, if it
returns (it fails otherwise: the session ends), the contact's phase went from `sealed` to one where
this party's nodes acknowledged a blob sealed after the message (`ownAck`). The other party checks
its own nodes the same way; a send is a two-party computation, so it leaves only when both
returned. -/
theorem storeAdvanced_acked (E : StoreEnv) (contact : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hph : phase contact w.log = .sealed) :
    Model.wp (storeAdvancedG (storeModel E) contact) (fun r _ w' =>
      r = .ok () → (phase contact w'.log).ownAck = true) c st w := by
  store_unfold
  wp_step
  simp only [hdb, ↓reduceIte]
  clear hdb
  repeat' (split <;> try wp_step)
  all_goals try (simp; done)
  all_goals simp_all [step, coreStep, Phase.settle, Phase.ownAck, Event.agrees]

/-- `storeSoft` inside a larger computation: from a `sealed` phase and a log satisfying a `Stable`
`I`, its continuation runs with `I` and, when it returned `true`, the `agreed` phase. -/
theorem storeSoft_then (E : StoreEnv) (contact : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) {I : List Event → Prop} (hI : Stable I) (hw : I w.log)
    (hph : phase contact w.log = .sealed) {K : Except String Bool → State → World → Prop}
    (hK : ∀ r st' w', I w'.log → (r = .ok true → phase contact w'.log = .agreed) → K r st' w') :
    Model.wp (storeSoftG (storeModel E) contact) K c st w :=
  Model.wp_mono (Model.wp_and (storeSoft_keeps hI E contact c st w hw) (storeSoft_agreed E contact c st w hdb hph))
    (fun r st' w' h => hK r st' w' h.1 h.2)

/-- `storeAdvanced` inside a larger computation (the path without recovery). -/
theorem storeAdvanced_then (E : StoreEnv) (contact : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) {I : List Event → Prop} (hI : Stable I) (hw : I w.log)
    (hph : phase contact w.log = .sealed) {K : Except String Unit → State → World → Prop}
    (hK : ∀ r st' w', I w'.log → (r = .ok () → (phase contact w'.log).ownAck = true) → K r st' w') :
    Model.wp (storeAdvancedG (storeModel E) contact) K c st w :=
  Model.wp_mono (Model.wp_and (storeAdvanced_keeps hI E contact c st w hw) (storeAdvanced_acked E contact c st w hdb hph))
    (fun r st' w' h => hK r st' w' h.1 h.2)

/-! ### ORD-2, a refresh's commit -/

set_option maxHeartbeats 2000000 in
/-- **ORD-2 (`commitScratch`).** With the database nodes, every run keeps `CommitsAgreed`: the
scratch is committed only after it was sealed for storage, this party's nodes acknowledged that
write and the other party reported its nodes' acknowledgement right after. -/
theorem commitScratch_agreed (E : StoreEnv) (contact : Nat) (kinds : List Nat) (c : Context) (st : State)
    (w : World) (hdb : c.dbClient.isSome) (hw : CommitsAgreed w.log) :
    Model.wp (commitScratchG (storeModel E) contact kinds) (fun _ _ w' => CommitsAgreed w'.log) c st w := by
  store_unfold
  wp_step
  simp only [hdb, ↓reduceIte]
  clear hdb
  repeat' (split <;> try wp_step)
  all_goals first
    | (keep_log stable_commitsAgreed; done)
    | (rw [commitsAgreed_cons]
       refine ⟨?_, fun c' he => ?_⟩
       · keep_log stable_commitsAgreed
       · cases he
         simp only [Bool.and_eq_true] at *
         simp_all [scratchStep, scratchCore, ScratchPhase.settle, Event.agrees])

/-- **ORD-2, the outcome (`commitScratch`).** With the database nodes: when it returns `true` the
newest event is the commit; when it returns `false` the newest event is the drop (nothing
committed: the contact is as before, in the engines and on the nodes). -/
theorem commitScratch_outcome (E : StoreEnv) (contact : Nat) (kinds : List Nat) (c : Context) (st : State)
    (w : World) (hdb : c.dbClient.isSome) :
    Model.wp (commitScratchG (storeModel E) contact kinds) (fun r _ w' =>
      (r = .ok true → w'.log.head? = some (.scratchCommit contact)) ∧
      (r = .ok false → w'.log.head? = some .scratchDrop)) c st w := by
  store_unfold
  wp_step
  simp only [hdb, ↓reduceIte]
  clear hdb
  repeat' (split <;> try wp_step)
  all_goals try simp only [Bool.and_eq_true] at *
  all_goals simp_all

/-! ### Versions -/

/-- A contact's version in a version list (`versionOf`). -/
def versionIn (versions : List (Nat × Nat)) (contact : Nat) : Nat :=
  ((versions.find? (·.1 == contact)).map (·.2)).getD 0

/-- `bumpVersion`'s change of the version list. -/
def bumpIn (versions : List (Nat × Nat)) (contact v : Nat) : List (Nat × Nat) :=
  versions.map (fun (c, x) => if c == contact then (c, v + 1) else (c, x))

/-- A contact the list holds gets the next version. -/
theorem versionIn_bumpIn (versions : List (Nat × Nat)) (contact : Nat) (h : contact ∈ versions.map (·.1)) :
    versionIn (bumpIn versions contact (versionIn versions contact)) contact = versionIn versions contact + 1 := by
  induction versions with
  | nil => simp at h
  | cons head tail ih =>
    obtain ⟨c, x⟩ := head
    by_cases hc : c = contact
    · subst hc; simp [versionIn, bumpIn]
    · have ht : contact ∈ tail.map (·.1) := by
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hc
        · exact h
      have := ih ht
      simpa [versionIn, bumpIn, hc] using this

/-- A contact the list does not hold is not added: its version stays 0 (a store for it would write
version 1 every time; the nodes would refuse the repeat). Every session puts each contact it sends
to in the list first (`Start.run`, `Serve.loadJob`), so this does not happen in the deployed paths. -/
theorem bumpIn_absent (versions : List (Nat × Nat)) (contact v : Nat) (h : contact ∉ versions.map (·.1)) :
    bumpIn versions contact v = versions := by
  induction versions with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨c, x⟩ := head
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hc : ¬c = contact := fun e => h.1 e.symm
    have := ih h.2
    simpa [bumpIn, hc] using this

/-- **`storeSoft`'s versions.** The version list moves to the contact's next version exactly when
the store was taken (and is unchanged otherwise, failures included). The write it submits is that
next version (`versionOf + 1`: the definition's text). -/
theorem storeSoft_versions (E : StoreEnv) (contact : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) :
    Model.wp (storeSoftG (storeModel E) contact) (fun r st' _ =>
      (r = .ok true → st'.contacts.versions =
        bumpIn st.contacts.versions contact (versionIn st.contacts.versions contact)) ∧
      (r ≠ .ok true → st'.contacts.versions = st.contacts.versions)) c st w := by
  have hn := isNone_false hdb
  store_unfold
  wp_step
  simp only [hn, Bool.false_eq_true, ↓reduceIte]
  clear hn hdb
  repeat' (split <;> try wp_step)
  all_goals simp_all [bumpIn, versionIn]

/-- **`storeAdvanced`'s versions.** With the database nodes, when it returns, the version list moved
to the contact's next version; when it fails, it is unchanged. -/
theorem storeAdvanced_versions (E : StoreEnv) (contact : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) :
    Model.wp (storeAdvancedG (storeModel E) contact) (fun r st' _ =>
      (r = .ok () → st'.contacts.versions =
        bumpIn st.contacts.versions contact (versionIn st.contacts.versions contact)) ∧
      (r ≠ .ok () → st'.contacts.versions = st.contacts.versions)) c st w := by
  store_unfold
  wp_step
  simp only [hdb, ↓reduceIte]
  clear hdb
  repeat' (split <;> try wp_step)
  all_goals simp_all [bumpIn, versionIn]

end TlsMpc.Node.Session.Events
