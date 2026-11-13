import TlsMpc.Node.Session.SendProofs

/-!
# P4 on the recovery path's loop: `deliverJob` (ORD-1 over every run, T11)

A twin of `Session/Send.lean`'s `deliverJob`, proved equal to the deployed definition by `rfl`
(`deliverJob_deployed`). Its text is the deployed text, except that the code after the delivery
loop is the separate definition `resultsTailG` (the deployed function has the same code inline; the
`rfl` proof checks they agree).

- **ORD-1 over every run (`deliverJob_sendsAgreed`).** `deliverJob`'s two nested `while` loops are
  `Loop.forIn`, a `partial def` that no proof can unfold. The twin is therefore run in the guarded
  model `Guarded SendsAgreed`: its `sendSoft` is the model of the deployed `sendSoft` with its proof
  `sendSoft_agreed`, and every other operation (the journal, the peer exchanges, the clock, the
  waits for responses, reconnects, refreshes, notes, the parser states) is ANY computation that
  keeps `SendsAgreed`, in particular any that hands no message request to the worker. Whatever the
  loops do, the run keeps `SendsAgreed`: every request of the run (all of them come from
  `sendSoft`, in the deployed code) was preceded by its own seal, storage seal and both parties'
  acknowledgements; a resend after a lost connection or a refresh reseals.
- **T11 (`deliverJob_results`, `resultsTail_spec`).** In the model, with the peer exchange an
  environment call that logs its event and every other operation ANY computation: when
  `deliverJob` returns, the newest event of the log is the results-digest exchange in which the other
  party's digest is our own, and that digest is the digest of the per-id results the session state
  now reports (`Report.results`). On a different digest (or no digest) the tail fails and leaves the
  session state, `Report.results` included, as it found it.

No I/O primitive; no emitter imports this module.
-/

namespace TlsMpc.Node.Session.Events
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal TlsMpc.Node TlsMpc.Node.Bytes TlsMpc.Node.Session

/-- Every effect of `deliverJob` besides `State` and `Context`. -/
structure DeliverOps (m : Type → Type) where
  insist : Bool → String → m Unit
  peer : PeerMsg → m PeerMsg
  note : String → m Unit
  readJournal : Channels → String → String → m (List JournalEntry)
  sleep : Channels → Nat → m Unit
  agreedClock : m Nat
  ensurePrepared : Nat → List Nat → m Unit
  sendSoft : Nat × Bytes → Nat → m (Option (Recovery.Result × String × Bool))
  awaitSoft : Nat → PublicReceive.State → m (PublicReceive.State × Bool)
  record : Channels → RecordEvent → m Unit
  reconnect : m Unit
  saveState : PublicReceive.State → m Unit
  refreshSoft : Nat → PublicReceive.State → m (PublicReceive.State × Recovery.Refreshed)
  keyUpdate : TlsApplication.Session TlsWorker.BufferHandle → Bool → m Unit
  journal : Channels → String → JournalLine → m Unit

/-- The deployed operations. -/
def deliverReal : DeliverOps SessionM where
  insist b e := insist b e
  peer := peer
  note := note
  readJournal ch path named := ch.readJournal path named
  sleep ch ms := ch.sleep ms
  agreedClock := agreedClock
  ensurePrepared := Send.ensurePrepared
  sendSoft := Send.sendSoft
  awaitSoft := awaitSoft
  record ch e := ch.record e
  reconnect := reconnect
  saveState := saveState
  refreshSoft := Send.refreshSoft
  keyUpdate s b := TlsApplication.keyUpdate s b
  journal ch path line := ch.journal path line

section Twins
variable {m : Type → Type} [Monad m] [MonadExceptOf String m] [MonadStateOf State m] [MonadReaderOf Context m]

def modifyReportG (f : Report → Report) : m Unit := modify fun s => { s with report := f s.report }
def modifyPoolG (f : Pool → Pool) : m Unit := modify fun s => { s with pool := f s.pool }

/-- The per-id results of a notify, from the delivery loop's outcomes (`deliverJob`'s tail). -/
def resultEntries (inputs : List (Nat × Bytes)) (messageOf contactOf : Nat → Nat)
    (outcomes : Array (Option (Recovery.Result × String))) : List Recovery.Entry :=
  (List.range inputs.length).map (fun index =>
    let (result, reason) := (outcomes.getD index none).getD (.fault, "no outcome")
    (messageOf index, contactOf index, result, reason))

/-- The digest both controllers compare (`PeerMsg.resultsDigest`). -/
def resultsDigestOf (entries : List Recovery.Entry) : Bytes :=
  TlsWire.hash (Recovery.canonical entries).toUTF8.data.toList

/-- `deliverJob`'s tail: the per-id results, agreed by digest, then reported (T11). -/
def resultsTailG (o : DeliverOps m) (inputs : List (Nat × Bytes)) (messageOf contactOf : Nat → Nat)
    (outcomes : Array (Option (Recovery.Result × String))) (delivered : Nat) : m Nat := do
  -- The per-id results. Both controllers computed them from agreed values: they compare a digest
  -- (through the worker's exchange) and report only what both arrived at.
  let entries : List Recovery.Entry := (List.range inputs.length).map (fun index =>
    let (result, reason) := (outcomes.getD index none).getD (.fault, "no outcome")
    (messageOf index, contactOf index, result, reason))
  let digest := TlsWire.hash (Recovery.canonical entries).toUTF8.data.toList
  let theirDigest ← match ← o.peer (.resultsDigest digest) with
    | .resultsDigest theirs => pure theirs
    | _ => throw "invalid results-digest reply"
  o.insist (theirDigest == digest) "the two parties' per-id results differ"
  modifyReportG fun r => { r with results := entries }
  return delivered

def deliverJobG (o : DeliverOps m) (inputs : List (Nat × Bytes)) (recipients : List Nat) (notifyId journal : Option String)
    (first : PublicReceive.State) : m Nat := do
  let c ← read
  modifyReportG fun r => { r with recoveryUsed := true }
  let count := max c.sendCircuits 1
  let settled ← match notifyId, journal with
    | some named, some path => do
      let mine ← o.readJournal c.ch path named
      let theirs ← match ← o.peer (.journal mine) with
        | .journal entries => pure entries
        | _ => throw "invalid journal reply"
      -- The same entry: the same 21 bytes on the link (`JournalEntry.encode`).
      let both := mine.filter (fun entry => theirs.any (fun other => other.encode == entry.encode))
      if !mine.isEmpty then o.note s!"{both.length} results settled by an earlier session of this notify"
      pure both
    | _, _ => pure []
  let contactOf (index : Nat) : Nat := (inputs.getD index (0, [])).1
  -- The message's number within the notify, for its contact.
  let messageOf (index : Nat) : Nat := ((inputs.take index).filter (·.1 == contactOf index)).length
  let mut outcomes : Array (Option (Recovery.Result × String)) := Array.replicate inputs.length none
  -- Contacts no longer sent to in this session, with the result that stopped them. From the start:
  -- those whose stored state did not open under their key.
  let mut stopped : List (Nat × Recovery.Result × String) :=
    (← get).contacts.unreadable.map (fun contact =>
      (contact, Recovery.Result.fault, "the contact's stored state does not open under its key"))
  -- Inputs during whose delivery the contact's sessions were replaced (and under a new identity key).
  let mut refreshedInputs : List Nat := []
  let mut changedInputs : List Nat := []
  -- The queue: (input, transient retries so far, not before this agreed time).
  let mut queue : List (Nat × Nat × Nat) := (List.range inputs.length).map (fun index => (index, 0, 0))
  let mut delivered := 0
  let mut rotated := false
  let mut rounds := 0
  -- TEST hook (SIGNAL_LOCAL_PAUSE_AFTER=K:MS): one pause once K inputs have a result, so that the
  -- harness can change something on the server in the middle of a session.
  let pauseAfter := c.hooks.pauseAfter
  let mut paused := false
  while !queue.isEmpty do
    rounds := rounds + 1
    o.insist (rounds ≤ 64 + 8 * inputs.length) "delivery budget exhausted"
    if let some (after, pause) := pauseAfter then
      if !paused && (outcomes.toList.filter Option.isSome).length ≥ after then
        paused := true
        o.note s!"TEST pause of {pause} ms after {after} results"
        o.sleep c.ch pause
    let now ← o.agreedClock
    let (index, retries, _) ← match queue.find? (fun (_, _, notBefore) => notBefore ≤ now) with
      | some item => pure item
      | none => do
        -- Everything left is backing off: both controllers wait for the soonest.
        let soonest := (queue.map (·.2.2)).foldl min (now + Recovery.longestWait)
        o.sleep c.ch (soonest - now)
        pure ((queue.find? (fun (_, _, notBefore) => notBefore == soonest)).getD (0, 0, 0))
    queue := queue.filter (·.1 != index)
    let input := inputs.getD index (0, [])
    let contact := input.1
    let message := messageOf index
    if let some (_, _, result) := settled.find? (fun (m, c, _) => m == message && c == contact) then
      outcomes := outcomes.set! index (some (result, "settled by an earlier session of this notify"))
      continue
    if let some (_, result, reason) := stopped.find? (·.1 == contact) then
      outcomes := outcomes.set! index (some (result, reason))
      continue
    let mut final : Option (Recovery.Result × String) := none
    let mut again : Option (Nat × Option Nat) := none
    let mut refreshes := 0
    let mut lost := 0
    let mut tries := 0
    while final.isNone && again.isNone do
      tries := tries + 1
      if tries > 16 then
        final := some (.retryLater, "attempts exhausted")
        break
      -- The contact's connection, its parser state and the request's id.
      let target := Circuits.assign recipients count contact
      modifyReportG fun r => { r with circuitSends := r.circuitSends ++ [(contact, target)] }
      modifyPoolG fun p => { p with current := target }
      let sent := (← get).pool.counters.getD target 0
      modifyPoolG fun p => { p with counters := p.counters.set! target (sent + 1) }
      let id := 2 ^ 63 + sent
      let s := (← get).pool.states.getD target first
      o.ensurePrepared contact (queue.map (fun (later, _, _) => contactOf later))   -- with the contacts that follow, in the same field rounds
      match ← o.sendSoft input id with
      | some (result, reason, stop) =>
        final := some (result, reason)
        if stop && !result.stops then stopped := stopped ++ [(contact, result, reason)]
        break
      | none => pure ()
      let (s, alive) ← o.awaitSoft 64 (PublicReceive.expect s id)
      o.record c.ch (.response contact message id alive s.status s.retryAfter)
      if !alive then
        -- Sent, not answered: whether the server took it is unknown. It is sent again (under new
        -- keys), accepting a duplicate.
        o.reconnect
        lost := lost + 1
        if lost > Recovery.reconnects then final := some (.retryLater, s!"the connection was closed {lost} times")
        continue
      o.saveState s
      match Recovery.onSend s.status with
      | .done =>
        final := some (if changedInputs.contains index then .deliveredAfterIdentityChange
          else if refreshedInputs.contains index then .deliveredAfterRefresh else .delivered, "")
      | .backOff => again := some (s.status, s.retryAfter)
      | .stop result => final := some (result, s!"the send was answered {s.status}")
      | .refresh =>
        if refreshes > Recovery.refreshRetries then
          final := some (.retryLater, s!"the device list was refused again after {refreshes} refreshes")
        else
          refreshes := refreshes + 1
          o.note s!"contact {contact}: send answered {s.status}, refresh {refreshes}"
          let (s, outcome) ← o.refreshSoft contact s
          match outcome with
          | .ok changed =>
            o.saveState s
            refreshedInputs := refreshedInputs ++ [index]
            if changed then changedInputs := changedInputs ++ [index]
          | .lost =>
            o.reconnect
            refreshes := refreshes - 1
            lost := lost + 1
            if lost > Recovery.reconnects then final := some (.retryLater, s!"the connection was closed {lost} times")
          | .stop result reason =>
            o.saveState s
            final := some (result, reason)
          | .transient status retryAfter =>
            o.saveState s
            again := some (status, retryAfter)
    match final, again with
    | some (result, reason), _ =>
      outcomes := outcomes.set! index (some (result, reason))
      if !reason.isEmpty then o.note s!"contact {contact}, message {message}: {result.text} ({reason})"
      if result.stops then stopped := stopped ++ [(contact, result, reason)]
      if result.isDelivered then
        delivered := delivered + 1
        if !rotated then
          rotated := true
          -- (Not under the libsignal profile: BoringSSL never sends a KeyUpdate of its own.)
          unless c.official do o.keyUpdate (← appNowG) false
      if result.settled then
        match notifyId, journal with
        | some named, some path =>
          o.journal c.ch path { notify := named, entry := (message, contact, result, reason) }
        | _, _ => pure ()
    | none, some (status, retryAfter) =>
      match Recovery.delay retries retryAfter with
      | some wait =>
        o.note s!"contact {contact}, message {message}: answered {status}, retry {retries + 1} in {wait} ms"
        queue := queue ++ [(index, retries + 1, (← o.agreedClock) + wait)]
      | none =>
        let reason := s!"answered {status}" ++ (match retryAfter with | some seconds => s!", Retry-After {seconds} s" | none => "") ++
          s!", after {retries} retries"
        o.note s!"contact {contact}, message {message}: retry later ({reason})"
        outcomes := outcomes.set! index (some (.retryLater, reason))
    | none, none => pure ()
  resultsTailG o inputs messageOf contactOf outcomes delivered

end Twins

theorem modifyReport_deployed : @modifyReport = modifyReportG (m := SessionM) := rfl
theorem modifyPool_deployed : @modifyPool = modifyPoolG (m := SessionM) := rfl
theorem deliverJob_deployed : @Send.deliverJob = deliverJobG (m := SessionM) deliverReal := rfl

/-! ### ORD-1 over every run of `deliverJob` -/

/-- The deliver operations in the guarded model: `sendSoft` is the model of the deployed `sendSoft`
with its ORD-1 proof (`sendSoftGuarded`); every other operation is `rest`'s, i.e. ANY computation
that keeps `SendsAgreed` (for instance any that logs no request: `Guarded.box`, `quietGuarded`). -/
def deliverGuarded (E : SendEnv) (rest : DeliverOps (Guarded SendsAgreed)) : DeliverOps (Guarded SendsAgreed) :=
  { rest with sendSoft := sendSoftGuarded E }

/-- **ORD-1 over every run of `deliverJob` (the recovery path; `deliver` and every job of `serve`).**
With the database nodes, from a log satisfying `SendsAgreed`, every run of the deployed text of
`deliverJob` (in the guarded model above) ends in a log satisfying `SendsAgreed`: every request it
hands to the worker comes after that message's seal, the storage seal of the advanced state, this
party's nodes' acknowledgement and the other party's report of its own, with no seal of the contact
in between; two requests to a contact need two seals and two acknowledged stores (a resend after a
lost connection, a back-off or a refresh reseals). Holds whatever the loops, the server, the
network, the database nodes and the other party do. -/
theorem deliverJob_sendsAgreed (E : SendEnv) (rest : DeliverOps (Guarded SendsAgreed))
    (inputs : List (Nat × Bytes)) (recipients : List Nat) (notifyId journal : Option String)
    (first : PublicReceive.State) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : SendsAgreed w.log) :
    SendsAgreed ((deliverJobG (deliverGuarded E rest) inputs recipients notifyId journal first).1 c st w).2.2.log :=
  (deliverJobG (deliverGuarded E rest) inputs recipients notifyId journal first).2 c st w hdb hw

/-- A computation whose every run only prepends events that are not requests. -/
def LogsNoRequest {α : Type} (x : Model α) : Prop :=
  ∀ c st w, ∃ seg, (x c st w).2.2.log = seg ++ w.log ∧ ∀ e ∈ seg, e.isRequest = false

theorem sendsAgreed_prepend {seg : List Event} (h : ∀ e ∈ seg, e.isRequest = false) {l : List Event}
    (hl : SendsAgreed l) : SendsAgreed (seg ++ l) := by
  induction seg with
  | nil => exact hl
  | cons e s ih =>
    refine ⟨ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')), fun c he => ?_⟩
    subst he; simp [Event.isRequest] at h

/-- Any computation that logs no request is a guarded operation (whatever else it does). -/
def quietGuarded {α : Type} (x : Model α) (h : LogsNoRequest x) : Guarded SendsAgreed α :=
  ⟨x, fun c st w _ hw => by
    obtain ⟨seg, he, hs⟩ := h c st w
    rw [he]; exact sendsAgreed_prepend hs hw⟩

/-! ### T11 -/

/-- What the application is told is agreed: the newest event of the log is the results-digest
exchange in which the other party's digest is our own, the digest of the reported results. -/
def ResultsAgreed (st : State) (w : World) : Prop :=
  ∃ rest, w.log = .peer (.resultsDigest (resultsDigestOf st.report.results))
    (some (.resultsDigest (resultsDigestOf st.report.results))) :: rest

/-- `deliverJob`'s operations for T11: the peer exchange is an environment call that logs its event
(`P`: any answer), `insist` is the session's; every other operation is `o`'s, ANY computation. -/
def deliverT11 (P : PeerMsg → Context → Nat → Except String PeerMsg) (o : DeliverOps Model) : DeliverOps Model :=
  { o with peer := fun msg => Model.atom (P msg) (peerEvent msg), insist := fun b e => if b then pure () else throw e }

/-- **T11, the tail.** When it returns, `ResultsAgreed`; when it fails (a different digest, or a reply
that is not a digest), the session state is as it found it: `Report.results` is not set. -/
theorem resultsTail_spec (P : PeerMsg → Context → Nat → Except String PeerMsg) (o : DeliverOps Model)
    (inputs : List (Nat × Bytes)) (messageOf contactOf : Nat → Nat)
    (outcomes : Array (Option (Recovery.Result × String))) (delivered : Nat) (c : Context) (st : State) (w : World) :
    Model.wp (resultsTailG (deliverT11 P o) inputs messageOf contactOf outcomes delivered) (fun r st' w' =>
      (∀ n, r = .ok n → ResultsAgreed st' w') ∧ (∀ e, r = .error e → st' = st)) c st w := by
  simp only [resultsTailG, deliverT11, modifyReportG]
  wp_step
  repeat' (split <;> try wp_step)
  all_goals simp_all [ResultsAgreed, resultsDigestOf]

theorem ite_intro {p : Prop} [Decidable p] {A B : Prop} (ha : p → A) (hb : ¬p → B) : if p then A else B := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

/-- **T11 (`deliverJob`).** Whatever the delivery loops did (they are opaque `while` loops) and
whatever every operation but the peer exchange does: when `deliverJob` returns, `ResultsAgreed`
holds of the final state and log. -/
theorem deliverJob_results (P : PeerMsg → Context → Nat → Except String PeerMsg) (o : DeliverOps Model)
    (inputs : List (Nat × Bytes)) (recipients : List Nat) (notifyId journal : Option String)
    (first : PublicReceive.State) (c : Context) (st : State) (w : World) :
    Model.wp (deliverJobG (deliverT11 P o) inputs recipients notifyId journal first)
      (fun r st' w' => ∀ n, r = .ok n → ResultsAgreed st' w') c st w := by
  unfold deliverJobG
  repeat' (first
    | exact Model.wp_mono (resultsTail_spec P o _ _ _ _ _ _ _ _) (fun _ _ _ h => h.1)
    | refine Model.wp_bind_ok (fun _ _ _ _ => ?_) (fun _ _ _ _ h => nomatch h) _ _ _
    | split
    | (simp only [Model.wp_ite]; refine ite_intro (fun _ => ?_) (fun _ => ?_))
    | dsimp only)

end TlsMpc.Node.Session.Events
