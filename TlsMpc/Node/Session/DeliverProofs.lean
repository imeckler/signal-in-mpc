import TlsMpc.Node.Session.SendProofs

/-!
# P4 on the recovery path's loop: `deliverJob` (ORD-1 over every run, T11)

About `Session/Send.lean`'s `Send.deliverJobG` (with its tail `Send.resultsTailG`), whose instance
at `SessionM` and `Send.deliverReal` IS the deployed `deliverJob`.

- **ORD-1 over every run (`deliverJob_sendsAgreed`).** `deliverJob`'s two nested `while` loops are
  `Loop.forIn`, a `partial def` that no proof can unfold. The definition is therefore run in the guarded
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
open TlsMpc.Node.Session.Send (DeliverOps deliverReal resultsTailG deliverJobG)

/-- The per-id results of a notify, from the delivery loop's outcomes (`deliverJob`'s tail). -/
def resultEntries (inputs : List (Nat × Bytes)) (messageOf contactOf : Nat → Nat)
    (outcomes : Array (Option (Recovery.Result × String))) : List Recovery.Entry :=
  (List.range inputs.length).map (fun index =>
    let (result, reason) := (outcomes.getD index none).getD (.fault, "no outcome")
    (messageOf index, contactOf index, result, reason))

/-- The digest both controllers compare (`PeerMsg.resultsDigest`). -/
def resultsDigestOf (entries : List Recovery.Entry) : Bytes :=
  TlsWire.hash (Recovery.canonical entries).toUTF8.data.toList

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
