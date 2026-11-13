import TlsMpc.Node.Session.RefreshProofs

/-!
# P4 over the send loops: ORD-1 and ORD-2 for every run of `deliverJob` and `loop`

About `Session/Send.lean`'s `Send.loopG` (the send loop without recovery; the deployed `loop` is
`loopG` at `SessionM` and `Send.loopReal`) and `Send.deliverJobG`. In the guarded models, the
definitions of the loops with the definitions of what they call that matters:

| theorem | loop | property | from |
|---|---|---|---|
| `deliverJob_sendsAgreed'` | `deliverJob` (with its `refreshSoft`) | ORD-1, both parties | `sendSoft_agreed`, `commitScratch_keeps` |
| `deliverJob_commitsAgreed` | `deliverJob` (with its `refreshSoft`) | ORD-2 | `commitScratch_agreed`, `sendSoft_keeps` |
| `loop_sendsAcked` | `loop` (with its `refreshContact`) | ORD-1, own acknowledgement | `sendMessage_acked`, `commitScratch_keeps` |
| `loop_commitsAgreed` | `loop` (with its `refreshContact`) | ORD-2 | `commitScratch_agreed`, `sendMessage_keeps` |

In each, every other operation (`rest`, `R`) is ANY computation that keeps the property: in the
deployed code those are the functions that call neither `Flow.Send.request` / `requestDevices` nor
`Flow.Refresh.scratchCommit` (the only call sites are the deployed operations records
`Send.sendReal` and `storeReal`; checked by `scripts/lint_node.py`, rule `ordering-sites`).

No I/O primitive; no emitter imports this module.
-/

namespace TlsMpc.Node.Session.Events
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal TlsMpc.Node TlsMpc.Node.Bytes TlsMpc.Node.Session
open TlsMpc.Node.Session.Send (LoopOps loopReal loopG RefreshOps refreshReal refreshContactG refreshSoftG
  DeliverOps deliverJobG)

/-! ### The commit as a guarded operation -/

/-- `commitScratch` in the model, with its ORD-2 proof. -/
def commitScratchCommits (E : StoreEnv) (contact : Nat) (kinds : List Nat) : Guarded CommitsAgreed Bool :=
  ⟨commitScratchG (storeModel E) contact kinds, fun c st w hdb hw => commitScratch_agreed E contact kinds c st w hdb hw⟩

/-- `commitScratch` in the model, with its proof that it keeps a property no commit breaks. -/
def commitScratchKeeps {I : List Event → Prop} (hI : Stable I) (hc : ∀ c l, I l → I (.scratchCommit c :: l))
    (E : StoreEnv) (contact : Nat) (kinds : List Nat) : Guarded I Bool :=
  ⟨commitScratchG (storeModel E) contact kinds, fun c st w _ hw => commitScratch_keeps hI hc E contact kinds c st w hw⟩

/-- A refresh's operations with the given commit; every other operation is `R`'s. -/
def refreshWith {I : List Event → Prop} (commit : Nat → List Nat → Guarded I Bool) (R : RefreshOps (Guarded I)) :
    RefreshOps (Guarded I) :=
  { R with commitScratch := commit }

/-! ### `deliverJob` (the recovery path) -/

/-- ORD-1's model of `deliverJob`: the deployed `sendSoft` and the deployed `refreshSoft` (with the
deployed `commitScratch`); every other operation is `rest`'s / `R`'s. -/
def deliverSends (E : SendEnv) (rest : DeliverOps (Guarded SendsAgreed)) (R : RefreshOps (Guarded SendsAgreed)) :
    DeliverOps (Guarded SendsAgreed) :=
  { rest with
    sendSoft := sendSoftGuarded E
    refreshSoft := refreshSoftG (refreshWith (commitScratchKeeps stable_sendsAgreed (fun c _ h => sendsAgreed_commit c h) E.store) R) }

/-- **ORD-1 over every run of `deliverJob`, its refreshes included.** With the database nodes, every
run of the deployed text of `deliverJob` (with the deployed texts of `sendSoft`, `refreshSoft` and
the store functions) keeps `SendsAgreed`. -/
theorem deliverJob_sendsAgreed' (E : SendEnv) (rest : DeliverOps (Guarded SendsAgreed)) (R : RefreshOps (Guarded SendsAgreed))
    (inputs : List (Nat × Bytes)) (recipients : List Nat) (notifyId journal : Option String)
    (first : PublicReceive.State) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : SendsAgreed w.log) :
    SendsAgreed ((deliverJobG (deliverSends E rest R) inputs recipients notifyId journal first).1 c st w).2.2.log :=
  (deliverJobG (deliverSends E rest R) inputs recipients notifyId journal first).2 c st w hdb hw

/-- ORD-2's model of `deliverJob`. -/
def deliverCommits (E : SendEnv) (rest : DeliverOps (Guarded CommitsAgreed)) (R : RefreshOps (Guarded CommitsAgreed)) :
    DeliverOps (Guarded CommitsAgreed) :=
  { rest with
    sendSoft := sendSoftCommits E
    refreshSoft := refreshSoftG (refreshWith (commitScratchCommits E.store) R) }

/-- **ORD-2 over every run of `deliverJob`.** With the database nodes, every run of the deployed text
of `deliverJob` (with the deployed `sendSoft`, `refreshSoft`, `commitScratch`) keeps
`CommitsAgreed`: a refresh's device list becomes a contact's state only after both parties saw the
nodes acknowledge it; otherwise it is dropped. -/
theorem deliverJob_commitsAgreed (E : SendEnv) (rest : DeliverOps (Guarded CommitsAgreed)) (R : RefreshOps (Guarded CommitsAgreed))
    (inputs : List (Nat × Bytes)) (recipients : List Nat) (notifyId journal : Option String)
    (first : PublicReceive.State) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : CommitsAgreed w.log) :
    CommitsAgreed ((deliverJobG (deliverCommits E rest R) inputs recipients notifyId journal first).1 c st w).2.2.log :=
  (deliverJobG (deliverCommits E rest R) inputs recipients notifyId journal first).2 c st w hdb hw

/-! ### `loop` (the path without recovery) -/

/-- ORD-1's model of `loop`: the deployed `sendMessage` and the deployed `refreshContact` (with the
deployed `commitScratch`); every other operation is `rest`'s / `R`'s. -/
def loopSends (E : SendEnv) (rest : LoopOps (Guarded SendsAcked)) (R : RefreshOps (Guarded SendsAcked)) :
    LoopOps (Guarded SendsAcked) :=
  { rest with
    sendMessage := sendMessageGuarded E
    refreshContact := refreshContactG (refreshWith (commitScratchKeeps stable_sendsAcked (fun c _ h => sendsAcked_commit c h) E.store) R) }

/-- **ORD-1 over every run of `loop`, its refresh-and-resend included.** With the database nodes,
every run of the deployed text of `loop` keeps `SendsAcked`: every request comes after its own seal,
storage seal and this party's nodes' acknowledgement (the other party's nodes acknowledge to the
other party, which fails before the joint send otherwise). -/
theorem loop_sendsAcked (E : SendEnv) (rest : LoopOps (Guarded SendsAcked)) (R : RefreshOps (Guarded SendsAcked))
    (known : List (Nat × Secret Bytes × Nat)) (recipients : List Nat) (fuel : Nat) (s : PublicReceive.State)
    (inputs : List (Nat × Bytes)) (completed : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : SendsAcked w.log) :
    SendsAcked ((loopG (loopSends E rest R) known recipients fuel s inputs completed).1 c st w).2.2.log :=
  (loopG (loopSends E rest R) known recipients fuel s inputs completed).2 c st w hdb hw

/-- ORD-2's model of `loop`. -/
def loopCommits (E : SendEnv) (rest : LoopOps (Guarded CommitsAgreed)) (R : RefreshOps (Guarded CommitsAgreed)) :
    LoopOps (Guarded CommitsAgreed) :=
  { rest with
    sendMessage := sendMessageCommits E
    refreshContact := refreshContactG (refreshWith (commitScratchCommits E.store) R) }

/-- **ORD-2 over every run of `loop`.** -/
theorem loop_commitsAgreed (E : SendEnv) (rest : LoopOps (Guarded CommitsAgreed)) (R : RefreshOps (Guarded CommitsAgreed))
    (known : List (Nat × Secret Bytes × Nat)) (recipients : List Nat) (fuel : Nat) (s : PublicReceive.State)
    (inputs : List (Nat × Bytes)) (completed : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : CommitsAgreed w.log) :
    CommitsAgreed ((loopG (loopCommits E rest R) known recipients fuel s inputs completed).1 c st w).2.2.log :=
  (loopG (loopCommits E rest R) known recipients fuel s inputs completed).2 c st w hdb hw

end TlsMpc.Node.Session.Events
