import TlsMpc.Node.Session.RefreshProofs

/-!
# P4 over the send loops: ORD-1 and ORD-2 for every run of `deliverJob` and `loop`

A twin of `Session/Send.lean`'s `loop` (the send loop without recovery), proved equal to the
deployed definition (`loop_deployed`). Then, in the guarded models, the deployed texts of the loops
with the deployed texts of what they call that matters:

| theorem | loop | property | from |
|---|---|---|---|
| `deliverJob_sendsAgreed'` | `deliverJob` (with its `refreshSoft`) | ORD-1, both parties | `sendSoft_agreed`, `commitScratch_keeps` |
| `deliverJob_commitsAgreed` | `deliverJob` (with its `refreshSoft`) | ORD-2 | `commitScratch_agreed`, `sendSoft_keeps` |
| `loop_sendsAcked` | `loop` (with its `refreshContact`) | ORD-1, own acknowledgement | `sendMessage_acked`, `commitScratch_keeps` |
| `loop_commitsAgreed` | `loop` (with its `refreshContact`) | ORD-2 | `commitScratch_agreed`, `sendMessage_keeps` |

In each, every other operation (`rest`, `R`) is ANY computation that keeps the property: in the
deployed code those are the functions that call neither `Flow.Send.request` / `requestDevices` nor
`Flow.Refresh.scratchCommit` (the only call sites are `sendDevices`, `sendMessage`, `sendSoft` and
`commitScratch`; checked by `grep` in the P4 report).

No I/O primitive; no emitter imports this module.
-/

namespace TlsMpc.Node.Session.Events
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal TlsMpc.Node TlsMpc.Node.Bytes TlsMpc.Node.Session

/-- Every effect of `loop` besides `State` and `Context`. -/
structure LoopOps (m : Type → Type) where
  insist : Bool → String → m Unit
  liftResult : {α : Type} → Except String α → m α
  receive : TlsApplication.Session TlsWorker.BufferHandle → m (TlsApplication.Received TlsWorker.BufferHandle)
  record : Nat → PublicReceive.State → m (PublicReceive.State × Bool)
  controlMasks : Flow.Worker → PublicReceive.State → m (List (List (BitVec 8)))
  sendPublic : Bytes → m Unit
  joint : Flow.Worker → m (Opened .jointRandom Bytes)
  refreshContact : Nat → PublicReceive.State → m PublicReceive.State
  nextId : m Nat
  sendMessage : Nat × Bytes → Nat → m Unit
  awaitReply : Nat → PublicReceive.State → m PublicReceive.State
  keyUpdate : TlsApplication.Session TlsWorker.BufferHandle → Bool → m Unit
  reloadContacts : List (Nat × Secret Bytes × Nat) → m Unit
  ensurePrepared : Nat → List Nat → m Unit
  toCircuit : List Nat → PublicReceive.State → Nat → Nat → m (PublicReceive.State × Nat)

/-- The deployed operations. -/
def loopReal : LoopOps SessionM where
  insist b e := insist b e
  liftResult x := liftResult x
  receive s := TlsApplication.receive s
  record := record
  controlMasks w s := controlMasks w s
  sendPublic := sendPublic
  joint w := Flow.Random.joint w
  refreshContact := Send.refreshContact
  nextId := nextId
  sendMessage := Send.sendMessage
  awaitReply := awaitReply
  keyUpdate s b := TlsApplication.keyUpdate s b
  reloadContacts := reloadContacts
  ensurePrepared := Send.ensurePrepared
  toCircuit := toCircuit

section Twins
variable {m : Type → Type} [Monad m] [MonadExceptOf String m] [MonadStateOf State m] [MonadReaderOf Context m]

def loopG (o : LoopOps m) (known : List (Nat × Secret Bytes × Nat)) (recipients : List Nat) :
    Nat → PublicReceive.State → List (Nat × Bytes) → Nat → m Nat
  | 0, _, _, _ => throw "receive budget exhausted"
  | fuel+1, s, inputs, completed => do
    let c ← read
    match ← o.receive (← appNowG) with
    | .application handle =>
      let wasPending := s.pending
      let (s, complete) ← o.record handle.id s
      -- The mask is public but must be the same for both controllers: joint randomness.
      let (s, frames) ← o.liftResult (PublicReceive.replies s (← o.controlMasks c.w s))
      for (kind, frame) in frames do
        o.sendPublic (toBytes frame)
        o.insist (kind != 8) "WebSocket peer closed before completion"
      -- Replies to completed server requests (each with its own joint mask).
      for request in s.requests do
        let random := (← o.joint c.w).val
        let (frame, message) ← o.liftResult (PublicReceive.reply request (toBits (random.take 4)))
        -- Nothing is received on this socket: a delivered message is left unacknowledged.
        unless message do o.sendPublic (toBytes frame)
      let s := { s with requests := [] }
      o.insist (!complete || wasPending) "unsolicited service response"
      -- A send refused for the contact's device list (409, 410): the contact's sessions are
      -- replaced and the message is sent again. Bounded: one refresh and one resend per message;
      -- a second refusal ends the session.
      let s ← if complete && s.lenient && (s.status == 409 || s.status == 410) then do
          let some input := (← get).lastSent | throw "no send to repeat"
          let refreshed ← o.refreshContact input.1 s
          let id ← o.nextId
          o.sendMessage input id
          let answered ← o.awaitReply 64 (PublicReceive.expect refreshed id)
          o.insist (200 ≤ answered.status && answered.status < 300) s!"the resend after a device refresh was answered {answered.status}"
          pure answered
        else do
          -- (Without `lenient` the parser has already refused anything but a success.)
          o.insist (!complete || !s.lenient || (200 ≤ s.status && s.status < 300)) s!"service response was not a success: {s.status}"
          pure s
      let finished := completed + (if complete then 1 else 0)
      -- (No KeyUpdate of our own under the libsignal profile: BoringSSL never sends one.)
      if complete && finished == 1 && !c.official then o.keyUpdate (← appNowG) false
      if s.upgraded && !s.pending then
        match inputs with
        | [] => o.insist (finished > 0) "private provider supplied no requests"; return finished
        | input::tail =>
          -- Request ids are public: a counter from 2^63, as the service expects.
          let id := 2 ^ 63 + finished
          if finished == 2 then o.reloadContacts known
          if finished == 2 then modifyContactsG fun k => { k with prepared := [] }   -- reloaded contacts are unprepared
          o.ensurePrepared input.1 (tail.map (·.1))
          -- Several circuits: the contact's connection, its parser state and request id.
          let (s, id) ← o.toCircuit recipients s input.1 id
          o.sendMessage input id
          loopG o known recipients fuel (PublicReceive.expect s id) tail finished
      else loopG o known recipients fuel s inputs finished
    | .control => loopG o known recipients fuel s inputs completed
    | .closed => throw "TLS closed before private responses"

end Twins

/-- The twin at the deployed operations is the deployed `loop` (by induction on the fuel: one
unfolding of each side, the same text). -/
theorem loop_deployed (known : List (Nat × Secret Bytes × Nat)) (recipients : List Nat) :
    ∀ fuel s inputs completed, Send.loop known recipients fuel s inputs completed =
      loopG (m := SessionM) loopReal known recipients fuel s inputs completed := by
  intro fuel
  induction fuel with
  | zero => intro s inputs completed; rfl
  | succ fuel ih =>
    intro s inputs completed
    simp only [Send.loop, loopG, ih]
    rfl

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
