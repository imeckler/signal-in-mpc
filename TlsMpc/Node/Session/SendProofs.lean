import TlsMpc.Node.Session.Send
import TlsMpc.Node.Session.StoreProofs

/-!
# P4, ORD-1: one send (`sendDevices`, `sendMessage`, `sendSoft`)

Twins (`Events.lean`, design note) of `Session/Send.lean`'s `sendDevices`, `sendMessage` (the path
without recovery) and `sendSoft` (the recovery path), each proved equal to the deployed definition by
`rfl` (`*_deployed`), and in `Model`:

- `sendSoft_agreed`: with the database nodes, a run of `sendSoft` keeps `SendsAgreed`: its request
  (`Flow.Send.request` / `requestDevices`) is handed to the worker only after the contact's message
  was sealed, its advanced state sealed for storage, acknowledged by this party's nodes and
  reported acknowledged by the other party, with no seal of that contact in between. Both of its
  paths (one device, a device list) and every early return are covered.
- `sendMessage_acked`, `sendDevices_acked`: the same for the path without recovery, with this
  party's acknowledgement (`SendsAcked`; `storeAdvanced` fails the session otherwise).
- `*_keepsCommits`: none of them commits a scratch (they keep ORD-2's `CommitsAgreed`).
- `sendSoftGuarded`, `sendMessageGuarded`: the same computations as `Guarded` values, for the loops
  (`DeliverProofs.lean`, `LoopProofs.lean`).

No I/O primitive; no emitter imports this module.
-/

namespace TlsMpc.Node.Session.Events
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal TlsMpc.Node TlsMpc.Node.Bytes TlsMpc.Node.Session

/-- Every effect of one send besides the store's (`StoreOps`), `State` and `Context`. -/
structure SendOps (m : Type → Type) where
  store : StoreOps m
  liftResult : {α : Type} → Except String α → m α
  restamp : Nat × Bytes → m (Nat × Bytes)
  sealOne : Flow.Worker → Nat → Bytes → m (Opened .sealedEnvelope (Option (Nat × List Bytes)))
  sealDevices : Flow.Worker → Nat → Bytes → Bytes → Nat → m (Opened .sealedEnvelope (Option (Nat × List Bytes)))
  joint : Flow.Worker → m (Opened .jointRandom Bytes)
  recordSend : Nat → Nat → Nat → List (BitVec 8) → m Unit
  request : Flow.Worker → Nat → List Nat → Bytes → Bytes → m TlsWorker.BufferHandle
  requestDevices : Flow.Worker → Nat → Nat → List Nat → Nat → Bytes → Bytes → m TlsWorker.BufferHandle
  appSend : TlsApplication.Session TlsWorker.BufferHandle → TlsWorker.BufferHandle → Nat → m Unit

/-- The deployed operations. -/
def sendReal : SendOps SessionM where
  store := storeReal
  liftResult x := liftResult x
  restamp := Send.restamp
  sealOne w c b := Flow.Send.«seal» w c b
  sealDevices w c a b n := Flow.Send.sealDevices w c a b n
  joint w := Flow.Random.joint w
  recordSend := Send.recordSend
  request w c o m f := Flow.Send.request w c o m f
  requestDevices w c p o n m f := Flow.Send.requestDevices w c p o n m f
  appSend s h n := TlsApplication.send s h n

/-- `liftResult`, lifted into a session, is `match`: what the model uses. -/
theorem liftResult_session {α : Type} (x : Except String α) :
    (liftResult x : SessionM α) = (match x with | .ok a => pure a | .error e => throw e) := by
  cases x <;> rfl

section Twins
variable {m : Type → Type} [Monad m] [MonadExceptOf String m] [MonadStateOf State m] [MonadReaderOf Context m]

def appNowG : m (TlsApplication.Session TlsWorker.BufferHandle) := do
  let pool := (← get).pool
  return (pool.connection pool.current).session

def sendDevicesG (o : SendOps m) (send : Nat × Bytes) (id : Nat) : m Unit := do
  let c ← read
  let some (address, _) := c.self | throw "no account address for a device list"
  let count := (← kindsOfG send.1).length
  let some (timestamp, sealed) := (← o.sealDevices c.w send.1 address send.2 count).val
    | throw "invalid sealed envelopes reply"
  storeAdvancedG o.store send.1
  let envelopes := sealed.map toBits
  let random := (← o.joint c.w).val
  let (frame, payloadAt, offsets) ← o.liftResult (PublicRequest.buildDevices envelopes timestamp id (toBits (random.take 4)) c.official)
  -- Both request kernels seal one TLS record (about five unanswered devices; section 5).
  o.store.insist (frame.length ≤ 16384) "a send to this many devices does not fit one record"
  o.recordSend send.1 id timestamp frame
  let handle ← o.requestDevices c.w send.1 payloadAt offsets count (random.take 4) (toBytes frame)
  o.appSend (← appNowG) handle frame.length

def sendMessageG (o : SendOps m) (send : Nat × Bytes) (id : Nat) : m Unit := do
  let c ← read
  let send ← o.restamp send
  modify fun st => { st with lastSent := some send }
  if (← kindsOfG send.1) != [0] then return ← sendDevicesG o send id
  let some (timestamp, sealed) := (← o.sealOne c.w send.1 send.2).val | throw "invalid sealed envelope reply"
  storeAdvancedG o.store send.1
  let random := (← o.joint c.w).val
  let (frame, offsets) ← o.liftResult (PublicRequest.build (toBits (sealed.headD [])) timestamp id (toBits (random.take 4)) c.official)
  o.recordSend send.1 id timestamp frame
  let handle ← o.request c.w send.1 offsets (random.take 4) (toBytes frame)
  o.appSend (← appNowG) handle frame.length

def sendSoftG (o : SendOps m) (send : Nat × Bytes) (id : Nat) : m (Option (Recovery.Result × String × Bool)) := do
  let c ← read
  let send ← o.restamp send
  let unacknowledged := (Recovery.Result.retryLater, "the database nodes did not acknowledge the contact's state", false)
  let refused := (Recovery.Result.fault, "the contact's stored state cannot produce a message", true)
  let kinds ← kindsOfG send.1
  if kinds != [0] then
    let some (address, _) := c.self | throw "no account address for a device list"
    let some (timestamp, sealed) := (← o.sealDevices c.w send.1 address send.2 kinds.length).val
      | return some refused
    let envelopes := sealed.map toBits
    let random := (← o.joint c.w).val
    let (frame, payloadAt, offsets) ← o.liftResult (PublicRequest.buildDevices envelopes timestamp id (toBits (random.take 4)) c.official)
    -- Both request kernels seal one TLS record: about five unanswered devices (MULTI_DEVICE.md, section 5).
    if frame.length > 16384 then
      return some (.retryLater, s!"a message to {kinds.length} devices does not fit one request (not supported yet)", true)
    if !(← storeSoftG o.store send.1) then return some unacknowledged
    o.recordSend send.1 id timestamp frame
    let handle ← o.requestDevices c.w send.1 payloadAt offsets kinds.length (random.take 4) (toBytes frame)
    o.appSend (← appNowG) handle frame.length
    return none
  let some (timestamp, sealed) := (← o.sealOne c.w send.1 send.2).val | return some refused
  if !(← storeSoftG o.store send.1) then return some unacknowledged
  let random := (← o.joint c.w).val
  let (frame, offsets) ← o.liftResult (PublicRequest.build (toBits (sealed.headD [])) timestamp id (toBits (random.take 4)) c.official)
  o.recordSend send.1 id timestamp frame
  let handle ← o.request c.w send.1 offsets (random.take 4) (toBytes frame)
  o.appSend (← appNowG) handle frame.length
  return none

end Twins

theorem appNow_deployed : @appNow = appNowG (m := SessionM) := rfl
theorem sendDevices_deployed : @Send.sendDevices = sendDevicesG (m := SessionM) sendReal := rfl
theorem sendMessage_deployed : @Send.sendMessage = sendMessageG (m := SessionM) sendReal := rfl
theorem sendSoft_deployed : @Send.sendSoft = sendSoftG (m := SessionM) sendReal := rfl

/-! ### The model of one send -/

/-- The environment's answer to each operation's `i`-th call. `restamp` (a session function: a
curve preparation, a clock agreement, the restamped message) is a black box that may change the
session state; `recordSend` (the event record) one that reads it. -/
structure SendEnv where
  store : StoreEnv
  restamp : Nat × Bytes → Context → State → Nat → Except String (Nat × Bytes) × State
  sealOne : Nat → Bytes → Context → Nat → Except String (Opened .sealedEnvelope (Option (Nat × List Bytes)))
  sealDevices : Nat → Bytes → Bytes → Nat → Context → Nat → Except String (Opened .sealedEnvelope (Option (Nat × List Bytes)))
  joint : Context → Nat → Except String (Opened .jointRandom Bytes)
  recordSend : Nat → Nat → Nat → List (BitVec 8) → Context → State → Nat → Except String Unit
  request : Nat → List Nat → Bytes → Bytes → Context → Nat → Except String TlsWorker.BufferHandle
  requestDevices : Nat → Nat → List Nat → Nat → Bytes → Bytes → Context → Nat → Except String TlsWorker.BufferHandle
  appSend : TlsApplication.Session TlsWorker.BufferHandle → TlsWorker.BufferHandle → Nat → Context → Nat → Except String Unit

/-- One send in the model: a seal logs `seal c` (whatever its answer: conservative), a request
`request c`, the TLS send `transmit`; `liftResult` is the session's (`liftResult_session`). -/
def sendModel (E : SendEnv) : SendOps Model where
  store := storeModel E.store
  liftResult x := match x with | .ok a => pure a | .error e => throw e
  restamp s := Model.box (E.restamp s)
  sealOne _ c b := Model.atom (E.sealOne c b) (fun _ => .seal c)
  sealDevices _ c a b n := Model.atom (E.sealDevices c a b n) (fun _ => .seal c)
  joint _ := Model.atom E.joint (fun _ => .other "joint")
  recordSend c i t f := Model.rbox (E.recordSend c i t f)
  request _ c o k f := Model.atom (E.request c o k f) (fun _ => .request c)
  requestDevices _ c p o n k f := Model.atom (E.requestDevices c p o n k f) (fun _ => .request c)
  appSend s h n := Model.atom (E.appSend s h n) (fun _ => .transmit n)

@[simp] theorem step_seal_self (c : Nat) (ph : Phase) : step c ph (.seal c) = .sealed := by
  cases ph <;> simp [step, coreStep, Event.agrees]
@[simp] theorem step_transmit (c : Nat) (ph : Phase) (n : Nat) : step c ph (.transmit n) = ph.settle := by
  cases ph <;> rfl
@[simp] theorem settle_agreed : Phase.agreed.settle = .agreed := rfl
@[simp] theorem settle_sealed : Phase.sealed.settle = .sealed := rfl
@[simp] theorem ownAck_settle (ph : Phase) : ph.settle.ownAck = ph.ownAck := by cases ph <;> rfl

/-- The tactic of the send proofs: unfold, then split on every answer of the environment. -/
macro "send_unfold" : tactic => `(tactic| simp only [sendSoftG, sendMessageG, sendDevicesG, sendModel, kindsOfG,
  appNowG, storeModel])

/-! ### ORD-1 for one send -/

set_option maxHeartbeats 2000000 in
/-- **ORD-1, `sendSoft` (the recovery path; both paths, one device and a device list; every early
return).** With the database nodes, a run keeps `SendsAgreed`: the request it hands to the worker
comes after the contact's message was sealed, its advanced state sealed for storage, acknowledged
by this party's nodes and reported acknowledged by the other party, and no seal of the contact in
between; nothing else it does is a request. -/
theorem sendSoft_agreed (E : SendEnv) (send : Nat × Bytes) (id : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : SendsAgreed w.log) :
    Model.wp (sendSoftG (sendModel E) send id) (fun _ _ w' => SendsAgreed w'.log) c st w := by
  send_unfold
  wp_step
  repeat' (split <;> try wp_step)
  all_goals first
    | (keep_log stable_sendsAgreed; done)
    | (refine storeSoft_then E.store _ c _ _ hdb stable_sendsAgreed ?_ ?_ ?_
       · keep_log stable_sendsAgreed
       · simp
       · intro r st' w' hI hph
         split
         · try wp_step
           repeat' (split <;> try wp_step)
           all_goals first
             | (keep_log stable_sendsAgreed; done)
             | simp_all
         · exact hI)

set_option maxHeartbeats 2000000 in
/-- **ORD-1, `sendDevices` (the path without recovery, a device list).** With the database nodes, a
run keeps `SendsAcked`: its request comes after the message was sealed, its advanced state sealed
for storage and acknowledged by this party's nodes (`storeAdvanced`; it fails the session
otherwise), with no seal of the contact in between. -/
theorem sendDevices_acked (E : SendEnv) (send : Nat × Bytes) (id : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : SendsAcked w.log) :
    Model.wp (sendDevicesG (sendModel E) send id) (fun _ _ w' => SendsAcked w'.log) c st w := by
  send_unfold
  wp_step
  repeat' (split <;> try wp_step)
  all_goals first
    | (keep_log stable_sendsAcked; done)
    | (refine storeAdvanced_then E.store _ c _ _ hdb stable_sendsAcked ?_ ?_ ?_
       · keep_log stable_sendsAcked
       · simp
       · intro r st' w' hI hph
         split
         · try wp_step
           repeat' (split <;> try wp_step)
           all_goals first
             | (keep_log stable_sendsAcked; done)
             | simp_all
         · exact hI)

set_option maxHeartbeats 2000000 in
/-- **ORD-1, `sendMessage` (the path without recovery; one device, and a device list through
`sendDevices`).** As `sendDevices_acked`. -/
theorem sendMessage_acked (E : SendEnv) (send : Nat × Bytes) (id : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : SendsAcked w.log) :
    Model.wp (sendMessageG (sendModel E) send id) (fun _ _ w' => SendsAcked w'.log) c st w := by
  send_unfold
  wp_step
  repeat' (split <;> try wp_step)
  all_goals first
    | (keep_log stable_sendsAcked; done)
    | (refine storeAdvanced_then E.store _ c _ _ hdb stable_sendsAcked ?_ ?_ ?_
       · keep_log stable_sendsAcked
       · simp
       · intro r st' w' hI hph
         split
         · try wp_step
           repeat' (split <;> try wp_step)
           all_goals first
             | (keep_log stable_sendsAcked; done)
             | simp_all
         · exact hI)

/-- Close `I (e₁ :: … :: l)` when every `eᵢ` is a request or neither a request nor a commit. -/
macro "keep_req" hI:term "," hreq:term : tactic => `(tactic| repeat (first | assumption | apply $hreq |
  (refine Stable.cons $hI ?_ ?_ ?_ <;> try simp [Event.isRequest, Event.isCommit])))

/-- A send commits no scratch: `sendSoft` keeps every `Stable` property that a request keeps
(ORD-2's `CommitsAgreed`), with or without the database. -/
theorem sendSoft_keeps {I : List Event → Prop} (hI : Stable I) (hreq : ∀ c l, I l → I (.request c :: l))
    (E : SendEnv) (send : Nat × Bytes) (id : Nat) (c : Context) (st : State) (w : World) (hw : I w.log) :
    Model.wp (sendSoftG (sendModel E) send id) (fun _ _ w' => I w'.log) c st w := by
  send_unfold
  wp_step
  repeat' (split <;> try wp_step)
  all_goals first
    | (keep_req hI, hreq; done)
    | (refine Model.wp_mono (storeSoft_keeps hI E.store _ c _ _ ?_) ?_
       · keep_req hI, hreq
       · intro r st' w' hI'
         split
         · try wp_step
           repeat' (split <;> try wp_step)
           all_goals keep_req hI, hreq
         · exact hI')

/-- `sendMessage` likewise. -/
theorem sendMessage_keeps {I : List Event → Prop} (hI : Stable I) (hreq : ∀ c l, I l → I (.request c :: l))
    (E : SendEnv) (send : Nat × Bytes) (id : Nat) (c : Context) (st : State) (w : World) (hw : I w.log) :
    Model.wp (sendMessageG (sendModel E) send id) (fun _ _ w' => I w'.log) c st w := by
  send_unfold
  wp_step
  repeat' (split <;> try wp_step)
  all_goals first
    | (keep_req hI, hreq; done)
    | (refine Model.wp_mono (storeAdvanced_keeps hI E.store _ c _ _ ?_) ?_
       · keep_req hI, hreq
       · intro r st' w' hI'
         split
         · try wp_step
           repeat' (split <;> try wp_step)
           all_goals keep_req hI, hreq
         · exact hI')

/-! ### The sends as guarded computations (for the loops) -/

/-- `sendSoft` in the model, with its proof that it keeps ORD-1 (both parties' acknowledgement). -/
def sendSoftGuarded (E : SendEnv) (send : Nat × Bytes) (id : Nat) :
    Guarded SendsAgreed (Option (Recovery.Result × String × Bool)) :=
  ⟨sendSoftG (sendModel E) send id, fun c st w hdb hw => sendSoft_agreed E send id c st w hdb hw⟩

/-- `sendSoft` in the model, with its proof that it keeps ORD-2. -/
def sendSoftCommits (E : SendEnv) (send : Nat × Bytes) (id : Nat) :
    Guarded CommitsAgreed (Option (Recovery.Result × String × Bool)) :=
  ⟨sendSoftG (sendModel E) send id, fun c st w _ hw =>
    sendSoft_keeps stable_commitsAgreed (fun c _ h => commitsAgreed_request c h) E send id c st w hw⟩

/-- `sendMessage` in the model, with its proof that it keeps ORD-1 (own acknowledgement). -/
def sendMessageGuarded (E : SendEnv) (send : Nat × Bytes) (id : Nat) : Guarded SendsAcked Unit :=
  ⟨sendMessageG (sendModel E) send id, fun c st w hdb hw => sendMessage_acked E send id c st w hdb hw⟩

/-- `sendMessage` in the model, with its proof that it keeps ORD-2. -/
def sendMessageCommits (E : SendEnv) (send : Nat × Bytes) (id : Nat) : Guarded CommitsAgreed Unit :=
  ⟨sendMessageG (sendModel E) send id, fun c st w _ hw =>
    sendMessage_keeps stable_commitsAgreed (fun c _ h => commitsAgreed_request c h) E send id c st w hw⟩

end TlsMpc.Node.Session.Events
