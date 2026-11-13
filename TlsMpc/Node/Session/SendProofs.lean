import TlsMpc.Node.Session.Send
import TlsMpc.Node.Session.StoreProofs

/-!
# P4, ORD-1: one send (`sendDevices`, `sendMessage`, `sendSoft`)

About the definitions of `Session/Send.lean`, `Send.sendDevicesG`, `Send.sendMessageG` (the path
without recovery) and `Send.sendSoftG` (the recovery path), whose instances at `SessionM` and
`Send.sendReal` ARE the deployed `sendDevices`, `sendMessage`, `sendSoft`; in `Model`, at any
environment (`sendModel E`):

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
open TlsMpc.Node.Session.Send (SendOps sendReal sendDevicesG sendMessageG sendSoftG)

/-- `liftResult`, lifted into a session, is `match`: what the model uses for `SendOps.liftResult`
(the deployed `sendReal.liftResult`). -/
theorem liftResult_session {α : Type} (x : Except String α) :
    (liftResult x : SessionM α) = (match x with | .ok a => pure a | .error e => throw e) := by
  cases x <;> rfl

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
