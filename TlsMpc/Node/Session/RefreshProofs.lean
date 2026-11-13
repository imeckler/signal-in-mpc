import TlsMpc.Node.Session.DeliverProofs

/-!
# P4: a device refresh (`refreshContact`, `refreshSoft`) and ORD-2 inside it

Twins of `Session/Send.lean`'s `refreshContact` (the path without recovery) and `refreshSoft` (the
recovery path), proved equal to the deployed definitions by `rfl`. Both reach the scratch's commit
only through `commitScratch` (an operation of the twin here). In the guarded models:

- `refreshCommits`: with `commitScratch` the model of the deployed one with its ORD-2 proof
  (`commitScratch_agreed`) and every other operation any computation that commits no scratch, both
  refreshes are `Guarded CommitsAgreed` (by their type, whatever their `for` loops do);
- `refreshSends`: with `commitScratch` the model of the deployed one with its proof that it hands
  no request to the worker (`commitScratch_keeps`), both refreshes are `Guarded SendsAgreed` /
  `Guarded SendsAcked`: a refresh never sends a message (its prekey fetch is not a message
  request).

No I/O primitive; no emitter imports this module.
-/

namespace TlsMpc.Node.Session.Events
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal TlsMpc.Node TlsMpc.Node.Bytes TlsMpc.Node.Session

/-- Every effect of a device refresh besides `State` and `Context`. -/
structure RefreshOps (m : Type → Type) where
  insist : Bool → String → m Unit
  liftResult : {α : Type} → Except String α → m α
  nextId : m Nat
  joint : Flow.Worker → m (Opened .jointRandom Bytes)
  recordFetch : Nat → Nat → List (BitVec 8) → m Unit
  fetch : Flow.Worker → Nat → Nat → List Nat → Bytes → Bytes → m TlsWorker.BufferHandle
  appSend : TlsApplication.Session TlsWorker.BufferHandle → TlsWorker.BufferHandle → Nat → m Unit
  touch : m Unit
  awaitReply : Nat → PublicReceive.State → m PublicReceive.State
  keepAlive : PublicReceive.State → m PublicReceive.State
  shape : Flow.Worker → m (Option (Opened .bundleShape (List Bool)))
  establish : Flow.Worker → Nat → Nat → Nat → Nat → Nat → Nat → Bool → BundleResponse.Widths →
    m (Opened .deviceStatus Bytes)
  log : Channels → LogLine → m Unit
  commitScratch : Nat → List Nat → m Bool
  drop : Flow.Worker → m Unit
  awaitSoft : Nat → PublicReceive.State → m (PublicReceive.State × Bool)
  keepAliveSoft : PublicReceive.State → m (PublicReceive.State × Bool)
  note : String → m Unit
  sleep : Channels → Nat → m Unit

/-- The deployed operations. -/
def refreshReal : RefreshOps SessionM where
  insist b e := insist b e
  liftResult x := liftResult x
  nextId := nextId
  joint w := Flow.Random.joint w
  recordFetch := Send.recordFetch
  fetch w c p o k f := Flow.Refresh.fetch w c p o k f
  appSend s h n := TlsApplication.send s h n
  touch := touch
  awaitReply := awaitReply
  keepAlive := keepAlive
  shape w := Flow.Refresh.shape w
  establish w c r i d s a sl it := Flow.Refresh.establish w c r i d s a sl it
  log ch line := ch.log line
  commitScratch := commitScratch
  drop w := Flow.Refresh.drop w
  awaitSoft := awaitSoft
  keepAliveSoft := keepAliveSoft
  note := note
  sleep ch ms := ch.sleep ms

section Twins
variable {m : Type → Type} [Monad m] [MonadExceptOf String m] [MonadStateOf State m] [MonadReaderOf Context m]

def refreshContactG (o : RefreshOps m) (contact : Nat) (start : PublicReceive.State) : m PublicReceive.State := do
  let c ← read
  let some (_, registration) := c.self | throw "no account for a device refresh"
  o.insist (0 < registration && registration < 2 ^ 32) "the export has no registration id for the account"
  -- The fetch names the contact: its UUID and access key are inserted by the engines.
  let fetchId ← o.nextId
  let random := (← o.joint c.w).val
  let (frame, payloadAt, offsets) ← o.liftResult (PublicRequest.buildFetch fetchId (toBits (random.take 4)))
  o.recordFetch contact fetchId frame
  let handle ← o.fetch c.w contact payloadAt offsets (random.take 4) (toBytes frame)
  o.appSend (← appNowG) handle frame.length
  o.touch
  -- Its body is collected unrevealed (`PublicReceive.step`: only a 200 with this id).
  let fetched ← o.awaitReply 64 { PublicReceive.expect start fetchId with fetch := some fetchId, bundle := none }
  let mut s := { fetched with fetch := none }
  -- 404: the account is gone; 401: the access key no longer matches. Neither is retried.
  o.insist (s.status == 200) s!"the prekey fetch was answered {s.status}"
  let some size := s.bundle | throw "prekey response without a body"
  o.insist (2540 ≤ size && size ≤ 65536) "prekey response size"
  s ← o.keepAlive s
  -- The one thing opened about the body: which of its bytes are JSON punctuation.
  let some flags ← o.shape c.w | throw "invalid bundle shape"
  o.insist (flags.val.length == size) "invalid bundle shape"
  -- In the clear, by both controllers: the devices' layout, if the flags are exactly a response's.
  let some widths := BundleResponse.layout? flags.val | throw "prekey response layout refused"
  let rows := (BundleResponse.starts BundleResponse.firstItem widths).zip widths
  o.insist (1 ≤ rows.length && rows.length ≤ 6) "device count"
  let slots := c.config.agreed.bundleSlots
  for ((at_, item), index) in rows.zipIdx do
    for step in [0:9] do
      s ← o.keepAlive s
      let out := (← o.establish c.w contact registration index rows.length step at_ slots item).val
      -- One status byte per device and not the reason: bad JSON, a bad signature, a changed
      -- identity key and a failed encapsulation look the same. The contact keeps its old state.
      -- (254 after the first step: the bundle's identity key is a new one, which is accepted.)
      o.insist (out == [255] || (out == [254] && index == 0 && step == 0)) "a device's session could not be established"
  o.log c.ch (.deviceRefresh rows.length)
  -- The new device list is stored, and only then becomes the contact's state (`commitScratch`).
  o.insist (← o.commitScratch contact (widths.map (fun w => if w.oneTime == 0 then 1 else 2)))
    "the database did not acknowledge a contact's new device list"
  o.keepAlive s

def refreshSoftG (o : RefreshOps m) (contact : Nat) (start : PublicReceive.State) :
    m (PublicReceive.State × Recovery.Refreshed) := do
  let c ← read
  let some (_, registration) := c.self | throw "no account for a device refresh"
  o.insist (0 < registration && registration < 2 ^ 32) "the export has no registration id for the account"
  let drop : m Unit := o.drop c.w
  drop
  let fetchId ← o.nextId
  let random := (← o.joint c.w).val
  let (frame, payloadAt, offsets) ← o.liftResult (PublicRequest.buildFetch fetchId (toBits (random.take 4)))
  o.recordFetch contact fetchId frame
  let handle ← o.fetch c.w contact payloadAt offsets (random.take 4) (toBytes frame)
  o.appSend (← appNowG) handle frame.length
  o.touch
  let (fetched, alive) ← o.awaitSoft 64 { PublicReceive.expect start fetchId with fetch := some fetchId, bundle := none }
  let mut s := { fetched with fetch := none, collect := false }
  if !alive then
    drop
    return (s, .lost)
  match Recovery.onFetch s.status with
  | .done => pure ()
  | .backOff =>
    drop
    return (s, .transient s.status s.retryAfter)
  | .stop result =>
    drop
    return (s, .stop result s!"the prekey fetch was answered {s.status}")
  | .refresh =>
    drop
    return (s, .stop .fault s!"the prekey fetch was answered {s.status}")
  let size := s.bundle.getD 0
  if !(2540 ≤ size && size ≤ 65536) then
    drop
    return (s, .stop .fault "server fault: the prekey response has no body of a possible size")
  let (next, alive) ← o.keepAliveSoft s
  s := next
  if !alive then
    drop
    return (s, .lost)
  -- The one thing opened about the body: which of its bytes are JSON punctuation.
  let some flags ← o.shape c.w
    | -- Strict mode, and the response's size class is not in the manifest (more devices than the
      -- deployment covers): this contact fails, the session goes on.
      drop
      return (s, .stop .fault s!"no circuit for a prekey response of {size} bytes (more devices than the deployment covers)")
  o.insist (flags.val.length == size) "invalid bundle shape"
  let layout := BundleResponse.layout? flags.val
  let widths := layout.getD []
  let rows := (BundleResponse.starts BundleResponse.firstItem widths).zip widths
  if layout.isNone || !(1 ≤ rows.length && rows.length ≤ 6) then
    drop
    return (s, .stop .fault "server fault: the prekey response is not a bundle")
  let mut changed := false
  let slots := c.config.agreed.bundleSlots
  for ((at_, item), index) in rows.zipIdx do
    for step in [0:9] do
      let (next, alive) ← o.keepAliveSoft s
      s := next
      if !alive then
        drop
        return (s, .lost)
      let out := (← o.establish c.w contact registration index rows.length step at_ slots item).val
      -- 254 (first step, first device): the bundle parsed and verified under an identity key that
      -- is not the stored one. Accepted by decision; reported.
      if out == [254] && index == 0 && step == 0 then changed := true
      else if out != [255] then
        -- One status byte and not the reason: bad JSON, a bad signature, a failed agreement or
        -- encapsulation look the same. Nothing is stored.
        drop
        return (s, .stop .fault "server fault: a device's bundle did not verify")
  -- Stored on the database nodes, then (and only then) the contact's state.
  if !(← o.commitScratch contact (widths.map (fun w => if w.oneTime == 0 then 1 else 2))) then
    return (s, .stop .retryLater "the database nodes did not acknowledge the new device list")
  o.note s!"contact {contact}: {rows.length} sessions established{if changed then " under a new identity key" else ""}"
  -- TEST hook: a pause here lets the harness change the contact's devices again before the resend.
  if let some pause := c.hooks.pauseRefresh then
    o.sleep c.ch pause
  return (s, .ok changed)

end Twins

theorem refreshContact_deployed : @Send.refreshContact = refreshContactG (m := SessionM) refreshReal := rfl
theorem refreshSoft_deployed : @Send.refreshSoft = refreshSoftG (m := SessionM) refreshReal := rfl

end TlsMpc.Node.Session.Events
