import TlsMpc.Signal.PrivateTextNotification
import TlsMpc.Signal.BundleResponse
import TlsMpc.Node.Policy.Request
import TlsMpc.Node.Session.Pool
import TlsMpc.Node.Session.Store

/-!
# The send session (REORGANIZATION_PLAN.md stage S7)

The application's request: `notify(ids, message)`. Ids and text are public to both parties; it
expands to one send per contact (`notify`, `inputsOf`). One send: the engines produce and open the
sealed-sender envelope; the request is assembled here; the engines insert the contact's fields and
seal the record. With the database the contact's advanced state is stored (and acknowledged by the
nodes) BEFORE its message leaves (ORD-1: `storeAdvanced`, `storeSoft`).

Two loops over the sends:
- `loop` (no database nodes, or `SIGNAL_RECOVERY=0`): a send answered 409/410 (the contact's
  devices changed) is handled by one device refresh and one resend (`refreshContact`); any other
  failure ends the session;
- `deliverJob` (the recovery path, with the database nodes): every input ends in a per-id result
  and the session carries on (`sendSoft`, `refreshSoft`, reconnects, retries with back-off, the
  notify's journal); the per-id results are agreed by digest (T11). Run once (`deliver`) or once
  per job of the long-lived session (`Serve.serve`).

Moved from the controller's `main` (stage S7), same operations and order. No I/O primitive.

The sends, the refreshes and both loops are monad-generic definitions (`sendSoftG`, …,
`deliverJobG`, effects the fields of `SendOps`, `RefreshOps`, `LoopOps`, `DeliverOps`); the
deployed functions are those definitions at `SessionM` and the deployed records (`sendReal`, …):
`abbrev f := fG realOps` (2026-11-12, PROOF_GAPS C3; `Session/Events.lean`, header). The only
call sites of `Flow.Send.request` / `requestDevices` are in `sendReal` (`lint_node.py`,
`ordering-sites`).
-/

namespace TlsMpc.Node.Session.Send
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal TlsMpc.Node TlsMpc.Node.Bytes TlsMpc.Node.Session

/-- `notify(ids, message)`: one built message per contact. The text is 1..256 bytes of UTF-8. What
goes to the engines is the built message of its size class c in 1..4: a validity byte, a kind byte,
80c bytes of padded content (Content, 0x80, zeros: Signal's padding in 80-byte blocks) and the
8-byte timestamp. The envelope's size depends on c alone, so its observer learns c: the Content's
length rounded up to 80 bytes (with today's timestamps, text of 1..68, 69..146, 147..226 or
227..256 bytes), not the exact length. -/
def notify (ids : List Nat) (message : String) (timestamp : Nat) : SessionM (List (Nat × Bytes)) := do
  let official := (← read).official
  let body := message.toUTF8.data.toList
  insist (0 < body.length && body.length ≤ 256) "notify message must be 1..256 bytes"
  insist (ids.all (· < 2 ^ 128)) "contact ids are u128"
  -- The text is public, so the message content (protobuf, padding) is built here with the same
  -- definition the private path compiles to a circuit (`PrivateTextNotification.buildPublic`: the
  -- smallest of the four size classes that holds the content; texts of at most 48 bytes get
  -- exactly what `build` gave them).
  ids.zipIdx.mapM (fun (contact, index) => do
    -- (libsignal profile: the official padding, 80c − 1 bytes, `buildPublicOfficial`.)
    let (classes, built) := ((if official then PrivateTextNotification.buildPublicOfficial else PrivateTextNotification.buildPublic)
      4 (toBits body) (toBits (uint 8 (timestamp + index)))).getD (0, [])
    insist (1 ≤ classes && classes ≤ 4 && built.length == (if official then 9 else 10) + 80 * classes && built.head? == some 255) "message text rejected"
    if official then modify fun st => { st with bodies := (toBytes built, body) :: st.bodies }
    pure (contact, toBytes built))

/-- The session's sends, from the agreed time `base` (`Start.Started.base`): through the daemon,
the application's one message to the requested ids the database holds (`contacts`); otherwise
(TEST) two broadcasts to every contact, and further ones on request (SIGNAL_LOCAL_BROADCASTS, for
measuring the cost per message). Without the export (a ceremony session): none. -/
def inputsOf (contacts : List Nat) (base : Option Nat) : SessionM (List (Nat × Bytes)) := do
  let c ← read
  match base with
  | none => pure []
  | some base =>
    if let some file := c.config.notifyFile then
      let text ← c.ch.readMessage file
      notify contacts text base
    else
    let count := c.hooks.broadcasts
    let more ← ((List.range (count - 2)).mapM (fun k => notify contacts
      -- the third broadcast is 200 bytes long (a larger size class)
      (if k == 0 then "MPC broadcast 3 " ++ String.ofList (List.replicate 184 'x') else s!"MPC broadcast {k + 3}") (base + 1000 * (k + 2))))
    pure ((← notify contacts "MPC broadcast one" base) ++ (← notify contacts "MPC broadcast two ☕" (base + 1000)) ++ more.flatten)

/-- libsignal profile: a message's timestamp is the agreed clock when it is first sent (an official
client stamps each message when it is sent; a broadcast built ahead with base + index drifts ever
further behind the server's clock), strictly increasing within the session, and kept when the same
message is sent again (a resend after a device refresh). The built content is rebuilt from its text
with the new timestamp: the same size class, since the timestamp's varint keeps its width. -/
def restamp (send : Nat × Bytes) : SessionM (Nat × Bytes) := do
  let c ← read
  if !c.official then return send
  if c.hooks.timestamp.isSome then return send
  if (← get).stamped.contains send.2 then return send
  let some (_, body) := (← get).bodies.find? (·.1 == send.2) | return send
  -- The contact's per-session preparation (its first send's curve work: tens of seconds without
  -- TLS_WORKER_HINTED) runs BEFORE the stamp, so that the stamp is taken just before the message
  -- is sealed and sent, as an official client's is. Once prepared, this costs one exchange; a
  -- contact with a device list is prepared by its own send.
  if (← kindsOf send.1) == [0] then
    let _ ← Flow.Curve.prepareContacts c.w [send.1]
  let now := max (← agreedNow) ((← get).lastStamp + 1)
  modify fun st => { st with lastStamp := now }
  let some (_, built) := PrivateTextNotification.buildPublicOfficial 4 (toBits body) (toBits (uint 8 now)) | throw "message text rejected"
  insist (built.length == send.2.length) "a new timestamp changed the message's size class"
  modify fun st => { st with stamped := toBytes built :: st.stamped }
  pure (send.1, toBytes built)

/-- A private request as far as the controllers know it (SIGNAL_RECORD): the frame with its private
slots (recipient, access key, device and registration ids) still zero. The worker fills them in the
engines and seals the record. -/
def recordSend (contact id timestamp : Nat) (frame : List (BitVec 8)) : SessionM Unit := do
  (← read).ch.record (.sentPrivate (← current) contact id timestamp (toBytes frame))

def recordFetch (contact id : Nat) (frame : List (BitVec 8)) : SessionM Unit := do
  (← read).ch.record (.sentPrekeyFetch (← current) contact id (toBytes frame))

/-! ### One send: operations and monad-generic definitions

`sendDevices`, `sendMessage`, `sendSoft` are defined once over any monad with the session's classes,
their effects being the fields of `SendOps` (the store's are `StoreOps`); the deployed functions are
these definitions at `SessionM` and `sendReal`. ORD-1 is proved about them
(`Session/SendProofs.lean`). -/

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

/-- The deployed operations of one send. -/
def sendReal : SendOps SessionM where
  store := storeReal
  liftResult x := liftResult x
  restamp := restamp
  sealOne w c b := Flow.Send.«seal» w c b
  sealDevices w c a b n := Flow.Send.sealDevices w c a b n
  joint w := Flow.Random.joint w
  recordSend := recordSend
  request w c o m f := Flow.Send.request w c o m f
  requestDevices w c p o n m f := Flow.Send.requestDevices w c p o n m f
  appSend s h n := TlsApplication.send s h n

section Generic
variable {m : Type → Type} [Monad m] [MonadExceptOf String m] [MonadStateOf State m] [MonadReaderOf Context m]

/-- One send to a contact with a device list (MULTI_DEVICE.md, section 5): the engines produce one
envelope per device, all for the same built text; the state is stored before anything leaves, as
for one device; then one request carries all of them. -/
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

/-- One send (a failure is the session's): sealed, the state stored, the request sent. -/
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

/-- `sendMessage` with the contact's failures as outcomes. `none`: the request left. Otherwise
nothing was sent: the result, the reason, and whether to stop sending to this contact. -/
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

end Generic

abbrev sendDevices (send : Nat × Bytes) (id : Nat) : SessionM Unit := sendDevicesG sendReal send id
abbrev sendMessage (send : Nat × Bytes) (id : Nat) : SessionM Unit := sendMessageG sendReal send id
abbrev sendSoft (send : Nat × Bytes) (id : Nat) : SessionM (Option (Recovery.Result × String × Bool)) :=
  sendSoftG sendReal send id

/-! ### A device refresh: operations and monad-generic definitions (ORD-2 inside it:
`Session/RefreshProofs.lean`, `LoopProofs.lean`) -/

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

/-- The deployed operations of a refresh. -/
def refreshReal : RefreshOps SessionM where
  insist b e := insist b e
  liftResult x := liftResult x
  nextId := nextId
  joint w := Flow.Random.joint w
  recordFetch := recordFetch
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

section Generic
variable {m : Type → Type} [Monad m] [MonadExceptOf String m] [MonadStateOf State m] [MonadReaderOf Context m]

/-- A contact whose device list changed (MULTI_DEVICE.md, sections 3 and 5). The server answers a
send 409 (devices missing or extra) or 410 (stale registration ids). Its body lists device ids and
is not read. Instead every session of the contact is replaced: fetch all its devices' prekey
bundles, establish a session per device in the engines, store the new device list, send the message
again. -/
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

/-- `refreshContact` with every failure as an outcome (`Recovery.Refreshed`). Nothing of the
contact changes, in the engines or on the database nodes, unless it returns `ok`. -/
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

end Generic

abbrev refreshContact (contact : Nat) (start : PublicReceive.State) : SessionM PublicReceive.State :=
  refreshContactG refreshReal contact start
abbrev refreshSoft (contact : Nat) (start : PublicReceive.State) : SessionM (PublicReceive.State × Recovery.Refreshed) :=
  refreshSoftG refreshReal contact start

/-- Before a contact's first send of the session: its per-session curve work (the table its
messages' key agreements are summed from) together with that of the contacts that follow it, in one
worker call whose field rounds they share: the latency of a few dozen rounds once per batch instead
of per contact. Only with the workers' constant-depth programs (TLS_WORKER_HINTED=1); without them
each contact is prepared by its own first send. An optimisation, never a decision: a contact the
call does not prepare (status other than 255: its key is refused, or it is not loaded) is prepared
or refused by its own send, with that path's per-contact outcome. The contact's state is still
stored before each of its sends; nothing here changes it. SIGNAL_PREPARE_BATCH: contacts per call
(default 32, at most 64; 0: never). -/
def ensurePrepared (contact : Nat) (upcoming : List Nat) : SessionM Unit := do
  let c ← read
  if !c.config.agreed.hinted then return
  let size := c.config.agreed.prepareBatch
  let done := (← get).contacts.prepared
  if size == 0 || done.contains contact then return
  let batch := ((contact :: upcoming).eraseDups.filter (fun x => !done.contains x)).take size
  let statuses ← Flow.Curve.prepareContacts c.w batch
  insist (statuses.val.length == batch.length) "invalid contacts-prepare reply"
  modifyContacts fun k => { k with prepared := k.prepared ++ batch }

/-! ### The send loop without recovery: operations and monad-generic definition (ORD-1, ORD-2 over
every run: `Session/LoopProofs.lean`) -/

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

/-- The deployed operations of `loop`. -/
def loopReal : LoopOps SessionM where
  insist b e := insist b e
  liftResult x := liftResult x
  receive s := TlsApplication.receive s
  record := record
  controlMasks w s := controlMasks w s
  sendPublic := sendPublic
  joint w := Flow.Random.joint w
  refreshContact := refreshContact
  nextId := nextId
  sendMessage := sendMessage
  awaitReply := awaitReply
  keyUpdate s b := TlsApplication.keyUpdate s b
  reloadContacts := reloadContacts
  ensurePrepared := ensurePrepared
  toCircuit := toCircuit

/-- The send loop without recovery (`known`: the contacts loaded, reloaded after two sends;
`recipients`: the session's contacts, for `Circuits.assign`). Against a Signal server a send may be
answered 409/410 (the contact's devices changed): such a response is completed and handled here
instead of ending the session. Returns the responses completed. -/
def loopG {m : Type → Type} [Monad m] [MonadExceptOf String m] [MonadStateOf State m] [MonadReaderOf Context m]
    (o : LoopOps m) (known : List (Nat × Secret Bytes × Nat)) (recipients : List Nat) :
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

abbrev loop (known : List (Nat × Secret Bytes × Nat)) (recipients : List Nat) :
    Nat → PublicReceive.State → List (Nat × Bytes) → Nat → SessionM Nat :=
  loopG loopReal known recipients

/-! ### The recovery path's loop: operations and monad-generic definition

`deliverJob` is defined once over any monad (`deliverJobG`, its effects the fields of
`DeliverOps`); the deployed `deliverJob` is that definition at `SessionM` and `deliverReal`. ORD-1,
ORD-2 over every run and T11 are proved about it (`Session/DeliverProofs.lean`, `LoopProofs.lean`). -/

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

/-- The deployed operations of `deliverJob`. -/
def deliverReal : DeliverOps SessionM where
  insist b e := insist b e
  peer := peer
  note := note
  readJournal ch path named := ch.readJournal path named
  sleep ch ms := ch.sleep ms
  agreedClock := agreedClock
  ensurePrepared := ensurePrepared
  sendSoft := sendSoft
  awaitSoft := awaitSoft
  record ch e := ch.record e
  reconnect := reconnect
  saveState := saveState
  refreshSoft := refreshSoft
  keyUpdate s b := TlsApplication.keyUpdate s b
  journal ch path line := ch.journal path line

section Generic
variable {m : Type → Type} [Monad m] [MonadExceptOf String m] [MonadStateOf State m] [MonadReaderOf Context m]

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

/-- **One notify's sends on the recovery path** (`inputs`, to the contacts `recipients`) on the
open connections (`Pool.openAll`; `first`: connection 0's parser state). Every input ends in a
per-id result; the session still ends on what is the session's own failure: an engine or worker
rejection, a disagreement between the parties, a TLS record that does not authenticate, a
handshake that fails.

What makes a resend safe: a contact's state is stored on the database nodes before its message
leaves (`storeSoft`), so sending the same text again always uses the next keys. A resend can
therefore duplicate a message, never reuse a key.

What an earlier session for the SAME notify settled (`notifyId` names the notify, `journal` is this
party's journal): an entry counts only when both parties' journals have it: a party that lost its
journal, or lies, can cause a duplicate, never a message left out. Entries are public values
(message number, id, result). Returns the inputs delivered; the per-id results (agreed by digest)
are in `Report.results`. -/
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

end Generic

abbrev deliverJob (inputs : List (Nat × Bytes)) (recipients : List Nat) (notifyId journal : Option String)
    (first : PublicReceive.State) : SessionM Nat :=
  deliverJobG deliverReal inputs recipients notifyId journal first

/-- **The one-notify send session on the recovery path**: open every connection, deliver. -/
def deliver (accept : Bytes) (inputs : List (Nat × Bytes)) : SessionM Nat := do
  let c ← read
  let first ← openAll accept
  deliverJob inputs (inputs.map (·.1)) c.config.notifyId c.config.notifyJournal first

/-- **The send session without recovery**: every contact loaded, connections 1..N-1 with several
Tor circuits (nothing otherwise), then `loop`. -/
def sendAll (accept : Bytes) (known : List (Nat × Secret Bytes × Nat)) (inputs : List (Nat × Bytes)) : SessionM Nat := do
  let c ← read
  requireLoaded
  openCircuits   -- connections 1..N-1 with several Tor circuits; nothing otherwise
  loop known (inputs.map (·.1)) (256 + 16 * inputs.length)
    { PublicReceive.start (toBits accept) with lenient := c.exportPath.isSome } inputs 0

end TlsMpc.Node.Session.Send
