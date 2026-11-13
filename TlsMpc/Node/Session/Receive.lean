import TlsMpc.Node.Session.Store

/-!
# The receive session (REORGANIZATION_PLAN.md stage S7)

The authenticated socket (`Config.Account.share`: this party's XOR share of the account id and
password; `.stored`: the account loaded from the database nodes): answer the server's requests,
keep the connection alive while nothing arrives, and stop after the expected number of delivered
messages (`SIGNAL_LOCAL_EXPECT`).

A delivered sealed-sender envelope is opened in the engines as a NEW contact's first message
(`receiveFirst`). Public here: our prekey ids the message names, the Kyber ciphertext, and the
message text. The sender's identity stays in the engines; the contact's record is sealed and stored
under a new id, and only then is the message acknowledged. Later messages from an existing contact
are not supported yet (they are refused).

`handleEnvelope` is what every session does with a completed envelope (`Context.envelope`, bound
by `Main`; without `Context.receiving` it is dropped unopened).

Moved from the controller's `main` (stage S7), same operations and order. No I/O primitive.
-/

namespace TlsMpc.Node.Session.Receive
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Node TlsMpc.Node.Bytes TlsMpc.Node.Session
open TlsMpc.Node.Channels.Real (inBand)

/-- Kyber-1024 decapsulation runs outside the engines, with a key both parties hold (OWN): the key
goes to the tool on its standard input (`Channels.kemDecapsulate`). -/
def decapsulate (key : Secret Bytes) (ciphertext : Bytes) : SessionM (Secret Bytes) := do
  let c ← read
  let some tool := c.config.kem | throw "SIGNAL_LOCAL_KEM (decapsulation tool) is required"
  liftResult (← c.ch.kemDecapsulate tool key ([8] ++ ciphertext))

/-- A refusal of the envelope being handled, with its reason (SIGNAL_RECORD). -/
def refusedBecause (reason : String) : SessionM (Option (Nat × String)) := do
  (← read).ch.record (.envelopeRefused reason)
  return none

/-- The delivered envelope just taken into the engines, opened as a new contact's first message:
the contact's id and the text, or `none` (refused, with the reason recorded). -/
def receiveFirst (keys : Export.ReceiveKeys) : SessionM (Option (Nat × String)) := do
  let c ← read
  let w := c.w
  -- The certificate's expiry is checked against a time both controllers agree on.
  let now ← agreedNow
  let signerId := toBytes (PublicReceive.varint keys.serverId)
  let opened ← match ← Flow.Receive.openFirst w keys.identityPublic now keys.serverKey keys.serverCertificate signerId with
    | .refused status =>
      return ← refusedBecause s!"not opened as a new contact's first message (reply {status.val}: sealed-sender layer, sender certificate, PreKey shape, or no kernel for its shape)"
    | .opened ids => pure ids.val
  let find (table : List (Nat × Secret Bytes)) (id : Nat) : Option (Secret Bytes) :=
    (table.find? (·.1 == id)).map (·.2)
  let oneTime := if opened.usesOneTime then find keys.oneTime opened.oneTime else some (Secret.hide (List.replicate 32 0))
  match oneTime, find keys.signed opened.signed, find keys.kyber opened.kyber with
  | some oneTime, some signed, some kyber =>
    let secret ← decapsulate kyber opened.kyberCiphertext
    -- With the database, the contact's id is named by the message itself; until then the contact
    -- is held under a provisional id (2^128 - 1, then 2^128 - 3, 2^128 - 4, …). The worker keeps the
    -- entry of a contact refused after its session was made (evicted, not erased) and makes a
    -- session only under an id with no entry, so a provisional id is never reused within a session.
    -- Both controllers count the same messages in the same order.
    let provisional ← modifyGet fun st =>
      let n := st.contacts.provisionals
      (if n == 0 then 2 ^ 128 - 1 else 2 ^ 128 - 2 - n, { st with contacts := { st.contacts with provisionals := n + 1 } })
    let contact ← if c.dbClient.isSome then pure provisional else
      modifyGet fun st =>
        let n := st.contacts.nextContact
        (n, { st with contacts := { st.contacts with nextContact := n + 1 } })
    let text ← match ← Flow.Receive.session w contact keys.address signed oneTime secret with
      | .refused status => return ← refusedBecause s!"no session from it (reply {status.val}: keys, MAC, content or text shape)"
      | .text text => pure text.val
    if c.dbClient.isSome then
      -- The text is the application's signup token (JSON: id, signature). It names the contact's
      -- id and is what authorises the database nodes to create it. A token the nodes do not
      -- accept (forged, or already used) refuses the message.
      let refuse (contact : Nat) : SessionM (Option (Nat × String)) := do
        Flow.Contacts.evict w contact
        refusedBecause s!"the text is not a signup token the database nodes accept, or they did not store the contact ({text.length} characters)"
      -- Fixed width: base64 of the id (16 bytes) and the application's signature (64).
      db (.receivedToken text)
      let parsed ← c.ch.db .tokenId
      let named := if parsed.ok then parsed.stdout.trimAscii.toString.toNat? else none
      match named with
      | none => refuse provisional
      | some id =>
        if id ≥ accountId then return ← refuse provisional
        let token ← c.ch.dbFile (DbCall.keptTokenFile id)
        db (.keptToken id text)
        if !(← Flow.Contacts.assign w provisional id).val then
          return ← refusedBecause s!"the new contact could not take the token's id {id}"
        match ← dbDeal id token with
        | none => refuse id
        | some share =>
          Flow.Contacts.key w id share
          -- Stored (acknowledged by the nodes) before the message is acknowledged.
          if !(← dbWrite id 1 (.signupToken token id)) then return ← refuse id
          return some (id, text)
    else
    -- Stored before it is acknowledged.
    let share ← freshShare
    let fresh ← nonce
    Flow.Contacts.key w contact share
    let stored := (← Flow.Contacts.seal w contact fresh).val
    match c.storeDirectory with
    | some directory => inBand (c.ch.saveShare directory (.testStore contact) share (fresh ++ stored))
    | none => pure ()
    return some (contact, text)
  | _, _, _ =>
    -- The message names a prekey we do not hold.
    Flow.Receive.drop w
    refusedBecause s!"it names a prekey this account does not hold (one-time {opened.usesOneTime}, signed {opened.signed}, Kyber {opened.kyber})"

/-- A completed delivered envelope (type `kind`, `size` bytes of sealed content, taken into the
engines while its record was read): opened as a new contact's first message when this session
receives (`Context.receiving`), otherwise dropped. Its outcome is queued for the acknowledgement
(`State.refusals`). -/
def handleEnvelope (kind size : Nat) : SessionM Unit := do
  let c ← read
  modifyReport fun r => { r with envelopes := r.envelopes ++ [(kind, size)] }
  let outcome ← match c.receiving with
    | some keys => do
      if kind == 6 && size > 0 then
        match ← receiveFirst keys with
        | some entry =>
          modifyReport fun r => { r with received := r.received ++ [entry] }
          -- For the node daemon (SIGNAL_LOCAL_EVENTS): the id that signed up, as soon as it is stored.
          if c.config.events then
            c.ch.report (.signup entry.1)
          pure (some entry)
        | none =>
          modifyReport fun r => { r with refused := r.refused + 1 }
          pure none
      else
        -- Not a sealed-sender message: not supported, dropped.
        modifyReport fun r => { r with refused := r.refused + 1 }
        Flow.Receive.drop c.w
        refusedBecause s!"not a sealed-sender message (envelope type {kind}, {size} bytes of content)"
    | none => do
      Flow.Receive.drop c.w
      pure none
  modify fun st => { st with refusals := st.refusals ++ [outcome.isNone] }
  c.ch.record (.envelope kind size (outcome.map (·.1)))

/-- The authenticated socket's loop, on connection 0. `SIGNAL_ACK_REFUSED=0` (the same on both
nodes): a delivered message this session refused is left unacknowledged, so the server keeps it for
a later session (a fixed build can then process it). Default: acknowledged. -/
def waiting : Nat → PublicReceive.State → Nat → Nat → SessionM Nat
  | 0, _, _, _ => throw "receive budget exhausted"
  | fuel+1, s, pings, expected => do
    let c ← read
    let first := (← get).pool.first
    let keepRefused := c.config.agreed.keepRefused
    if (← get).report.delivered ≥ expected then
      -- Before leaving: one keepalive, answered. The server answers in order, so its reply shows
      -- it has read everything sent before it, the acknowledgements included; closing straight
      -- after an acknowledgement could lose it, and the message would be delivered again.
      if (← get).closing then
        if !s.pending then return pings
      else
        modify fun st => { st with closing := true }
        let random := (← Flow.Random.joint c.w).val
        let id := 2 ^ 63 + pings
        sendPublic (toBytes (← liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
        modifyReport fun r => { r with keepalives := r.keepalives + 1 }
        return ← waiting fuel (PublicReceive.expect s id) (pings + 1) expected
    -- libsignal profile: 31 seconds without a record, then a WebSocket ping (libsignal-net
    -- `WS_KEEP_ALIVE_INTERVAL`; its payload is a one-byte ping counter from 1). The pong is a
    -- control frame the parser skips.
    if c.official && s.upgraded && !(← Flow.Server.awaitRecord c.w first.slot 124 250) then
      let random := (← Flow.Random.joint c.w).val
      sendPublic (toBytes (PublicReceive.ping ((pings + 1) % 256) (toBits (random.take 4))))
      modifyReport fun r => { r with keepalives := r.keepalives + 1 }
      waiting fuel s (pings + 1) expected
    else
    -- 25 seconds of agreed silence, then a keepalive.
    if !c.official && s.upgraded && !(← Flow.Server.awaitRecord c.w first.slot 100 250) then
      insist (!s.pending) "keepalive was not answered"
      let random := (← Flow.Random.joint c.w).val
      let id := 2 ^ 63 + pings
      sendPublic (toBytes (← liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
      modifyReport fun r => { r with keepalives := r.keepalives + 1 }
      waiting fuel (PublicReceive.expect s id) (pings + 1) expected
    else
    match ← TlsApplication.receive first.session with
    | .application handle =>
      let (s, _) ← record handle.id s
      let (s, frames) ← liftResult (PublicReceive.replies s (← controlMasks c.w s))
      for (kind, frame) in frames do
        sendPublic (toBytes frame)
        insist (kind != 8) "WebSocket peer closed before completion"
      for request in s.requests do
        let random := (← Flow.Random.joint c.w).val
        let (frame, message) ← liftResult (PublicReceive.reply request (toBits (random.take 4)))
        -- A delivered message was dealt with (stored or refused) while its record was read;
        -- acknowledging it lets the server remove it from the queue. Whether this message's
        -- envelope was refused (`SIGNAL_ACK_REFUSED`). One left on the server does not count
        -- towards the messages expected: it would be delivered first again on every connection.
        let wasRefused ← if message then do
            let queue := (← get).refusals
            modify fun st => { st with refusals := queue.tail }
            pure (queue.headD false)
          else pure false
        if message && !(wasRefused && keepRefused) then
          modifyReport fun r => { r with delivered := r.delivered + 1 }
        let acknowledge := (!message || c.receiving.isSome) && !(wasRefused && keepRefused)
        c.ch.record (.serverRequest message wasRefused acknowledge)
        if acknowledge then sendPublic (toBytes frame)
      waiting fuel { s with requests := [] } pings expected
    | .control => waiting fuel s pings expected
    | .closed =>
      c.ch.record .closedWhileWaiting
      throw "TLS closed while waiting for messages"

/-- **The receive session**: wait for `SIGNAL_LOCAL_EXPECT` delivered messages after the upgrade
(`accept`: the expected accept value), then (libsignal profile) a WebSocket Close after the closing
keepalive's answer (`closeWebSocket`), then abort the TLS session. Returns the keepalives sent. -/
def run (accept : Bytes) : SessionM Nat := do
  let pings ← waiting 4096 (PublicReceive.start (toBits accept)) 0 (← read).config.expect
  closeWebSocket
  TlsApplication.abort (← get).pool.first.session
  return pings

end TlsMpc.Node.Session.Receive
