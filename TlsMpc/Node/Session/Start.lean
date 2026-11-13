import TlsMpc.Node.Session.Store
import TlsMpc.Node.Session.Ceremony

/-!
# How every two-party session starts (REORGANIZATION_PLAN.md stage S7)

1. `connect` (before the session's state exists): the settings agreement (SECURITY_MAP D.11), the
   server's TCP connection (through the Tor proxy with circuits), the TLS handshake on the engines,
   connection 0's application session.
2. `run`: the socket's upgrade and what the session holds before its first request:
   - a ceremony session: `Ceremony.upgrade`;
   - otherwise (SIGNAL_LOCAL_EXPORT, scaffolding): `fromExport`: the account (from the database
     nodes, or TEST: from the export), the contacts (from the database nodes under the
     application's signed request, from the TEST store, or TEST: admitted from the export), and the
     upgrade: the UNAUTHENTICATED socket, whose upgrade request is public (sealed-sender sends must
     not go on an authenticated socket), or, receiving, the authenticated socket with the shared
     credentials;
   - then the export's receive keys and own address, and the agreed time a broadcast is stamped
     with (one clock agreement whenever there is an export, whatever the session's kind).

The fixture session (no export: contacts 1 and 2 admitted by the worker, in-memory texts) was
removed in stage S7.

Moved from the controller's `main` (stage S7), same operations and order. No I/O primitive.
-/

namespace TlsMpc.Node.Session.Start
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Node TlsMpc.Node.Bytes TlsMpc.Node.Session
open TlsMpc.Node.Channels.Real (inBand)

/-- What `run` leaves for the session's kind.
- `accept`: the expected accept value of the upgrade (its 101 is read by the kind);
- `known`: per contact loaded: id, this party's key share, the version of the stored state it was
  loaded from (0: none);
- `receiving`, `self`: the export's receive keys (the authenticated socket) and our own address and
  registration id;
- `base`: the agreed time the session's broadcast is stamped with (with an export). -/
structure Started where
  accept : Bytes
  known : List (Nat × Secret Bytes × Nat)
  receiving : Option Export.ReceiveKeys
  self : Option (Bytes × Nat)
  base : Option Nat

/-- **The settings agreement, the connection and the handshake** (connection 0). The settings
agreement comes before anything else: each controller sends the other the SHA-256 of the settings
that must be the same on both nodes (`Config.agreedText`), and the session ends on a difference. -/
def connect (c : Context) : M Connection := do
  let settings := Config.digest c.config
  let theirSettings ← match ← c.ch.exchange c.w.link (.settingsDigest settings) with
    | .settingsDigest digest => pure digest
    | _ => throw "invalid settings digest reply"
  insist (theirSettings == settings)
    s!"the two nodes' settings differ (SECURITY_MAP D.11); this node's: {Config.agreedText c.config}"
  liftM (c.ch.record (.connect c.endpoint c.port c.tlsConfig.hostname c.authenticated (c.config.socks.map (·.1)) c.circuits c.official))
  Flow.Server.connect c.w c.endpoint (← liftM (natural c.port)) (c.proxyFor (if c.authenticated then none else some 0))
  liftM (c.ch.record .connected)
  let handshake ← Flow.Tls.handshake c.w c.tlsConfig
  liftM (c.ch.record (.handshake handshake.serverCertificateVerified handshake.serverFinishedVerified))
  insist (handshake.serverCertificateVerified && handshake.serverFinishedVerified) "handshake not accepted after retirement"
  -- The worker's selected connection (kept by `w`; `w.on i` selects connection i first) and the
  -- one this controller is using (`Pool.current`). Connection 0 never selects unless there are more.
  let kept ← liftM (IO.mkRef (none : Option Bytes) : IO (IO.Ref (Option Bytes)))
  let session ← liftM (Flow.Tls.application (c.w.on 0) handshake kept)
  pure { session, slot := kept }

/-- A session with the export (SIGNAL_LOCAL_EXPORT): the account, the contacts and the upgrade.
Returns the expected accept value and the contacts loaded. -/
def fromExport (path : String) : SessionM (Bytes × List (Nat × Secret Bytes × Nat)) := do
  let c ← read
  let w := c.w
  let app := (← get).pool.first.session
  let (certificate, identity, records) ← liftResult (← c.ch.readExport path)
  let accountStored ← if c.dbClient.isSome then do
      let (accountRead, accountShares) ← dbRead .account "account"
      match dbShare accountShares accountId, dbBlob accountRead accountId with
      | some share, some (_, blob) =>
        Flow.Account.key w share
        Flow.Account.load w (← liftResult (fromHex blob))
        pure true
      | _, _ => pure false
    else pure false
  -- TEST: until the account's row exists it is admitted from the export.
  unless accountStored do
    Flow.Account.admitTest w identity certificate
  -- Per wanted contact: its TEST record from the export, if it has one.
  let records : List (Nat × Option (Secret Bytes)) := records.map fun (contact, record) => (contact, some record)
  -- Contacts that exist only in the store (received in an earlier session).
  let extra := c.hooks.extraContacts.map (fun contact => (contact, (none : Option (Secret Bytes))))
  -- (The long-lived session starts with none: each job loads its own, `Serve.loadJob`.)
  let wanted := if c.authenticated || c.config.serveDir.isSome then [] else records ++ extra
  -- Through the daemon: exactly the ids of the application's signed request, whose message hash
  -- must be the text's. (TEST: an id of the export is still created from it.)
  let wanted ← match c.config.notifyFile, c.authenticated with
    | some file, false => do
      let text ← c.ch.readMessage file
      let request ← liftResult (← c.ch.readRequest (← dbEnv "SIGNAL_DB_REQUEST"))
      let ids := request.ids
      insist (!ids.isEmpty) "the notify request lists no ids"
      let signedFor ← liftResult (fromHex request.messageHash)
      insist (signedFor == TlsWire.hash text.toUTF8.data.toList) "the message is not the one the notify request was signed for"
      pure (ids.map (fun id => (id, (records.find? (·.1 == id)).bind (·.2))))
    | _, _ => pure wanted
  let known ← if c.dbClient.isSome && !wanted.isEmpty then do
    -- From the database nodes, under the application's signed request for these ids.
    let (readJson, sharesJson) ← dbRead (.request (← dbEnv "SIGNAL_DB_REQUEST")) "contacts"
    -- A contact created moments ago is not served until the nodes' next epoch.
    let waiting := readJson.notYetReadable
    -- Through the daemon, such an id, and one the nodes do not hold at all (unless the TEST export
    -- can create it), is that id's result and not the session's end. Both parties must have found
    -- the same ones.
    let wanted ← if c.config.notifyFile.isNone then pure wanted else do
      let gone := wanted.filterMap (fun (contact, record) =>
        if waiting.contains (toString contact) then some (contact, true)
        else if record.isNone && ((dbShare sharesJson contact).isNone || (dbBlob readJson contact).isNone) then some (contact, false)
        else none)
      insist (← absentAgreed gone) "the two parties' database reads differ"
      modifyReport fun r => { r with absent := gone }
      pure (wanted.filter (fun (contact, _) => !gone.any (·.1 == contact)))
    insist (wanted.all (fun (contact, _) => !waiting.contains (toString contact))) "a contact is not readable until the database's next epoch"
    wanted.mapM (fun (contact, record) => do
      let share := dbShare sharesJson contact
      let blob := dbBlob readJson contact
      match share, blob with
      | some share, some (version, blob) =>
        Flow.Contacts.key w contact share
        -- Both parties must have been given the same blob: the request is agreed.
        openState contact (← liftResult (fromHex blob))
        pure (contact, share, version)
      | _, _ =>
        -- TEST: a contact of the export that the database does not have yet is created there,
        -- under a signup token the harness supplies (SIGNAL_DB_TOKENS/<id>.json).
        let some record := record | throw "contact is not in the database"
        let some share ← dbDeal contact s!"{← dbEnv "SIGNAL_DB_TOKENS"}/{contact}.json" | throw "dealing a contact key failed"
        Flow.Contacts.admitTest w contact record
        Flow.Contacts.key w contact share
        pure (contact, share, 0))
  else wanted.mapM (fun (contact, record) => do
    let saved ← match c.storeDirectory with
      | none => pure none
      | some directory => inBand (c.ch.loadStored directory contact)
    match saved with
    | some (share, rest) =>
      -- A stored contact: key from the shares, then the state from its ciphertext.
      insist (share.length == 32 && rest.length > 24) "stored contact shape"
      Flow.Contacts.key w contact share
      openState contact rest
      pure (contact, share, number (rest.take 8))
    | none =>
      let some record := record | throw "contact has no stored state"
      let share ← freshShare
      Flow.Contacts.admitTest w contact record
      Flow.Contacts.key w contact share
      pure (contact, share, 0))
  if c.authenticated then
    match c.config.account with
    | .share share =>
      -- The password is shared: neither party can open this socket alone.
      Flow.Account.credentials w share
      if c.dbClient.isSome && !accountStored then
        -- TEST: the first session that has the account's key and credentials creates its row on
        -- the database nodes (key dealt under a token for the reserved id).
        let some keyShare ← dbDeal accountId s!"{← dbEnv "SIGNAL_DB_TOKENS"}/{accountId}.json" | throw "dealing the account key failed"
        Flow.Account.key w keyShare
        let fresh ← nonce
        let stored := (← Flow.Account.seal w fresh).val
        insist (← dbSubmit "account" .account 1 (fresh ++ stored)) "the database did not acknowledge the account's state"
    | _ => insist accountStored "no credentials: the account is not stored and none were given"
    let (request, size, accept) ← Flow.Upgrade.authenticated w 1
    TlsApplication.send app request size
    pure (accept.val, known)
  else
    let upgrade ← Flow.Upgrade.anonymous w
    sendPublic (toBytes (c.anonymousUpgrade (toBits upgrade.val.1)))
    pure (upgrade.val.2, known)

/-- **The start of every session** after `connect`: see the top of this file. -/
def run : SessionM Started := do
  let c ← read
  let (accept, known) ← match c.config.ceremony, c.exportPath with
    | some stage, _ => Ceremony.upgrade stage
    | none, none => throw "SIGNAL_LOCAL_EXPORT is required (the fixture session was removed in stage S7)"
    | none, some path => fromExport path
  -- Receiving (authenticated socket with an export): a delivered sealed-sender envelope is opened
  -- in the engines as a NEW contact's first message (`Receive.receiveFirst`).
  let receiving ← match c.exportPath, c.authenticated with
    | some path, true => pure (some (← liftResult (← c.ch.readReceive path)))
    | _, _ => pure none
  modifyContacts fun k => { k with versions := known.map (fun (contact, _, version) => (contact, version)) }
  -- Our own address and registration id, for sessions the client starts (a contact's new device).
  let self ← match c.exportPath with
    | some path => pure (some (← liftResult (← c.ch.readSelf path)))
    | none => pure none
  -- The broadcast's timestamp is public and must be the same for both controllers: agreed.
  let base ← match c.exportPath with
    | some _ => pure (some (← agreedNow))
    | none => pure none
  pure { accept, known, receiving, self, base }

end TlsMpc.Node.Session.Start
