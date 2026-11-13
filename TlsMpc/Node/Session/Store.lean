import TlsMpc.Node.Session.Common

/-!
# Contacts at rest: the database nodes and the TEST store (REORGANIZATION_PLAN.md stage S7)

The database nodes (SIGNAL_DB_CLIENT: the `handoff_client` of secret-shared-db, with
SIGNAL_DB_NETWORK, SIGNAL_DB_KEY and a scratch directory SIGNAL_DB_WORK). Each party runs the client
itself: its key shares never leave it. Between the parties go only the parity shares of a read
(whose sums must be zero) and small status bytes. A contact's state is one blob,
`nonce ‖ check ‖ ciphertext (‖ kinds ‖ count)`, which the nodes accept only when both parties
submit the same bytes as the next version.

- reads: `dbRead` (under the application's request, or of the account's own row), `dbShare`,
  `dbBlob`, `absentAgreed`;
- a contact's state in the engines: `openState`, `sealState`, `kindsOf`/`setKinds`,
  `requireLoaded`, `forget`;
- writes: `dbSubmit` (a failure is the session's), `dbSubmitSoft` (a failure is the contact's),
  `dbWrite`, `storeAdvanced`, `storeSoft`, `commitScratch` (ORD-2: a refresh's scratch becomes the
  contact's state only after the nodes acknowledged it), `dbDeal` (a new contact's key);
- the TEST store and the at-rest round trip: `reloadContacts`, `writeBack`.

Not a module of the plan's list (which names Common, Pool, Send, Serve, Receive, Ceremony,
Delete): these are shared by the send, serve and receive kinds and by `Start`. Moved from the
controller's `main` (stage S7), same operations and order. No I/O primitive.

The functions on the ORD-1 / ORD-2 paths are monad-generic definitions (`kindsOfG` …
`commitScratchG`, effects the fields of `StoreOps`); the deployed ones are those definitions at
`SessionM` and `storeReal` (2026-11-12, PROOF_GAPS C3; `Session/Events.lean`, header).
-/

namespace TlsMpc.Node.Session
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Node TlsMpc.Node.Bytes
open TlsMpc.Node.Channels.Real (inBand)

/-- A database setting (`SIGNAL_DB_*`), required with SIGNAL_DB_CLIENT. -/
def dbEnv (name : String) : SessionM String := do
  liftResult (Channels.Real.dbSetting (← read).config " with SIGNAL_DB_CLIENT" name)

/-- The application's signed request that authorises reads and write-backs: SIGNAL_DB_REQUEST,
or in the long-lived session (`serve`) the request of the job being served. -/
def requestFile : SessionM String := do
  match (← get).jobRequest with
  | some path => pure path
  | none => dbEnv "SIGNAL_DB_REQUEST"

/-- A command or input file of the database client (`DbCall`); a failed command's standard error
is logged. -/
def dbTry (call : DbCall) : SessionM Bool := do
  let c ← read
  let out ← c.ch.db call
  if !out.ok then c.ch.log (.dbClientFailed call.command out.stderr)
  pure out.ok

/-! ### The store's operations and its monad-generic definitions

The functions on the ORD-1 / ORD-2 paths (`kindsOf` … `commitScratch`) are defined once over any
monad with the session's classes, their effects being the fields of `StoreOps`; the deployed
function is that definition at `SessionM` and `storeReal` (`abbrev f := fG storeReal`). The
ordering theorems (`Session/StoreProofs.lean`) are about these definitions. -/

/-- Every effect `Store`'s ORD-1 / ORD-2 functions perform, besides `State` and `Context`. -/
structure StoreOps (m : Type → Type) where
  insist : Bool → String → m Unit
  dbTry : DbCall → m Bool
  peer : PeerMsg → m PeerMsg
  writeAcknowledged : Channels → String → m Bool
  nonce : m Bytes
  contactSeal : Flow.Worker → Nat → Bytes → m (Opened .sealedBlob Bytes)
  requestFile : m String
  scratchSeal : Flow.Worker → Nat → Bytes → m (Opened .sealedBlob Bytes)
  scratchCommit : Flow.Worker → Nat → m Unit
  drop : Flow.Worker → m Unit

/-- The deployed operations. -/
def storeReal : StoreOps SessionM where
  insist b e := insist b e
  dbTry := dbTry
  peer := peer
  writeAcknowledged ch n := ch.writeAcknowledged n
  nonce := nonce
  contactSeal w c f := Flow.Contacts.seal w c f
  requestFile := requestFile
  scratchSeal w c f := Flow.Refresh.scratchSeal w c f
  scratchCommit w c := Flow.Refresh.scratchCommit w c
  drop w := Flow.Refresh.drop w

section Generic
variable {m : Type → Type} [Monad m] [MonadExceptOf String m] [MonadStateOf State m] [MonadReaderOf Context m]

/-- A contact with a device list (MULTI_DEVICE.md, section 4): the kinds of its devices' entries,
in order (0: a 319-byte record; 1, 2: record and pending, 1935 bytes). They are public (every
send's length shows them) and are stored in the clear after the ciphertext, as `kinds ‖ count`. A
contact that is one established record has kinds [0] and is stored as before, without them. -/
def kindsOfG (contact : Nat) : m (List Nat) := do
  pure ((((← get).contacts.kinds.find? (·.1 == contact)).map (·.2)).getD [0])

def setKindsG (contact : Nat) (kinds : List Nat) : m Unit :=
  modifyContactsG fun k => { k with kinds := k.kinds.filter (·.1 != contact) ++ [(contact, kinds)] }

/-- The version of a contact's state this session holds (0: none). -/
def versionOfG (contact : Nat) : m Nat := do
  pure (((← get).contacts.versions.find? (·.1 == contact)).map (·.2) |>.getD 0)

def bumpVersionG (contact : Nat) : m Unit := do
  let version ← versionOfG contact
  modifyContactsG fun k => { k with versions := k.versions.map (fun (c, v) => if c == contact then (c, version + 1) else (c, v)) }

/-- Seal a contact's current state under a new nonce: `check ‖ ciphertext (‖ kinds ‖ count)`. -/
def sealStateG (o : StoreOps m) (contact : Nat) (fresh : Bytes) : m Bytes := do
  let stored := (← o.contactSeal (← read).w contact fresh).val
  let kinds ← kindsOfG contact
  pure (if kinds == [0] then stored else stored ++ kinds.map UInt8.ofNat ++ [UInt8.ofNat kinds.length])

def dbG (o : StoreOps m) (call : DbCall) : m Unit := do
  o.insist (← o.dbTry call) s!"database client failed: {call.command}"

/-- Store a contact's sealed state as blob `version`. Counts once all but one node committed it. -/
def dbSubmitG (o : StoreOps m) (name : String) (authority : WriteAuthority) (version : Nat) (blob : Bytes) : m Bool := do
  dbG o (.blob name blob)
  dbG o (.writeBlob name authority version)
  let _ ← o.peer .submitted   -- both parties have submitted
  dbG o (.writeBlob name authority version)   -- repeating it reports the commit to whichever party was first
  o.writeAcknowledged (← read).ch name

def dbWriteG (o : StoreOps m) (contact version : Nat) (authority : WriteAuthority) : m Bool := do
  let fresh ← o.nonce
  let stored ← sealStateG o contact fresh
  o.insist (stored.length > 16) "invalid stored contact state"
  dbSubmitG o (toString contact) authority version (fresh ++ stored)

/-- With the database: the contact's advanced state is stored (and acknowledged by the nodes)
BEFORE its message leaves. If the session dies afterwards the stored state is never behind what was
sent, so no message key or counter can be used twice; at worst a message that was stored for but
never sent leaves a gap in the counter. -/
def storeAdvancedG (o : StoreOps m) (contact : Nat) : m Unit := do
  if (← read).dbClient.isSome then
    let version := ((← get).contacts.versions.find? (·.1 == contact)).map (·.2) |>.getD 0
    o.insist (← dbWriteG o contact (version + 1) (.request (← o.requestFile) contact)) "the database did not acknowledge a contact's state"
    modifyContactsG fun k => { k with versions := k.versions.map (fun (c, v) => if c == contact then (c, version + 1) else (c, v)) }

/-- As `dbSubmit`, for a write whose failure is one contact's and not the session's: a client that
fails, or nodes that do not acknowledge, give `false`. The two parties tell each other what they
saw and both use the conjunction, so they take the same branch. -/
def dbSubmitSoftG (o : StoreOps m) (name : String) (authority : WriteAuthority) (version : Nat) (blob : Bytes) : m Bool := do
  dbG o (.blob name blob)
  let first ← o.dbTry (.writeBlob name authority version)
  let _ ← o.peer .submitted   -- both parties have submitted
  let second ← o.dbTry (.writeBlob name authority version)
  let acknowledged ← o.writeAcknowledged (← read).ch name
  let mine := first && second && acknowledged
  let theirs ← match ← o.peer (.acknowledged mine) with
    | .acknowledged yes => pure yes
    | _ => throw "invalid acknowledgement reply"
  pure (mine && theirs)

/-- `storeAdvanced` as an outcome: `false` when the database nodes did not take the state. -/
def storeSoftG (o : StoreOps m) (contact : Nat) : m Bool := do
  if (← read).dbClient.isNone then return true
  let fresh ← o.nonce
  let stored ← sealStateG o contact fresh
  o.insist (stored.length > 16) "invalid stored contact state"
  let taken ← dbSubmitSoftG o (toString contact) (.request (← o.requestFile) contact)
    ((← versionOfG contact) + 1) (fresh ++ stored)
  if taken then bumpVersionG contact
  pure taken

/-- A refresh's new device list is SCRATCH in the worker (operation 60 no longer touches the
contact). Here it becomes the contact's state: sealed, stored on the database nodes as the
contact's next version, and only when they acknowledged it committed in the engines. Otherwise the
scratch is dropped: the contact is exactly as before, in the engines and on the nodes. `kinds`: its
entries' kinds, stored after the ciphertext as in `sealState`. -/
def commitScratchG (o : StoreOps m) (contact : Nat) (kinds : List Nat) : m Bool := do
  let c ← read
  let fresh ← o.nonce
  let stored := (← o.scratchSeal c.w contact fresh).val
  let taken ← if c.dbClient.isSome then
      dbSubmitSoftG o (toString contact) (.request (← o.requestFile) contact)
        ((← versionOfG contact) + 1) (fresh ++ stored ++ kinds.map UInt8.ofNat ++ [UInt8.ofNat kinds.length])
    else pure true
  if taken then
    o.scratchCommit c.w contact
    if c.dbClient.isSome then bumpVersionG contact
    setKindsG contact kinds
  else o.drop c.w
  pure taken

end Generic

/-! The deployed functions: the definitions above at `SessionM` and `storeReal`. -/

abbrev db (call : DbCall) : SessionM Unit := dbG storeReal call
abbrev kindsOf (contact : Nat) : SessionM (List Nat) := kindsOfG contact
abbrev setKinds (contact : Nat) (kinds : List Nat) : SessionM Unit := setKindsG contact kinds
abbrev versionOf (contact : Nat) : SessionM Nat := versionOfG contact
abbrev bumpVersion (contact : Nat) : SessionM Unit := bumpVersionG contact
abbrev sealState (contact : Nat) (fresh : Bytes) : SessionM Bytes := sealStateG storeReal contact fresh
abbrev dbSubmit (name : String) (authority : WriteAuthority) (version : Nat) (blob : Bytes) : SessionM Bool :=
  dbSubmitG storeReal name authority version blob
abbrev dbWrite (contact version : Nat) (authority : WriteAuthority) : SessionM Bool :=
  dbWriteG storeReal contact version authority
abbrev storeAdvanced (contact : Nat) : SessionM Unit := storeAdvancedG storeReal contact
abbrev dbSubmitSoft (name : String) (authority : WriteAuthority) (version : Nat) (blob : Bytes) : SessionM Bool :=
  dbSubmitSoftG storeReal name authority version blob
abbrev storeSoft (contact : Nat) : SessionM Bool := storeSoftG storeReal contact
abbrev commitScratch (contact : Nat) (kinds : List Nat) : SessionM Bool := commitScratchG storeReal contact kinds

/-- Every path but the recovery path refuses to go on with a contact whose state did not open. -/
def requireLoaded : SessionM Unit := do
  insist (← get).contacts.unreadable.isEmpty "contact key does not match the stored state"

/-- Load a contact's stored state `version ‖ check ‖ ciphertext (‖ kinds ‖ count)`. A contact whose
stored state does not open under its key (the worker replies 0 and leaves it unloaded) is noted
(`Contacts.unreadable`): the recovery path reports it as that contact's fault; every other path
refuses to go on (`requireLoaded`). -/
def openState (contact : Nat) (stored : Bytes) : SessionM Unit := do
  let w := (← read).w
  if stored.length == 24 + 319 then
    if !(← Flow.Contacts.load w contact stored).val then
      modifyContacts fun k => { k with unreadable := k.unreadable ++ [contact] }
  else
    let count := (stored.getLast?.getD 0).toNat
    insist (1 ≤ count && count ≤ 6 && stored.length > 24 + count + 1) "stored contact shape"
    let body := stored.take (stored.length - 1 - count)
    let kinds := ((stored.drop body.length).take count).map (·.toNat)
    insist (kinds.all (· ≤ 2) && body.length == 24 + (kinds.map (fun k => if k == 0 then 319 else 1935)).foldl (· + ·) 0)
      "stored contact shape"
    if !(← Flow.Contacts.loadDevices w contact kinds body).val then
      modifyContacts fun k => { k with unreadable := k.unreadable ++ [contact] }
    setKinds contact kinds

/-- Read this party's shares (under the application's request, or of the account's own row), check
them against the other party's with the parity shares, and combine. Returns the read (public:
blobs, ids not yet served) and this party's combined shares, per id (`Secret`). -/
def dbRead (source : ReadAuthority) (name : String) : SessionM (Channels.Real.DbRead × List (String × Secret Bytes)) := do
  let c ← read
  db (.read source name)
  db (.parity name)
  let theirs ← match ← peer (.parity (← c.ch.readParity name)) with
    | .parity file => pure file
    | _ => throw "invalid parity reply"
  db (.theirParity name theirs)
  db (.verifySignatures name)
  db (.paritySum name)
  db (.combine name)
  pure (← c.ch.readDbRead name, ← c.ch.readKeyShares name)

/-- From a read: an id's combined share. -/
def dbShare (shares : List (String × Secret Bytes)) (contact : Nat) : Option (Secret Bytes) :=
  (shares.find? (·.1 == toString contact)).map (·.2)

/-- From a read: an id's blob (version, bytes in hex). -/
def dbBlob (read : Channels.Real.DbRead) (contact : Nat) : Option (Nat × String) := read.blob contact

/-- Whether the other party found the same requested ids absent from a read (not held, or `true`:
not served until the next epoch): their digests (`PeerMsg.absentDigest`) agree. -/
def absentAgreed (gone : List (Nat × Bool)) : SessionM Bool := do
  let mine := TlsWire.hash (gone.flatMap (fun (contact, later) => uint 16 contact ++ [(if later then 1 else 0 : UInt8)]))
  match ← peer (.absentDigest mine) with
  | .absentDigest theirs => pure (theirs == mine)
  | _ => throw "invalid absent-digest reply"

/-- The account's own row on the database nodes (identity key, password, certificate): a reserved
id that the two parties may read and write without an application request. -/
def accountId : Nat := 2 ^ 128 - 2

/-- Deal this party's half of a new contact's key under the application's signup token for that
id. The dealt summand is this party's share of the key. -/
def dbDeal (contact : Nat) (token : String) : SessionM (Option (Secret Bytes)) := do
  let c ← read
  let random := (← Flow.Random.joint c.w).val
  let dealt ← dbTry (.deal token contact (random.take 16))
  let (committed, summand) ← if dealt then do
      let (nodes, summand) ← c.ch.readDealt contact
      pure (nodes.map (· == "committed"), summand)
    else pure ([], none)
  -- A node commits when the second of the two halves reaches it, and tells only that party. The
  -- parties tell each other which nodes they saw commit; all but one must have.
  let mine := committed ++ List.replicate (16 - committed.length) false
  let theirs ← match ← peer (.committedNodes mine) with
    | .committedNodes nodes => pure nodes
    | _ => throw "invalid committed-nodes reply"
  let both := (List.zipWith (· || ·) mine theirs).filter id
  match summand with
  | some summand =>
    if both.length < 4 then return none
    return some summand
  | none => return none

def setVersion (contact version : Nat) : SessionM Unit :=
  modifyContacts fun k => { k with versions := k.versions.filter (·.1 != contact) ++ [(contact, version)] }

/-- The long-lived session: nothing of a contact stays in the engines or in this session's
bookkeeping (evicted if held). -/
def forget (contact : Nat) : SessionM Unit := do
  if (← get).contacts.resident.contains contact then
    Flow.Contacts.evict (← read).w contact
  modifyContacts fun k => { k with
    resident := k.resident.filter (· != contact)
    prepared := k.prepared.filter (· != contact)
    kinds := k.kinds.filter (·.1 != contact) }

/-- Contact state at rest: after two sends the state is sealed, evicted and reloaded from the
ciphertext, so the remaining sends prove the round trip preserved it. Every seal under a contact's
key uses a new version (the version is the cipher's nonce). -/
def reloadContacts (known : List (Nat × Secret Bytes × Nat)) : SessionM Unit := do
  let w := (← read).w
  for (contact, share, _) in known do
    let version ← nonce
    let stored ← sealState contact version
    insist (stored.length > 16) "invalid stored contact state"
    Flow.Contacts.evict w contact
    Flow.Contacts.key w contact share
    openState contact (version ++ stored)
  requireLoaded

/-- After the sends: every contact's advanced state goes back to the TEST store (with the database
it was stored before each send, `storeAdvanced`). -/
def writeBack (known : List (Nat × Secret Bytes × Nat)) : SessionM Unit := do
  let c ← read
  if c.dbClient.isSome then pure ()   -- stored before each send (storeAdvanced)
  else
  match c.storeDirectory with
  | none => pure ()
  | some directory =>
    for (contact, share, _) in known do
      let version ← nonce
      let stored ← sealState contact version
      insist (stored.length > 16) "invalid stored contact state"
      inBand (c.ch.saveShare directory (.testStore contact) share (version ++ stored))

end TlsMpc.Node.Session
