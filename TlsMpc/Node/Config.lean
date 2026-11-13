import TlsMpc.TlsWire
import TlsMpc.Node.Secret

/-!
# The controller's configuration (REORGANIZATION_PLAN.md stage S4)

Every environment variable the controller reads (SECURITY_MAP A.7), typed, in one `Config`. The
parser here is pure: `Config.ofEnv` takes a lookup function. The one place that reads the process
environment is `Config.read` in `TlsMpc/Node/Channels.lean` (plan section 3.2: the only file with
I/O primitives besides the worker pipe); everything else receives the value.

Three groups:
- `Agreed`: settings that change what the two controllers do, which must therefore be the same on
  both nodes. At the start of every two-party session each controller sends the other the SHA-256
  of `agreedText` and the session ends on a difference (SECURITY_MAP D.11: before, a mismatch
  showed only at the first request that differed);
- the session's kind and paths (this node's own; the kind is in `agreedText` too);
- `TestHooks`: pauses, a fixed clock, extra broadcasts, the TEST store, the trace. They are
  `none` unless the controller was started with `--test` (plan section 3.2; SECURITY_MAP D.12).
  Without `--test` they are ignored, and `ignoredHooks` names any that were set.

Still TEST scaffolding but not hooks (production paths use them until the account and contacts
come only from the database nodes; node_daemon/README.md, "What is still scaffolding"):
`SIGNAL_LOCAL_EXPORT`, `SIGNAL_LOCAL_KEM`, `SIGNAL_DB_TOKENS`. No emitter imports this module.
-/

namespace TlsMpc.Node.Config
open TlsMpc.TlsWire TlsMpc.Node

/-- Settings both nodes must have the same (SECURITY_MAP D.11), agreed at session start. -/
structure Agreed where
  /-- `SIGNAL_CLIENT_PROFILE`: `libsignal` makes what the server sees follow the official clients
  (CLIENT_FINGERPRINT.md): libsignal's ClientHello layout, upgrade requests, request JSON,
  WebSocket pings instead of keepalive requests, no client-initiated KeyUpdate, each message's
  timestamp taken when it is sent; `legacy` (the default) keeps the original behaviour. Also used
  for circuit production (`request-shape`). -/
  official : Bool
  /-- `SIGNAL_ACK_REFUSED=0`: a delivered message the session refused is left unacknowledged. -/
  keepRefused : Bool
  /-- `SIGNAL_RECOVERY` (unless `0`): a send session with the database nodes ends every input in
  a per-id result (`Recovery`); `0` runs the old fail-fast loop. -/
  recovery : Bool
  /-- `SIGNAL_PREPARE_BATCH`: contacts prepared per worker call (default 32, at most 64; 0: never). -/
  prepareBatch : Nat
  /-- `SIGNAL_BUNDLE_SLOTS` (unless `0`): the fixed-width `bundle-slot` layout (`establishTail`). -/
  bundleSlots : Bool
  /-- `SIGNAL_RECEIVE_JUMP`: read by the worker (`service_kernels.h`, how far a first message's
  number may be); the controller reads it only to agree on it. -/
  receiveJump : Option String
  /-- `TLS_WORKER_HINTED=1`: the workers' constant-depth programs (also in the worker's session
  string); the controller batches preparation only with them. -/
  hinted : Bool
  /-- `SIGNAL_TOR_CIRCUITS` (resolved: 0 without a proxy, 1 by default with one). -/
  circuits : Nat
  /-- `SIGNAL_WORKER=legacy`: the session's worker is the C++ `tls-worker*-fixture-v3`, kept
  selectable for one more stage to compare it with `node_worker` (REORGANIZATION_PLAN.md S8);
  `node` (the default): `node_worker`'s `node-worker`. The controller refuses a WORKER binary of
  the other kind (`Main.session`). Agreed: the two kinds link their workers differently. -/
  legacyWorker : Bool
  /-- `SIGNAL_SCRIPTS=NAME,NAME`: the flow groups that run as Lean scripts through the controller's
  script runner (op 93, `Flows/Select.lean`) instead of the worker's legacy operations; names from
  `scriptNames`. Empty (the default): every flow is legacy, as before. Agreed: both controllers must
  run the same flows the same way. Needs `node_worker` (`legacyWorker` false). -/
  scripts : List String := []
  deriving BEq, Repr

/-- The flow groups `SIGNAL_SCRIPTS` may name (`Flows/Select.lean` says which are available and what
each needs). -/
def scriptNames : List String :=
  ["random", "upgrade", "contacts", "account", "masks", "tls", "curve", "send", "receive", "refresh"]

/-- TEST hooks (only with `--test`). -/
structure TestHooks where
  /-- `SIGNAL_LOCAL_TIMESTAMP`: fixes the agreed clock (the same on both nodes). -/
  timestamp : Option Nat := none
  /-- `SIGNAL_LOCAL_PAUSE_AFTER=K:MS`: one pause once K inputs have a result. -/
  pauseAfter : Option (Nat × Nat) := none
  /-- `SIGNAL_LOCAL_PAUSE_REFRESH=MS`: a pause after a device refresh, before the resend. -/
  pauseRefresh : Option Nat := none
  /-- `SIGNAL_LOCAL_BROADCASTS`: broadcasts of an export session (default 2). -/
  broadcasts : Nat := 2
  /-- `SIGNAL_LOCAL_EXTRA_CONTACTS`: contacts that exist only in the TEST store. -/
  extraContacts : List Nat := []
  /-- `SIGNAL_LOCAL_NEW_CONTACT`: the first id of a contact received without the database. -/
  newContact : Nat := 1000
  /-- `SIGNAL_LOCAL_STORE`: the TEST stand-in for the database nodes (this party's directory). -/
  store : Option String := none
  /-- `SIGNAL_LOCAL_TRACE`: print revealed (public) bytes to standard error. -/
  trace : Bool := false
  deriving Repr

/-- The environment variables of `TestHooks`. -/
def hookNames : List String :=
  ["SIGNAL_LOCAL_TIMESTAMP", "SIGNAL_LOCAL_PAUSE_AFTER", "SIGNAL_LOCAL_PAUSE_REFRESH", "SIGNAL_LOCAL_BROADCASTS",
   "SIGNAL_LOCAL_EXTRA_CONTACTS", "SIGNAL_LOCAL_NEW_CONTACT", "SIGNAL_LOCAL_STORE", "SIGNAL_LOCAL_TRACE"]

/-- Which socket a session opens and with what. -/
inductive Account where
  /-- The unauthenticated socket (a send session). -/
  | none
  /-- The authenticated socket with this party's XOR share of the account id and password
  (`SIGNAL_LOCAL_CREDENTIALS` as hex, or `SIGNAL_LOCAL_CREDENTIALS_FILE`, a file holding the hex:
  how the registration ceremony hands its share to the session it starts). -/
  | share (credentials : Secret Bytes)
  /-- The authenticated socket with the account loaded from the database nodes
  (`SIGNAL_LOCAL_RECEIVE` without credentials). -/
  | stored

def Account.authenticated : Account → Bool
  | .none => false
  | _ => true

def Account.label : Account → String
  | .none => "unauthenticated"
  | .share _ => "credentials"
  | .stored => "stored"

/-- The database nodes' client (`SIGNAL_DB_CLIENT`) and its settings; each other setting is
checked where it is needed (`required`). -/
structure Database where
  client : String
  network : Option String
  key : Option String
  work : Option String
  request : Option String
  /-- TEST: signup tokens the harness supplies for contacts of the export. -/
  tokens : Option String

structure Config where
  agreed : Agreed
  /-- `SIGNAL_TOR_SOCKS=IP:PORT` (numeric). -/
  socks : Option (String × Nat)
  /-- `SIGNAL_RECORD`: the event log of this party's exchanges with the server. -/
  record : Option String
  account : Account
  /-- `SIGNAL_LOCAL_CREDENTIALS_FILE`, loaded by `Config.read` into `account`. -/
  credentialsFile : Option String
  /-- `SIGNAL_LOCAL_EXPECT`: delivered messages an authenticated session waits for (default 1). -/
  expect : Nat
  /-- `SIGNAL_LOCAL_EVENTS`: report each signup on standard output (for the node daemon). -/
  events : Bool
  /-- `SIGNAL_CEREMONY`: the registration ceremony's stage this session runs. -/
  ceremony : Option String
  /-- `SIGNAL_CEREMONY_DIR`: this node's ceremony directory. -/
  ceremonyDir : Option String
  /-- `SIGNAL_NOTIFY_MESSAGE_FILE`, `SIGNAL_NOTIFY_ID`, `SIGNAL_NOTIFY_JOURNAL`: a notify through
  the node daemon. -/
  notifyFile : Option String
  notifyId : Option String
  notifyJournal : Option String
  /-- `SIGNAL_SERVE_DIR`: the long-lived send session's job directory. -/
  serveDir : Option String
  /-- `SIGNAL_LOCAL_EXPORT` (scaffolding): the account's exported state. -/
  exportFile : Option String
  /-- `SIGNAL_LOCAL_KEM` (scaffolding): the Kyber decapsulation tool (key on its stdin). -/
  kem : Option String
  database : Option Database
  /-- `none` unless started with `--test`. -/
  test : Option TestHooks
  /-- Hooks that were set but ignored (started without `--test`). -/
  ignoredHooks : List String

/-- The test hooks in force (their defaults without `--test`). -/
def Config.hooks (c : Config) : TestHooks := c.test.getD {}

/-- A setting needed by the step about to run. -/
def required (name : String) (value : Option String) (context : String := "") : Except String String :=
  match value with
  | some v => .ok v
  | none => .error s!"{name} is required{context}"

private def number? (name : String) (value : Option String) : Except String (Option Nat) :=
  match value with
  | none => .ok none
  | some text => match text.toNat? with
    | some n => .ok (some n)
    | none => .error s!"{name} must be a number"

/-- The configuration from the environment `env`; `test`: started with `--test`. -/
def ofEnv (env : String → Option String) (test : Bool) : Except String Config := do
  let official ← match env "SIGNAL_CLIENT_PROFILE" with
    | none | some "legacy" => pure false
    | some "libsignal" => pure true
    | some other => throw s!"SIGNAL_CLIENT_PROFILE must be libsignal or legacy, not {other}"
  let legacyWorker ← match env "SIGNAL_WORKER" with
    | none | some "node" => pure false
    | some "legacy" => pure true
    | some other => throw s!"SIGNAL_WORKER must be node or legacy, not {other}"
  let scripts := (((env "SIGNAL_SCRIPTS").getD "").splitOn ",").map (·.trimAscii.toString) |>.filter (· != "")
  for name in scripts do
    unless scriptNames.contains name do
      throw s!"SIGNAL_SCRIPTS: unknown flow group {name} (known: {String.intercalate "," scriptNames})"
  if legacyWorker && !scripts.isEmpty then
    throw "SIGNAL_SCRIPTS needs node_worker (not SIGNAL_WORKER=legacy)"
  let circuitCount ← number? "SIGNAL_TOR_CIRCUITS" (env "SIGNAL_TOR_CIRCUITS")
  let socks ← match env "SIGNAL_TOR_SOCKS" with
    | none => pure none
    | some text => match text.splitOn ":" with
      | [host, port] => match port.toNat? with
        | some p => pure (some (host, p))
        | none => throw "SIGNAL_TOR_SOCKS must be IP:PORT"
      | _ => throw "SIGNAL_TOR_SOCKS must be IP:PORT"
  let circuits := circuitCount.getD (if socks.isSome then 1 else 0)
  unless (circuits == 0) == socks.isNone && circuits ≤ 16 do
    throw "SIGNAL_TOR_CIRCUITS of 1..16 needs SIGNAL_TOR_SOCKS, and SIGNAL_TOR_SOCKS at least one circuit"
  let account ← match env "SIGNAL_LOCAL_CREDENTIALS", env "SIGNAL_LOCAL_RECEIVE" with
    | some hex, _ => match Secret.ofHex hex.trimAscii.toString with
      | .ok share => pure (Account.share share)
      | .error _ => throw "SIGNAL_LOCAL_CREDENTIALS is not hex"
    | none, some _ => pure .stored
    | none, none => pure .none
  let credentialsFile := env "SIGNAL_LOCAL_CREDENTIALS_FILE"
  if credentialsFile.isSome && (env "SIGNAL_LOCAL_CREDENTIALS").isSome then
    throw "SIGNAL_LOCAL_CREDENTIALS and SIGNAL_LOCAL_CREDENTIALS_FILE are both set"
  let database := (env "SIGNAL_DB_CLIENT").map fun client =>
    { client, network := env "SIGNAL_DB_NETWORK", key := env "SIGNAL_DB_KEY", work := env "SIGNAL_DB_WORK",
      request := env "SIGNAL_DB_REQUEST", tokens := env "SIGNAL_DB_TOKENS" : Database }
  let hooks : TestHooks := {
    timestamp := (env "SIGNAL_LOCAL_TIMESTAMP").bind String.toNat?
    pauseAfter := match ((env "SIGNAL_LOCAL_PAUSE_AFTER").getD "").splitOn ":" with
      | [after, pause] => match after.toNat?, pause.toNat? with
        | some after, some pause => some (after, pause)
        | _, _ => none
      | _ => none
    pauseRefresh := (env "SIGNAL_LOCAL_PAUSE_REFRESH").bind String.toNat?
    broadcasts := ((env "SIGNAL_LOCAL_BROADCASTS").bind String.toNat?).getD 2
    extraContacts := ((env "SIGNAL_LOCAL_EXTRA_CONTACTS").getD "").splitOn "," |>.filterMap String.toNat?
    newContact := ((env "SIGNAL_LOCAL_NEW_CONTACT").bind String.toNat?).getD 1000
    store := env "SIGNAL_LOCAL_STORE"
    trace := (env "SIGNAL_LOCAL_TRACE").isSome }
  pure {
    agreed := {
      official
      keepRefused := env "SIGNAL_ACK_REFUSED" == some "0"
      recovery := env "SIGNAL_RECOVERY" != some "0"
      prepareBatch := min 64 (((env "SIGNAL_PREPARE_BATCH").bind String.toNat?).getD 32)
      bundleSlots := env "SIGNAL_BUNDLE_SLOTS" != some "0"
      receiveJump := env "SIGNAL_RECEIVE_JUMP"
      hinted := env "TLS_WORKER_HINTED" == some "1"
      circuits, legacyWorker, scripts := scripts.eraseDups }
    socks, record := env "SIGNAL_RECORD", account, credentialsFile
    expect := ((env "SIGNAL_LOCAL_EXPECT").bind String.toNat?).getD 1
    events := (env "SIGNAL_LOCAL_EVENTS").isSome
    ceremony := env "SIGNAL_CEREMONY", ceremonyDir := env "SIGNAL_CEREMONY_DIR"
    notifyFile := env "SIGNAL_NOTIFY_MESSAGE_FILE", notifyId := env "SIGNAL_NOTIFY_ID"
    notifyJournal := env "SIGNAL_NOTIFY_JOURNAL", serveDir := env "SIGNAL_SERVE_DIR"
    exportFile := env "SIGNAL_LOCAL_EXPORT", kem := env "SIGNAL_LOCAL_KEM", database
    test := if test then some hooks else none
    ignoredHooks := if test then [] else hookNames.filter (fun name => (env name).isSome) }

/-- Every variable `ofEnv` reads (what `Config.read` takes from the process environment). -/
def names : List String :=
  ["SIGNAL_CLIENT_PROFILE", "SIGNAL_TOR_CIRCUITS", "SIGNAL_TOR_SOCKS", "SIGNAL_LOCAL_CREDENTIALS",
   "SIGNAL_LOCAL_CREDENTIALS_FILE", "SIGNAL_LOCAL_RECEIVE", "SIGNAL_DB_CLIENT", "SIGNAL_DB_NETWORK", "SIGNAL_DB_KEY",
   "SIGNAL_DB_WORK", "SIGNAL_DB_REQUEST", "SIGNAL_DB_TOKENS", "SIGNAL_ACK_REFUSED", "SIGNAL_RECOVERY",
   "SIGNAL_PREPARE_BATCH", "SIGNAL_BUNDLE_SLOTS", "SIGNAL_RECEIVE_JUMP", "TLS_WORKER_HINTED", "SIGNAL_RECORD",
   "SIGNAL_LOCAL_EXPECT", "SIGNAL_LOCAL_EVENTS", "SIGNAL_CEREMONY", "SIGNAL_CEREMONY_DIR",
   "SIGNAL_NOTIFY_MESSAGE_FILE", "SIGNAL_NOTIFY_ID", "SIGNAL_NOTIFY_JOURNAL", "SIGNAL_SERVE_DIR",
   "SIGNAL_LOCAL_EXPORT", "SIGNAL_LOCAL_KEM", "SIGNAL_WORKER", "SIGNAL_SCRIPTS"] ++ hookNames

/-- What the two controllers agree on at session start, as text: the `Agreed` settings, the
session's kind, and the TEST hooks that change the agreed flow (not this node's paths, the TEST
store or the trace). -/
def agreedText (c : Config) : String :=
  let a := c.agreed
  let hooks := c.test.map fun h =>
    s!"timestamp={h.timestamp} pause_after={h.pauseAfter} pause_refresh={h.pauseRefresh} broadcasts={h.broadcasts} extra_contacts={h.extraContacts} new_contact={h.newContact}"
  s!"settings v1; profile={if a.official then "libsignal" else "legacy"} ack_refused={!a.keepRefused} recovery={a.recovery} " ++
  s!"prepare_batch={a.prepareBatch} bundle_slots={a.bundleSlots} receive_jump={a.receiveJump} hinted={a.hinted} " ++
  s!"circuits={a.circuits} worker={if a.legacyWorker then "legacy" else "node"}" ++
  (if a.scripts.isEmpty then "" else s!" scripts={String.intercalate "," a.scripts}") ++
  s!"; socket={c.account.label} expect={c.expect} ceremony={c.ceremony} serve={c.serveDir.isSome} " ++
  s!"notify={c.notifyFile.isSome} export={c.exportFile.isSome} database={c.database.isSome}; test={hooks}"

/-- The SHA-256 the two controllers exchange at session start (`PeerMsg.settingsDigest`, plan 3.1). -/
def digest (c : Config) : Bytes := TlsWire.hash (agreedText c).toUTF8.data.toList

end TlsMpc.Node.Config
