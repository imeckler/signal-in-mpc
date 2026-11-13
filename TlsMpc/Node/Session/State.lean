import TlsMpc.TlsApplication
import TlsMpc.Signal.RelayUpgrade
import TlsMpc.Node.Policy.Clock
import TlsMpc.Node.Policy.Receive
import TlsMpc.Node.Policy.Circuits
import TlsMpc.Node.Policy.Recovery
import TlsMpc.Node.Export
import TlsMpc.Node.Config
import TlsMpc.Node.Channels
import TlsMpc.Node.Flow

/-!
# A two-party session's context and state (REORGANIZATION_PLAN.md stage S7)

Every session function (`TlsMpc/Node/Session/*.lean`) is a `SessionM` action:
- it reads the session's fixed **context** (`Context`: the channels `ch`, the flow API's worker
  `w`, the configuration, the server's endpoint), a reader;
- it threads the session's mutable **state** (`State`) explicitly, a `StateT`. Nothing a session
  function keeps between calls is an `IO.Ref` of its own: what the old `main` held in 40 references
  is a field here, so P4 (ORD-1, ORD-2, T11) can state properties over the state a function
  returns. The state survives a failure (`ExceptT` over `StateT`): the final report of a failed
  session still says how far it came, as before.

Two kinds of reference remain inside values the session holds, both owned by libraries below it:
the TLS connection objects (`Connection`: `TlsApplication.Session`'s own state, and the slot the
connection's transport takes the next record from) and the flow API's worker (`Flow.Worker`: the
operations used, the selected connection). They are handles, not session state.

No I/O primitive here (the lint's `io-baseline`); no emitter imports this module.
-/

namespace TlsMpc.Node.Session
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal TlsMpc.Node

/-- One connection to the server: its TLS session (in the engines) and the slot its transport takes
the next record from (filled by a poll that found one: `Flow.Server.awaitRecord`, `receiveSoft`). -/
structure Connection where
  session : TlsApplication.Session TlsWorker.BufferHandle
  slot : IO.Ref (Option Bytes)

/-- The connections of the session (X2's pool builds on it). Connection 0 is the first one opened
(`first`), and the one in use unless several Tor circuits are configured.
- `connections`: by index (0 is `first`);
- `current`: the connection in use (its parser state is the caller's);
- `states`: per connection, its response parser state while another one is in use (the recovery
  path: `deliverJob`, `serve`);
- `parked`: the same for the non-recovery path (`loop`), kept apart as before S7;
- `counters`: per connection, the sends so far (request ids count from 2^63 per connection). -/
structure Pool where
  first : Connection
  connections : Array Connection
  current : Nat := 0
  states : Array PublicReceive.State := #[]
  parked : Array PublicReceive.State := #[]
  counters : Array Nat

/-- Connection `index` (connection 0 when there is no such index). -/
def Pool.connection (pool : Pool) (index : Nat) : Connection := pool.connections.getD index pool.first

/-- What the session's final report (and a job's result) says, accumulated as it runs. -/
structure Report where
  /-- Server bytes revealed (all of them public). -/
  revealed : Nat := 0
  /-- Delivered messages counted on the authenticated socket. -/
  delivered : Nat := 0
  keepalives : Nat := 0
  /-- Every delivered envelope handled: (type, content size). -/
  envelopes : List (Nat × Nat) := []
  /-- New contacts received: (contact id, the text of their first message). -/
  received : List (Nat × String) := []
  refused : Nat := 0
  /-- (contact, connection) of every send, in order. -/
  circuitSends : List (Nat × Nat) := []
  recoveryUsed : Bool := false
  ceremonyDone : Bool := false
  /-- Per-id results once both parties agreed on them. -/
  results : List Recovery.Entry := []
  /-- The recovery path's public events, in order. -/
  recoveryLog : List String := []
  /-- Requested ids left out: (id, `true`: not served until the nodes' next epoch). -/
  absent : List (Nat × Bool) := []

/-- What the session knows of its contacts in the engines (all public: ids, versions, kinds). -/
structure Contacts where
  /-- A contact with a device list: its entries' kinds (MULTI_DEVICE.md section 4); `[0]` if absent. -/
  kinds : List (Nat × List Nat) := []
  /-- Contacts whose stored state did not open under their key. -/
  unreadable : List Nat := []
  /-- Per contact, the version of its state on the database nodes this session holds. -/
  versions : List (Nat × Nat) := []
  /-- Contacts whose per-session curve work is done (`ensurePrepared`). -/
  prepared : List Nat := []
  /-- The long-lived session: contacts held in the engines from an earlier job. -/
  resident : List Nat := []
  /-- Provisional ids handed out (receiving with the database). -/
  provisionals : Nat := 0
  /-- The next new contact's id (receiving without the database). -/
  nextContact : Nat

/-- The session's mutable state, threaded through every session function. -/
structure State where
  pool : Pool
  report : Report := {}
  contacts : Contacts
  /-- Request ids of requests outside the sends' counter (keepalives, fetches, ceremony calls). -/
  extraIds : Nat := 0
  /-- The agreed time of the last exchange with the server (keepalives after 20 s of quiet). -/
  quiet : Nat := 0
  /-- Send: built content → text, for the content `notify` built (libsignal profile). -/
  bodies : List (Bytes × Bytes) := []
  /-- Send: contents already restamped. -/
  stamped : List Bytes := []
  lastStamp : Nat := 0
  /-- Send: the last message sent (resent after a device refresh). -/
  lastSent : Option (Nat × Bytes) := none
  /-- Serve: the signed request of the job being served (authorises reads and write-backs). -/
  jobRequest : Option String := none
  /-- Receive: per handled envelope, in order, whether it was refused. -/
  refusals : List Bool := []
  /-- Receive: the closing keepalive was sent. -/
  closing : Bool := false

/-- The monad under the reader: failures (`String`) over the state, so the state survives them. -/
abbrev Inner := ExceptT String (StateT State IO)

/-- A worker or channel action (`TlsClient.M`) inside a session. -/
instance : MonadLift M Inner where
  monadLift action := ExceptT.mk (StateT.lift action.run)

/-- The session's fixed context.
- `ch`: every channel (plan 3.2); `w`: the engines (the flow API);
- `party`, `session`: this party's index and the session id (as given on the command line);
- `endpoint`, `port`, `tlsConfig`: the server;
- `self`, `receiving`: what the export says of our own account (set by `Start`);
- `envelope`: what to do with a delivered envelope completed while a record is read
  (`Receive.handleEnvelope`, bound by `Main`; `Common.record` calls it). -/
structure Context where
  ch : Channels
  w : Flow.Worker
  config : Node.Config.Config
  party : String
  session : String
  endpoint : String
  port : String
  tlsConfig : TlsWire.Config
  self : Option (Bytes × Nat) := none
  receiving : Option Export.ReceiveKeys := none
  envelope : Nat → Nat → Inner Unit

/-- Every session function. -/
abbrev SessionM := ReaderT Context Inner

namespace Context
variable (c : Context)
/-- The client profile (`Config.Agreed.official`): what the server sees. -/
def official : Bool := c.config.agreed.official
def hooks : Node.Config.TestHooks := c.config.hooks
/-- The authenticated socket (credentials share, or the account stored on the database nodes). -/
def authenticated : Bool := c.config.account.authenticated
def exportPath : Option String := c.config.exportFile
def dbClient : Option String := c.config.database.map (·.client)
/-- TEST stand-in for the database nodes (one directory per party, only with `--test`). -/
def storeDirectory : Option String := c.hooks.store
/-- Tor circuits (`SIGNAL_TOR_CIRCUITS`), the same on both nodes. -/
def circuits : Nat := c.config.agreed.circuits
/-- Connections of a send session (none of the receive session's). -/
def sendCircuits : Nat := if c.authenticated then 0 else c.circuits
/-- The recovery path (a send session with the database nodes): every failure a per-id result. -/
def recovery : Bool := c.exportPath.isSome && !c.authenticated && c.dbClient.isSome && c.config.agreed.recovery
/-- The proxy and credentials of a connection (`none`: the receive socket); none without Tor. -/
def proxyFor (index : Option Nat) : Option TlsWorker.Proxy := c.config.socks.map (fun (host, p) =>
  let (username, password) := Circuits.labels c.session c.circuits index
  { host, port := p, username, password })
/-- The unauthenticated socket's upgrade request (public), for the profile. -/
def anonymousUpgrade (nonce : List (BitVec 8)) : List (BitVec 8) :=
  if c.official then RelayUpgrade.anonymousRequest PublicReceive.fast nonce
  else RelayUpgrade.legacyAnonymousRequest PublicReceive.fast nonce
end Context

/-- Change the pool, the report or the contacts. -/
def modifyPool (f : Pool → Pool) : SessionM Unit := modify fun s => { s with pool := f s.pool }
def modifyReport (f : Report → Report) : SessionM Unit := modify fun s => { s with report := f s.report }
def modifyContacts (f : Contacts → Contacts) : SessionM Unit := modify fun s => { s with contacts := f s.contacts }

/-- Lift an `IO` action of a channel (named, for readability where Lean cannot infer the monad). -/
def io (action : IO α) : SessionM α := liftM action

end TlsMpc.Node.Session
