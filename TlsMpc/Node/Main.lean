import Lean
import TlsMpc.TlsWorkerProcess
import TlsMpc.Node.Policy.Request
import TlsMpc.Node.Policy.Recovery
import TlsMpc.Node.Policy.ReceiveTest
import TlsMpc.Node.Bench
import TlsMpc.Node.Session.Start
import TlsMpc.Node.Session.Receive
import TlsMpc.Node.Session.Ceremony
import TlsMpc.Node.Session.Send
import TlsMpc.Node.Session.Serve
import TlsMpc.Node.Session.Delete

/-!
# The node controller (`public_service_controller`; REORGANIZATION_PLAN.md stage S7)

`main` parses the command line and runs one thing: a check (`parse-bench`, `recovery-check`,
`policy-check`), the circuit producer's `request-shape`, the `ceremony` and `db-delete`
subcommands, or one two-party session (`session`). The executable's root,
`handshake_backend/EmpHybridWork/PublicServiceController.lean`, is `def main := TlsMpc.Node.Main.main`.

A two-party session: secret from the two parties are the contact list and the client's own keys.
Everything the server sends back is handled in the clear: each record is still decrypted and
authenticated inside the engines under the shared TLS keys, then its bytes are revealed one at a
time and parsed by the same Lean parsers the private profile compiles to circuits, run on concrete
bytes (`ByteAuth.concrete`); of a server-initiated request only the verb, path, id and headers are
revealed, never its body (`Policy/Receive.lean`). Each party runs this controller; the workers act
only on requests both controllers issue identically. Public here: record lengths and contents of
responses and control frames, request ids, the WebSocket nonce and masks. Private: credentials,
every request the client sends, all session and identity state.

Tor (PRODUCT_TODO.md section 8): `SIGNAL_TOR_SOCKS=IP:PORT` and `SIGNAL_TOR_CIRCUITS=N`, the same for
both parties. N = 0 (default): one direct connection. N ≥ 1: every connection goes through the
proxy, the server asked for by hostname; the leader's SOCKS5 username/password picks a Tor circuit
per connection (`Circuits.labels`). A send session opens N connections up front (`Session/Pool`)
and sends each contact's messages on the connection `Circuits.assign` gives it; a receive session
uses one connection with a circuit of its own.

**Where the session code is** (`TlsMpc/Node/Session/`, every function a `SessionM` action over the
channels `ch` and the flow API's worker `w`, its state threaded explicitly, `State.lean`):
- `Start`: settings agreement, connection, handshake, upgrade, the account and contacts;
- one module per kind: `Send` (one notify: `loop`, or `deliver` on the recovery path), `Serve`
  (the long-lived send session), `Receive` (the authenticated socket), `Ceremony`;
- shared: `Common` (records, waiting, keepalives), `Pool` (connections), `Store` (contacts at rest).
I/O only through `Channels` (`TlsMpc/Node/Channels.lean`); messages typed (`Messages.lean`); the
engines only through the flow API (`TlsMpc/Node/Flow.lean`); openings only as `Reveal.lean`'s kinds.
-/

namespace TlsMpc.Node.Main
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal
open Lean (toJson)
open TlsMpc.Node.Bytes TlsMpc.Node.Bench
open TlsMpc.Node TlsMpc.Node.Session

/-- PRODUCTION OF CIRCUITS ONLY (scripts/produce_circuits.py, CIRCUIT_SHAPES.md): the kernel that
seals a request frame, named as a session names it, from the frame this controller builds:
  request-shape send CERTIFICATE ENVELOPE      a send to one device     (signal-request-ctr)
  request-shape devices ENVELOPE ENVELOPE ...  one message per device   (bundle-request-ctr)
  request-shape fetch                          the prekey fetch         (bundle-fetch-ctr)
The sizes are envelope sizes in bytes. A frame's shape depends on them alone: the timestamp has 13
digits and request ids count from 2^63 (ten varint bytes). -/
def requestShape (test : Bool) (kind : String) (sizes : List String) : IO Unit := do
  let numbers ← sizes.mapM natural
  let official := (← Config.read test).agreed.official
  let mask : List (BitVec 8) := List.replicate 4 0
  let envelope (size : Nat) : List (BitVec 8) := List.replicate size 0
  let parts ← match kind, numbers with
    | "send", [certificate, size] =>
        match PublicRequest.build (envelope size) 1700000000000 (2 ^ 63) mask official with
        | .ok (frame, offsets) => pure (["signal-request-ctr", toString certificate, toString frame.length] ++ offsets.map toString)
        | .error e => throw (IO.userError e)
    | "devices", _ :: _ =>
        match PublicRequest.buildDevices (numbers.map envelope) 1700000000000 (2 ^ 63) mask official with
        | .ok (frame, payloadAt, offsets) =>
            pure (["bundle-request-ctr", toString frame.length, toString payloadAt] ++ offsets.map toString)
        | .error e => throw (IO.userError e)
    | "fetch", [] =>
        match PublicRequest.buildFetch (2 ^ 63) mask with
        | .ok (frame, payloadAt, offsets) =>
            pure (["bundle-fetch-ctr", toString frame.length, toString payloadAt] ++ offsets.map toString)
        | .error e => throw (IO.userError e)
    | _, _ => throw (IO.userError "request-shape send CERTIFICATE ENVELOPE | devices ENVELOPE ... | fetch")
  Channels.Real.report (.kernelShape parts)

/-- Unit check of the failure classification and of the response parser on failures (`Recovery.checks`). -/
def recoveryCheck : IO Unit := do
  let outcomes := Recovery.checks ()
  Channels.Real.report (.recoveryCheck (outcomes.all (·.2)) outcomes.length ((outcomes.filter (!·.2)).map (·.1)))
  unless outcomes.all (·.2) do throw (IO.userError "recovery check failed")

/-- The reveal policy's property test (T1; `TlsMpc/Node/Policy/ReceiveTest.lean`): generated server
streams, well-formed and mutated, against the reference classifier. Minutes, so a mode of its own
rather than part of `recovery-check`. -/
def policyCheck : IO Unit := do
  let outcomes := ReceiveTest.checks ()
  Channels.Real.report (.policyCheck (outcomes.all (·.2)) outcomes.length ((outcomes.filter (!·.2)).map (·.1)))
  unless outcomes.all (·.2) do throw (IO.userError "policy check failed")

/-- **The session's kind**, after `Start.run`: the ceremony's stage (SIGNAL_CEREMONY), the receive
session (the authenticated socket), or a send session: the long-lived one (SIGNAL_SERVE_DIR), one
notify on the recovery path (the database nodes), or one notify without it. A send session's
contacts' state then goes back to the TEST store (`writeBack`). Returns the responses completed. -/
def kind (started : Start.Started) : SessionM Nat := do
  let c ← read
  if let some stage := c.config.ceremony then
    return ← Ceremony.run stage started.accept
  if c.authenticated then
    return ← Receive.run started.accept
  let inputs ← Send.inputsOf (started.known.map (·.1)) started.base
  insist (c.config.serveDir.isNone || c.recovery) "SIGNAL_SERVE_DIR needs the database nodes, the export and recovery"
  let finished ← if c.recovery then
      match c.config.serveDir with
      | some folder => Serve.serve folder started.accept
      | none => Send.deliver started.accept inputs
    else Send.sendAll started.accept started.known inputs
  writeBack started.known
  TlsApplication.abort (← get).pool.first.session
  return finished

/-- Run a session on `context`: `Start.connect`, then `Start.run` and `kind` threading the
session's state. Returns the outcome and the final report's facts (what the state says when the
session ended, failed or not). -/
def run (context : Context) : IO (Except String Nat × Report) := do
  match ← (Start.connect context).run with
  | .error e => pure (.error e, {})
  | .ok first =>
    let initial : State := {
      pool := { first, connections := #[first], counters := Array.replicate (max context.sendCircuits 1) 0 }
      contacts := { nextContact := context.hooks.newContact } }
    let body : SessionM Nat := do
      let started ← Start.run
      let known := { context with self := started.self, receiving := started.receiving }
      -- A delivered envelope completed while a record is read (`Common.record`).
      let ready := { known with envelope := fun type size => (Receive.handleEnvelope type size).run known }
      withReader (fun _ => ready) (kind started)
    let (outcome, state) ← ((body.run context).run).run initial
    pure (outcome, state.report)

/-- **One two-party session**: WORKER DIRECTORY PARTY HOSTS PORT MANIFEST SESSION ENDPOINT PORT
HOSTNAME AUTH TRUST UNUSED. Spawns the worker WORKER (`node_worker`'s binary; the C++ worker only
with `SIGNAL_WORKER=legacy`; its certificate check is the checker at AUTH, with TRUST), runs the
session, and reports (`DaemonLine.finalReport`). -/
def session (test : Bool) (args : List String) : IO Unit := do
  let [worker,directory,party,hosts,basePort,manifest,session,endpoint,port,hostname,auth,trust,_unused] := args |
    throw (IO.userError "WORKER DIRECTORY PARTY HOSTS PORT MANIFEST SESSION ENDPOINT PORT HOSTNAME AUTH TRUST UNUSED")
  -- Every setting of this session (`Config`); the agreed ones are compared with the other node's
  -- at the start (`Start.connect`).
  let config ← Config.read test
  -- The worker (S8): `node_worker`'s `node-worker` for the session's mode (the caller builds it
  -- with node_worker/build.sh), or, with the agreed `SIGNAL_WORKER=legacy`, the C++
  -- `tls-worker*-fixture-v3` for one more stage. A binary of the other kind is refused here,
  -- before anything is spawned, rather than discovered at the workers' link.
  let nodeWorker := (System.FilePath.mk worker).fileName == some "node-worker"
  unless nodeWorker != config.agreed.legacyWorker do
    throw (IO.userError s!"SIGNAL_WORKER={if config.agreed.legacyWorker then "legacy" else "node"} does not match the worker binary {worker} (node: node_worker's node-worker; legacy: a tls-worker*-fixture-v3)")
  -- Every channel of the session (plan 3.2): the only way this session reaches the outside,
  -- besides the worker pipe.
  let ch := Channels.real config party
  -- The client profile (`Config.Agreed.official`): what the server sees.
  let official := config.agreed.official
  let tlsConfig : TlsWire.Config := { hostname, alpn := ["http/1.1"], profile := if official then .libsignal else .legacy }
  let certificate ← IO.mkRef false
  let running ← TlsWorkerProcess.spawn {
    executable := worker, workingDirectory := directory,party := ← natural party,
    hostsFile := hosts,port := ← natural basePort,manifestFile := manifest,sessionId := ← sessionBytes session }
    (fun name chain scheme hash signature => do
      let (valid, checkerError) ← liftM (ch.checkCertificate auth
        { hostname := name, trust, scheme, transcript := hash, signature, chain })
      liftM (ch.record (.serverCertificate name trust scheme hash chain valid checkerError))
      liftM (certificate.set valid : IO Unit);return valid)
  try
    -- The flow API's handle on the engines (`TlsMpc/Node/Flow.lean`): every worker operation of
    -- this session is a `Flow.*` function of it; it records the operations used (the final check).
    let w ← Flow.Worker.start running.rpc ch.random
    let context : Context := { ch, w, config, party, session, endpoint, port, tlsConfig
                               envelope := fun _ _ => throw "a delivered envelope before the session started" }
    let (outcome, report) ← run context
    if !outcome.isOk then
      let _ ← (Flow.Tls.abortWorker w).run
      pure ()
    let verified ← certificate.get
    let codes ← w.operations
    -- (A recovery session passes when it ended in results both parties agreed on; which
    -- operations it used depends on what happened to its contacts. Operation 15, the client's
    -- own KeyUpdate, is not used under the libsignal profile.)
    let passed := verified && outcome.isOk && (config.ceremony.isNone || report.ceremonyDone) && !codes.contains 18 &&
      (context.authenticated || report.ceremonyDone || report.recoveryUsed ||
      ((codes.contains 15 || official) && codes.contains 43 &&codes.contains 41 && codes.contains 42 && codes.contains 37 && codes.contains 38))
    let circuits := config.agreed.circuits
    ch.report (.finalReport {
      passed, certificateVerified := verified
      responsesCompleted := match outcome with | .ok n => n | .error _ => 0
      bytesRevealed := report.revealed, messagesDelivered := report.delivered, keepalives := report.keepalives
      envelopes := report.envelopes, received := report.received, refused := report.refused
      privateReceiveParsingUsed := codes.contains 18
      circuits, circuitSends := report.circuitSends
      circuitLabels := (List.range circuits).map (fun i => Circuits.labels session circuits (some i))
      -- Per id of each notify message, once both parties agreed: one of `Recovery.Result.text`.
      results := report.results
      recoveryUsed := report.recoveryUsed, recovery := report.recoveryLog
      -- Requested ids (daemon notify) left out of the session: not on the database nodes; not
      -- served until their next epoch.
      unknown := (report.absent.filter (fun entry => !entry.2)).map (·.1)
      notYetReadable := (report.absent.filter (·.2)).map (·.1)
      error := match outcome with | .ok _ => "" | .error e => e })
    unless passed do throw (IO.userError "public-receive service session failed")
  finally running.stop

/-- **The controller.** `--test` (anywhere in the arguments): the TEST hooks of `Config.TestHooks`
are in force. -/
def main (arguments : List String) : IO Unit := do
  let test := arguments.contains "--test"
  match arguments.filter (· != "--test") with
  | ["parse-bench"] => parseBench Channels.Real.benchIO
  | ["recovery-check"] => recoveryCheck
  | ["policy-check"] => policyCheck
  | "request-shape" :: kind :: sizes => requestShape test kind sizes
  | ["ceremony", configPath, name, stage] => Ceremony.stage configPath name stage
  | ["db-delete", party, request] => Delete.run test party request
  | args => session test args

end TlsMpc.Node.Main
