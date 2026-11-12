import Lean
import Std.Time
import TlsMpc.TlsWorkerProcess
import TlsMpc.TlsWebSocketUpgrade
import TlsMpc.TlsWebSocketFrame
import TlsMpc.TlsWebSocketIdle
import TlsMpc.TlsWebSocketControl
import TlsMpc.TlsChatResponse
import TlsMpc.Signal.Word64Fast
import TlsMpc.Signal.RelayEncoding
import TlsMpc.Signal.PrivateTextNotification
import TlsMpc.Signal.RelayUpgrade
import TlsMpc.Signal.BundleResponse
import TlsMpc.Signal.BundleSlots
import TlsMpc.CeremonyRequests
import TlsMpc.Node.Policy.Clock
import TlsMpc.Node.Policy.Receive
import TlsMpc.Node.Policy.Request
import TlsMpc.Node.Policy.Circuits
import TlsMpc.Node.Policy.Recovery
import TlsMpc.Node.Bytes
import TlsMpc.Node.Export
import TlsMpc.Node.Bench
import TlsMpc.Node.Config
import TlsMpc.Node.Secret
import TlsMpc.Node.Channels

/-!
Service controller for the public-receive profile.

Secret from the two parties: the contact list and the client's own keys.
Everything the server sends back is handled in the clear: each record is still
decrypted and authenticated inside the engines under the shared TLS keys, then
its bytes are revealed one at a time and parsed HERE, by the same Lean parsers
the private profile compiles to circuits, run on concrete bytes
(`ByteAuth.concrete`). Each party runs this controller; the workers act only on
requests both controllers issue identically.

One restriction keeps contacts hidden: of a server-initiated request only the
verb, path, id and headers are revealed, never its body. The body of a
delivered message is an envelope: its field keys, lengths and varints are
revealed, and its sealed content goes to the engines unopened, where it is
received as a NEW contact's first message (`TlsMpc/ReceiveKernels.lean`).
Public from that: which of our prekeys the message names, its Kyber
ciphertext, and the message text. The sender's identity stays in the engines;
the contact's record is sealed and stored under a new id, and only then is the
message acknowledged. Later messages from an existing contact are not
supported yet (they are refused and acknowledged).

Public here: record lengths and contents of responses and control frames,
request ids, the WebSocket nonce and masks. Private: credentials, every
request the client sends, all session and identity state.

Tor (PRODUCT_TODO.md section 8). `SIGNAL_TOR_SOCKS=IP:PORT` (a local Tor client's SOCKS port,
numeric) and `SIGNAL_TOR_CIRCUITS=N`, the same for both parties (the proxy, credentials and
count are part of the agreed connect requests; a party configured differently aborts the
session). N = 0 (default, and no SOCKS address): one direct connection, as before. N ≥ 1: every
connection goes through the proxy, the server asked for by hostname; the leader's SOCKS5
username/password picks a Tor circuit per connection (`Circuits.labels`). A send session opens N
connections up front, each with its own TLS session and unauthenticated WebSocket, and sends
each contact's messages on the connection `Circuits.assign` gives it; a receive session uses one
connection with a circuit of its own. What the server can still link: see `Circuits`.
-/
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal
open Lean (toJson)
open TlsMpc.Node.Bytes TlsMpc.Node.Export TlsMpc.Node.Bench
open TlsMpc.Node

-- The pure parts of this controller are in library modules under `TlsMpc/Node/` (stage S2):
-- `PublicReceive` (what is revealed of the server's bytes, the parsers, the pass-over, the replies)
-- in `TlsMpc/Node/Policy/Receive.lean`; `PublicRequest` (the request templates built in the clear)
-- in `TlsMpc/Node/Policy/Request.lean`; `Circuits` (which connection each contact is sent on) in
-- `TlsMpc/Node/Policy/Circuits.lean`; `Recovery` (failures as per-contact outcomes, results, the
-- journal, and the `recovery-check` unit check) in `TlsMpc/Node/Policy/Recovery.lean`;
-- `PublicReceive.fast` and the byte conversions (`toBits`, `toBytes`, `fromHex`, `natural`,
-- `sessionBytes`) in `TlsMpc/Node/Bytes.lean`; the export parsers (`readExport`, `readSelf`,
-- `readReceive`, `ReceiveKeys`) in `TlsMpc/Node/Export.lean`; `parseBench` in
-- `TlsMpc/Node/Bench.lean`.
--
-- Stage S4: every environment variable is read once, by `Config.read` (`TlsMpc/Node/Channels.lean`),
-- into the typed `Config` of `TlsMpc/Node/Config.lean`; the TEST hooks are in force only when the
-- controller is started with `--test` (anywhere in its arguments). Secret material held here is
-- `Secret` (`TlsMpc/Node/Secret.lean`): it reaches the engines through `Secret.inputOwn`, this node's
-- disk through `Channels.saveShare`, the KEM tool through its standard input.


/-- One masking key per queued control reply (`PublicReceive.replies`), each the first 4 bytes of
its own joint randomness: RFC 6455 section 5.3 requires a fresh key for each frame. None when
nothing is queued. -/
def controlMasks (on : TlsWorker.Rpc) (s : PublicReceive.State) : TlsClient.M (List (List (BitVec 8))) :=
  (List.range (PublicReceive.queuedReplies s)).mapM fun _ => do
    let random ← on.call .publicRandom []
    TlsClient.insist (random.length == 32) "invalid joint randomness"
    pure (toBits (random.take 4))

/-- An I/O step whose failure is the session's (an error string in `M`, reported), not an exception. -/
def inBand (step : IO α) : TlsClient.M α := ExceptT.mk do
  match ← step.toBaseIO with
  | .ok value => pure (.ok value)
  | .error e => pure (.error (toString e))


/-- The end of operation 60 (`bundleEstablish`) for an item with digit counts `w`: the counts,
and with `slots` (`SIGNAL_BUNDLE_SLOTS`, on unless `0`) the splice that turns the item into the
fixed-width layout of `bundle-slot` (`BundleSlots.splice`: a count, then per run zeros 1 byte,
copy 2 bytes), so that one circuit serves every digit count (CIRCUIT_SHAPES.md). -/
def establishTail (slots : Bool) (w : BundleResponse.Widths) : List UInt8 :=
  [w.device, w.registration, w.signed, w.oneTime, w.kyber].map UInt8.ofNat ++
    (if slots then
      let runs := BundleSlots.splice w
      UInt8.ofNat runs.length :: runs.flatMap fun (zeros, copy) => [UInt8.ofNat zeros, UInt8.ofNat (copy / 256), UInt8.ofNat (copy % 256)]
    else [])





/-- `SIGNAL_RECORD=FILE` (real_signal/REAL_TEST_PLAN.md, "Recording"): every exchange with the
Signal server, one JSON line per event with this party's clock in milliseconds, appended to
FILE. Only values this controller holds in the clear: revealed server bytes, public records it
sends, the request templates of private sends (their private slots are zero here), the server's
certificate chain, statuses and outcomes. Nothing secret-shared reaches it. -/
def recordTo (record : Option String) (event : String) (fields : List (String × Lean.Json)) : IO Unit := do
  let some path := record | return
  let now := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val.toNat
  let line := (Lean.Json.mkObj ([("time_ms", toJson now), ("event", toJson event)] ++ fields)).compress
  IO.FS.withFile path .append (fun file => file.putStrLn line)


set_option maxRecDepth 16384 in   -- one long `do` block: the elaborator's default depth is not enough for it
set_option maxHeartbeats 800000 in   -- and the compiler's default budget (200000) is not either
def main (arguments : List String) : IO Unit := do
  -- `--test` (anywhere): the TEST hooks of `Config.TestHooks` are in force.
  let test := arguments.contains "--test"
  let args := arguments.filter (· != "--test")
  if args == ["parse-bench"] then
    parseBench
    return
  if args == ["recovery-check"] then
    -- Unit check of the failure classification and of the response parser on failures (`Recovery.checks`).
    let outcomes := Recovery.checks ()
    IO.println (Lean.Json.mkObj [("passed", toJson (outcomes.all (·.2))), ("checks", toJson outcomes.length),
      ("failed", toJson ((outcomes.filter (!·.2)).map (·.1)))]).compress
    unless outcomes.all (·.2) do throw (IO.userError "recovery check failed")
    return
  if let "request-shape" :: kind :: sizes := args then
    -- PRODUCTION OF CIRCUITS ONLY (scripts/produce_circuits.py, CIRCUIT_SHAPES.md): the kernel that
    -- seals a request frame, named as a session names it, from the frame this controller builds:
    --   request-shape send CERTIFICATE ENVELOPE      a send to one device     (signal-request-ctr)
    --   request-shape devices ENVELOPE ENVELOPE ...  one message per device   (bundle-request-ctr)
    --   request-shape fetch                          the prekey fetch         (bundle-fetch-ctr)
    -- The sizes are envelope sizes in bytes. A frame's shape depends on them alone: the timestamp
    -- has 13 digits and request ids count from 2^63 (ten varint bytes).
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
    IO.println (" ".intercalate ("kernel" :: parts))
    return
  if let ["ceremony", configPath, name, stage] := args then
    /- The registration ceremony, run on BOTH nodes with the same NAME (CEREMONY.md):
         public_service_controller ceremony NODE_CONFIG.json NAME register|certificate|store
       NODE_CONFIG is the node daemon's configuration (node_daemon/README.md). Each stage is one
       two-party session; this node's files are in STATE/ceremony/. Before `register`, ONE
       node's operator puts there: number.txt, keys.json (the key tool's output), captcha.txt
       (the token is longer than a terminal line: a file, never a prompt), and, when the SMS
       arrives, code.txt. `register` leaves this node's shares (credentials.share,
       recovery.share) and account.json; `certificate` leaves certificate.b64; `store` puts the
       account's row on the database nodes (it needs the sessions' export file: scaffolding). -/
    let config ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile configPath))
    let field (path : List String) : Option Lean.Json :=
      path.foldl (fun json key => json.bind (fun j => (j.getObjVal? key).toOption)) (some config)
    let text (path : List String) : IO String :=
      match (field path).bind (fun j => j.getStr?.toOption) with
      | some value => pure value
      | none => throw (IO.userError s!"the node configuration has no {".".intercalate path}")
    let count (path : List String) : IO Nat :=
      match (field path).bind (fun j => j.getNat?.toOption) with
      | some value => pure value
      | none => throw (IO.userError s!"the node configuration has no {".".intercalate path}")
    let directory := s!"{← text ["state_directory"]}/ceremony"
    IO.FS.createDirAll directory
    let hosts := (((field ["worker", "hosts"]).bind (fun j => j.getArr?.toOption)).getD #[]).toList.filterMap (fun j => j.getStr?.toOption)
    IO.FS.writeFile s!"{directory}/hosts" (String.join (hosts.map (· ++ "\n")))
    let environment := match (field ["environment"]).bind (fun j => j.getObj?.toOption) with
      | some entries => entries.toList.filterMap (fun (key, value) => value.getStr?.toOption.map (fun v => (key, v)))
      | none => []
    let manifest := match (field ["circuits", "manifest"]).bind (fun j => j.getStr?.toOption) with
      | some path => [("CIRCUIT_MANIFEST", path)]
      | none => []
    -- This node's XOR share of the credentials (left by `register`): the child session is given
    -- the file's path (SIGNAL_LOCAL_CREDENTIALS_FILE), never the value (plan 4.2 row 3).
    let shareFile := s!"{directory}/credentials.share"
    let (offset, workerDirectory, extra) ← match stage with
      | "register" => pure (100, ← text ["worker", "send_directory"], [("SIGNAL_CEREMONY", "register"), ("SIGNAL_CEREMONY_DIR", directory)])
      | "certificate" => pure (140, ← text ["worker", "receive_directory"],
          [("SIGNAL_CEREMONY", "certificate"), ("SIGNAL_CEREMONY_DIR", directory), ("SIGNAL_LOCAL_CREDENTIALS_FILE", shareFile)])
      | "store" => do
          IO.FS.createDirAll s!"{directory}/db"
          -- The existing session that creates the account's row from the credentials in two
          -- shares (it expects no message and ends at once).
          pure (180, ← text ["worker", "receive_directory"], [("SIGNAL_LOCAL_CREDENTIALS_FILE", shareFile), ("SIGNAL_LOCAL_EXPECT", "0"),
            ("SIGNAL_LOCAL_EXPORT", ← text ["test", "export"]), ("SIGNAL_LOCAL_KEM", ← text ["test", "kem_tool"]),
            ("SIGNAL_DB_CLIENT", ← text ["database", "client"]), ("SIGNAL_DB_NETWORK", ← text ["database", "network"]),
            ("SIGNAL_DB_KEY", ← text ["database", "key"]), ("SIGNAL_DB_WORK", s!"{directory}/db"),
            ("SIGNAL_DB_TOKENS", ← text ["test", "tokens"])])
      | _ => throw (IO.userError "ceremony stages: register, certificate, store")
    unless stage == "register" || (← Channels.loadShare shareFile).any (·.length == 38) do
      throw (IO.userError s!"{directory}/credentials.share is missing: run the register stage first")
    let session := TlsWorkerProcess.hex (TlsWire.hash s!"ceremony {name} {stage}".toUTF8.data.toList)
    let child ← IO.Process.output {
      cmd := ← text ["controller"]
      args := #[← text ["worker", "binary"], workerDirectory, toString (← count ["party"]), s!"{directory}/hosts",
        toString ((← count ["worker", "port_base"]) + offset), ← text ["circuits", "tool"], session, ← text ["signal", "endpoint"],
        toString (← count ["signal", "port"]), ← text ["signal", "hostname"], ← text ["signal", "certificate_checker"],
        ← text ["signal", "trust_root"], "0"]
      env := ((environment ++ manifest ++ [("SIGNAL_RECORD", s!"{directory}/record.jsonl")] ++ extra).map
        (fun (key, value) => (key, some value))).toArray }
    IO.FS.writeFile s!"{directory}/{stage}.log" child.stderr
    IO.FS.writeFile s!"{directory}/{stage}.json" child.stdout
    let report := (Lean.Json.parse ((child.stdout.splitOn "\n").headD "")).toOption.getD Lean.Json.null
    let passed := child.exitCode == 0 && (report.getObjValAs? Bool "passed").toOption == some true
    IO.println (Lean.Json.mkObj [("ceremony", toJson stage), ("passed", toJson passed), ("directory", toJson directory),
      ("error", toJson ((report.getObjValAs? String "error").toOption.getD ""))]).compress
    unless passed do throw (IO.userError s!"ceremony stage {stage} failed; see {directory}/{stage}.log")
    return
  if let ["db-delete", party, request] := args then
    -- The application's signed delete request: this party submits it to the database nodes,
    -- which act once both parties have. Repeated until all but one node has confirmed.
    let database := (← Config.read test).database
    let setting (name : String) (field : Config.Database → Option String) : IO String :=
      IO.ofExcept ((Config.required name (database.bind field)).mapError IO.userError)
    let out := s!"{← setting "SIGNAL_DB_WORK" (·.work)}/delete.json"
    for _ in [0:40] do
      let run ← IO.Process.output { cmd := ← setting "SIGNAL_DB_CLIENT" (some ·.client), args := #["delete", "--network", ← setting "SIGNAL_DB_NETWORK" (·.network),
        "--key", ← setting "SIGNAL_DB_KEY" (·.key), "--party", party, "--request", request, "--out", out] }
      unless run.exitCode == 0 do throw (IO.userError s!"database client delete: {run.stderr}")
      let done := match Lean.Json.parse (← IO.FS.readFile out) with
        | .ok json => (json.getObjValAs? Bool "acknowledged").toOption.getD false
        | .error _ => false
      if done then
        IO.println "{\"deleted\":true}"
        return
      IO.sleep 500
    throw (IO.userError "the database nodes did not confirm the delete")
  let [worker,directory,party,hosts,basePort,manifest,session,endpoint,port,hostname,auth,trust,_unused] := args |
    throw (IO.userError "WORKER DIRECTORY PARTY HOSTS PORT MANIFEST SESSION ENDPOINT PORT HOSTNAME AUTH TRUST UNUSED")
  -- Every setting of this session (`Config`); the agreed ones are compared with the other node's
  -- at the start (`settings` below).
  let config ← Config.read test
  let recordEvent (event : String) (fields : List (String × Lean.Json)) : IO Unit := recordTo config.record event fields
  let hooks := config.hooks
  -- The client profile (`Config.Agreed.official`): what the server sees.
  let official := config.agreed.official
  let tlsConfig : TlsWire.Config := { hostname, alpn := ["http/1.1"], profile := if official then .libsignal else .legacy }
  let anonymousUpgrade (nonce : List (BitVec 8)) : List (BitVec 8) :=
    if official then RelayUpgrade.anonymousRequest PublicReceive.fast nonce
    else RelayUpgrade.legacyAnonymousRequest PublicReceive.fast nonce
  let certificate ← IO.mkRef false
  let operations ← IO.mkRef ([] : List Nat)
  let revealed ← IO.mkRef 0
  -- Authenticated-socket session (`Config.Account.share`: this party's XOR share of the account
  -- id and password): wait for delivered messages instead of sending. `.stored`
  -- (SIGNAL_LOCAL_RECEIVE without credentials): the same session with the account (identity key,
  -- password) loaded from the database nodes.
  let authenticated := config.account.authenticated
  let delivered ← IO.mkRef 0
  let keepalives ← IO.mkRef 0
  let envelopes ← IO.mkRef ([] : List (Nat × Nat))
  -- New contacts received in this session: (contact id, the text of their first message).
  let received ← IO.mkRef ([] : List (Nat × String))
  let refused ← IO.mkRef 0
  let kept ← IO.mkRef (none : Option Bytes)
  -- Tor (the top of this file): SIGNAL_TOR_SOCKS=IP:PORT and SIGNAL_TOR_CIRCUITS=N (checked by `Config.ofEnv`).
  let socks := config.socks
  let circuits := config.agreed.circuits
  -- The proxy and credentials of a connection (`none`: the receive socket); none without Tor.
  let proxyFor (index : Option Nat) : Option TlsWorker.Proxy := socks.map (fun (host, p) =>
    let (username, password) := Circuits.labels session circuits index
    { host, port := p, username, password })
  -- (contact, connection) of every send, in order (public; reported).
  let circuitSends ← IO.mkRef ([] : List (Nat × Nat))
  -- Recovery (`Recovery` above): whether this session ran it, its per-id results once both
  -- parties agreed on them, and its public events in order (for the report).
  let recoveryUsed ← IO.mkRef false
  -- The registration ceremony (CEREMONY.md): SIGNAL_CEREMONY names the stage this session runs
  -- (`register` or `certificate`), SIGNAL_CEREMONY_DIR this node's ceremony directory.
  let ceremony := config.ceremony
  let ceremonyDone ← IO.mkRef false
  let results ← IO.mkRef ([] : List Recovery.Entry)
  let recoveryLog ← IO.mkRef ([] : List String)
  -- The application's notify through the node daemon (node_daemon/README.md):
  -- SIGNAL_NOTIFY_MESSAGE_FILE holds the message text, and the session's contacts are the ids of
  -- the signed request (SIGNAL_DB_REQUEST). A requested id that the database nodes do not hold,
  -- or do not serve until their next epoch (`true`), is left out of the session and reported.
  let notifyFile := config.notifyFile
  -- The long-lived send session (SIGNAL_SERVE_DIR; `serve` below, node_daemon/README.md): no
  -- contacts at the start; jobs (one signed notify each) handed over by the daemon in that directory.
  let serveDir := config.serveDir
  let absent ← IO.mkRef ([] : List (Nat × Bool))
  let running ← TlsWorkerProcess.spawn {
    executable := worker, workingDirectory := directory,party := ← natural party,
    hostsFile := hosts,port := ← natural basePort,manifestFile := manifest,sessionId := ← sessionBytes session }
    (fun name chain scheme hash signature => do
      let result ← liftM (IO.Process.output {
        cmd := auth
        args := #[name,trust,toString scheme,TlsWorkerProcess.hex hash,TlsWorkerProcess.hex signature] ++
          (chain.map TlsWorkerProcess.hex).toArray })
      let valid := result.exitCode == 0 && result.stdout.trimAscii.toString == "authenticated"
      liftM (recordEvent "server-certificate" [("hostname", toJson name), ("trust", toJson trust), ("scheme", toJson scheme),
        ("transcript_sha256", toJson (TlsWorkerProcess.hex hash)), ("chain_der_hex", toJson (chain.map TlsWorkerProcess.hex)),
        ("accepted", toJson valid), ("checker_error", toJson result.stderr.trimAscii.toString)] : IO Unit)
      liftM (certificate.set valid : IO Unit);return valid)
  try
    let rpc : TlsWorker.Rpc := {running.rpc with call := fun op input => do
      liftM (operations.modify (fun codes => if codes.contains (TlsWorkerPipe.code op) then codes else codes ++ [TlsWorkerPipe.code op]) : IO Unit)
      running.rpc.call op input}
    let action : M Nat := do
      -- The settings agreement (SECURITY_MAP D.11; plan 3.1 `PeerMsg.settingsDigest`): before
      -- anything else, each controller sends the other the SHA-256 of the settings that must be
      -- the same on both nodes (`Config.agreedText`), and the session ends on a difference.
      let settings := Config.digest config
      let theirSettings ← rpc.call .exchange settings
      insist (theirSettings == settings)
        s!"the two nodes' settings differ (SECURITY_MAP D.11); this node's: {Config.agreedText config}"
      liftM (recordEvent "connect" [("endpoint", toJson endpoint), ("port", toJson port), ("hostname", toJson hostname),
        ("socket", toJson (if authenticated then "authenticated" else "unauthenticated")), ("proxy", toJson (socks.map (·.1))),
        ("circuits", toJson circuits), ("profile", toJson (if official then "libsignal" else "legacy"))] : IO Unit)
      TlsWorker.connectVia rpc endpoint (← liftM (natural port)) (proxyFor (if authenticated then none else some 0))
      liftM (recordEvent "connected" [] : IO Unit)
      let handshake ← TlsClient.run (TlsWorker.backend rpc) (TlsWorker.transport rpc) tlsConfig
      liftM (recordEvent "handshake" [("certificate_verified", toJson handshake.serverCertificateVerified),
        ("finished_verified", toJson handshake.serverFinishedVerified)] : IO Unit)
      insist (handshake.serverCertificateVerified && handshake.serverFinishedVerified) "handshake not accepted after retirement"
      -- The worker's selected connection (`active`) and the one this controller is using
      -- (`current`, its TLS session in `apps`). Connection 0 never selects unless there are more.
      let active ← liftM (IO.mkRef 0 : IO (IO.Ref Nat))
      let app ← liftM (TlsWorker.applicationSession (TlsWorker.onConnection rpc active 0) handshake
        (some (TlsWorker.waitingTransport (TlsWorker.onConnection rpc active 0) kept)))
      let apps ← liftM (IO.mkRef #[app] : IO (IO.Ref (Array (TlsApplication.Session TlsWorker.BufferHandle))))
      let current ← liftM (IO.mkRef 0 : IO (IO.Ref Nat))
      let appNow : M (TlsApplication.Session TlsWorker.BufferHandle) := do
        pure ((← liftM (apps.get : IO (Array (TlsApplication.Session TlsWorker.BufferHandle)))).getD (← liftM (current.get : IO Nat)) app)
      let sendPublic (bytes : Bytes) : M Unit := do
        liftM (recordEvent "sent-public" [("connection", toJson (← liftM (current.get : IO Nat))), ("hex", toJson (TlsWorkerProcess.hex bytes))] : IO Unit)
        let handle ← rpc.call .publicBuffer bytes
        insist (handle.length == 8 && number handle != 0) "invalid public buffer handle"
        TlsApplication.send (← appNow) ⟨number handle⟩ bytes.length
      -- Two ways to start. Fixture: state admitted by the worker, authenticated upgrade
      -- with private credentials. Local Signal server (SIGNAL_LOCAL_EXPORT): contacts
      -- admitted from the export, and the UNAUTHENTICATED socket, whose upgrade request is
      -- public (sealed-sender sends must not go on an authenticated socket).
      let exportPath := config.exportFile
      -- TEST stand-in for the database nodes (SIGNAL_LOCAL_STORE, one directory per party, only
      -- with `--test`): per contact, this party's key share and the stored state (version, check,
      -- ciphertext).
      let storeDirectory := hooks.store
      -- TEST (no database): this party's key share of a contact, its own randomness.
      let freshShare : M (Secret Bytes) := do
        let random ← liftM (Channels.random 32)
        -- below 2^254, so below the share modulus
        pure (random.map fun bytes => bytes.take 31 ++ [(bytes.getD 31 0) &&& 0x3f])
      /- The database nodes (SIGNAL_DB_CLIENT: the `handoff_client` of secret-shared-db, with
      SIGNAL_DB_NETWORK, SIGNAL_DB_KEY and a scratch directory SIGNAL_DB_WORK). Each party
      runs the client itself: its key shares never leave it. Between the parties go only the
      parity shares of a read (whose sums must be zero) and small status bytes. A contact's
      state is one blob, `nonce ‖ check ‖ ciphertext`, which the nodes accept only when both
      parties submit the same bytes as the next version. -/
      let dbClient := config.database.map (·.client)
      let dbEnv (name : String) : M String :=
        let field : Config.Database → Option String := match name with
          | "SIGNAL_DB_NETWORK" => (·.network) | "SIGNAL_DB_KEY" => (·.key) | "SIGNAL_DB_WORK" => (·.work)
          | "SIGNAL_DB_REQUEST" => (·.request) | "SIGNAL_DB_TOKENS" => (·.tokens) | _ => fun _ => none
        liftResult (Config.required name (config.database.bind field) " with SIGNAL_DB_CLIENT")
      -- The application's signed request that authorises reads and write-backs: SIGNAL_DB_REQUEST,
      -- or in the long-lived session (`serve`) the request of the job being served.
      let jobRequest ← liftM (IO.mkRef (none : Option String) : IO (IO.Ref (Option String)))
      let requestFile : M String := do
        match ← liftM (jobRequest.get : IO (Option String)) with
        | some path => pure path
        | none => dbEnv "SIGNAL_DB_REQUEST"
      let dbWork (name : String) : M String := do pure s!"{← dbEnv "SIGNAL_DB_WORK"}/{name}"
      let dbTry (arguments : List String) : M Bool := do
        let some tool := dbClient | throw "no database client"
        let out ← liftM (IO.Process.output { cmd := tool, args := arguments.toArray })
        if out.exitCode != 0 then liftM (IO.eprintln s!"database client {arguments.headD ""}: {out.stderr}" : IO Unit)
        pure (out.exitCode == 0)
      let db (arguments : List String) : M Unit := do
        insist (← dbTry arguments) s!"database client failed: {arguments.headD ""}"
      let dbParty : M (List String) := do
        pure ["--network", ← dbEnv "SIGNAL_DB_NETWORK", "--key", ← dbEnv "SIGNAL_DB_KEY", "--party", party]
      let dbJson (name : String) : M Lean.Json := do
        liftResult (Lean.Json.parse (← liftM (IO.FS.readFile (← dbWork name) : IO String)))
      -- Each party sends the other its bytes (of any length).
      let swap (mine : Bytes) : M Bytes := do
        let size ← rpc.call .exchange (uint 4 mine.length)
        insist (size.length == 4) "invalid exchange reply"
        let width := max mine.length (number size)
        let mut rest := mine ++ List.replicate (width - mine.length) 0
        let mut theirs : Bytes := []
        while !rest.isEmpty do
          theirs := theirs ++ (← rpc.call .exchange (rest.take 60000))
          rest := rest.drop 60000
        pure (theirs.take (number size))
      -- The current time (milliseconds), agreed: each controller reads its own clock, they tell
      -- each other, and both use the later one if the two are within two minutes. (A test may
      -- fix it with SIGNAL_LOCAL_TIMESTAMP, the same for both.)
      let agreedNow : M Nat := do
        match hooks.timestamp with
        | some fixed => pure fixed
        | none =>
          let mine := (← liftM (Std.Time.Timestamp.now : IO Std.Time.Timestamp)).toMillisecondsSinceUnixEpoch.val.toNat
          liftResult (Node.Policy.Clock.agree mine (number (← swap (uint 8 mine))))
      -- A new nonce for each seal of a contact's state: joint randomness.
      let nonce : M Bytes := do
        let random ← rpc.call .publicRandom []
        insist (random.length == 32 && random.take 8 != List.replicate 8 255) "invalid joint randomness"
        pure (random.take 8)
      -- A contact with a device list (MULTI_DEVICE.md, section 4): the kinds of its devices'
      -- entries, in order (0: a 319-byte record; 1, 2: record and pending, 1935 bytes). They are
      -- public (every send's length shows them) and are stored in the clear after the
      -- ciphertext, as `kinds ‖ count`. A contact that is one established record has kinds [0]
      -- and is stored as before, without them.
      let deviceKinds ← liftM (IO.mkRef ([] : List (Nat × List Nat)) : IO (IO.Ref (List (Nat × List Nat))))
      let kindsOf (contact : Nat) : M (List Nat) := do
        pure ((((← liftM (deviceKinds.get : IO (List (Nat × List Nat)))).find? (·.1 == contact)).map (·.2)).getD [0])
      let setKinds (contact : Nat) (kinds : List Nat) : M Unit :=
        liftM (deviceKinds.modify (fun all => all.filter (·.1 != contact) ++ [(contact, kinds)]) : IO Unit)
      -- Load a contact's stored state `version ‖ check ‖ ciphertext (‖ kinds ‖ count)`.
      -- A contact whose stored state does not open under its key (the worker replies 0 and
      -- leaves it unloaded) is noted here: the recovery path reports it as that contact's
      -- fault; every other path refuses to go on (`requireLoaded`).
      let unreadable ← liftM (IO.mkRef ([] : List Nat) : IO (IO.Ref (List Nat)))
      let requireLoaded : M Unit := do
        insist (← liftM (unreadable.get : IO (List Nat))).isEmpty "contact key does not match the stored state"
      let openState (contact : Nat) (stored : Bytes) : M Unit := do
        if stored.length == 24 + 319 then
          if (← rpc.call .contactOpen (uint 16 contact ++ stored)) == [0] then
            liftM (unreadable.modify (· ++ [contact]) : IO Unit)
        else
          let count := (stored.getLast?.getD 0).toNat
          insist (1 ≤ count && count ≤ 6 && stored.length > 24 + count + 1) "stored contact shape"
          let body := stored.take (stored.length - 1 - count)
          let kinds := ((stored.drop body.length).take count).map (·.toNat)
          insist (kinds.all (· ≤ 2) && body.length == 24 + (kinds.map (fun k => if k == 0 then 319 else 1935)).foldl (· + ·) 0)
            "stored contact shape"
          if (← rpc.call .devicesOpen (uint 16 contact ++ [UInt8.ofNat count] ++ kinds.map UInt8.ofNat ++ body)) == [0] then
            liftM (unreadable.modify (· ++ [contact]) : IO Unit)
          setKinds contact kinds
      -- Seal a contact's current state under a new nonce: `check ‖ ciphertext (‖ kinds ‖ count)`.
      let sealState (contact : Nat) (fresh : Bytes) : M Bytes := do
        let stored ← rpc.call .contactSeal (uint 16 contact ++ fresh)
        insist (stored.length > 16) "invalid stored contact state"
        let kinds ← kindsOf contact
        pure (if kinds == [0] then stored else stored ++ kinds.map UInt8.ofNat ++ [UInt8.ofNat kinds.length])
      -- Store a contact's sealed state as blob `version`. Counts once all but one node committed it.
      let dbSubmit (name : String) (authority : List String) (version : Nat) (blob : Bytes) : M Bool := do
        let file ← dbWork s!"blob-{name}"
        liftM (IO.FS.writeBinFile file ⟨blob.toArray⟩ : IO Unit)
        let arguments := ["write-blob"] ++ (← dbParty) ++ authority ++ ["--version", toString version,
          "--blob-file", file, "--out", ← dbWork s!"write-{name}.json"]
        db arguments
        let _ ← swap [1]   -- both parties have submitted
        db arguments       -- repeating it reports the commit to whichever party was first
        pure (((← dbJson s!"write-{name}.json").getObjValAs? Bool "acknowledged").toOption.getD false)
      let dbWrite (contact version : Nat) (authority : List String) : M Bool := do
        let fresh ← nonce
        let stored ← sealState contact fresh
        insist (stored.length > 16) "invalid stored contact state"
        dbSubmit (toString contact) (authority ++ ["--id", toString contact]) version (fresh ++ stored)
      -- Read this party's shares (under the application's request, or of the account's own
      -- row), check them against the other party's with the parity shares, and combine.
      -- Returns the read output and this party's combined shares, per id (`Secret`).
      let dbRead (source : List String) (name : String) : M (Lean.Json × List (String × Secret Bytes)) := do
        let read ← dbWork s!"{name}-read.json"
        let mine ← dbWork s!"{name}-parity-mine.json"
        let theirs ← dbWork s!"{name}-parity-theirs.json"
        let sums ← dbWork s!"{name}-sums.json"
        let shares ← dbWork s!"{name}-shares.json"
        db (["read"] ++ (← dbParty) ++ source ++ ["--out", read])
        db ["parity", "--summands", read, "--out", mine]
        let received ← swap (← liftM (IO.FS.readBinFile mine : IO ByteArray)).data.toList
        liftM (IO.FS.writeBinFile theirs ⟨received.toArray⟩ : IO Unit)
        db ["verify-signatures", "--network", ← dbEnv "SIGNAL_DB_NETWORK", "--reports", theirs]
        db ["parity-sum", "--mine", mine, "--theirs", theirs, "--out", sums]
        db ["combine", "--summands", read, "--parity-sums", sums, "--out", shares]
        pure (← dbJson s!"{name}-read.json", ← inBand (Channels.readKeyShares shares))
      -- From a read: an id's combined share, and its blob (version, bytes in hex).
      let dbEntry (json : Lean.Json) (contact : Nat) : Option Lean.Json :=
        (((json.getObjValAs? (Array Lean.Json) "ids").toOption.getD #[]).toList).find?
          (fun e => (e.getObjValAs? String "id").toOption == some (toString contact))
      let dbShare (shares : List (String × Secret Bytes)) (contact : Nat) : Option (Secret Bytes) :=
        (shares.find? (·.1 == toString contact)).map (·.2)
      let dbBlob (read : Lean.Json) (contact : Nat) : Option (Nat × String) :=
        ((dbEntry read contact).bind (fun e => (e.getObjVal? "blob").toOption)).bind (fun b =>
          match b.getObjValAs? Nat "version", b.getObjValAs? String "hex" with
          | .ok version, .ok hex => some (version, hex)
          | _, _ => none)
      -- The account's own row on the database nodes (identity key, password, certificate): a
      -- reserved id that the two parties may read and write without an application request.
      let accountId := 2 ^ 128 - 2
      -- Deal this party's half of a new contact's key under the application's signup token
      -- for that id. The dealt summand is this party's share of the key.
      let dbDeal (contact : Nat) (token : String) : M (Option (Secret Bytes)) := do
        let random ← rpc.call .publicRandom []
        insist (random.length == 32) "invalid joint randomness"
        let dealt ← dbTry (["deal"] ++ (← dbParty) ++ ["--signup-token", token, "--id", toString contact,
          "--session", TlsWorkerProcess.hex (random.take 16), "--out", ← dbWork s!"deal-{contact}.json"])
        let (committed, summand) ← if dealt then do
            let (nodes, summand) ← inBand (Channels.readDealt (← dbWork s!"deal-{contact}.json"))
            pure (nodes.map (fun status => if status == "committed" then (1 : UInt8) else 0), summand)
          else pure ([], none)
        -- A node commits when the second of the two halves reaches it, and tells only that
        -- party. The parties tell each other which nodes they saw commit; all but one must have.
        let mine := committed ++ List.replicate (16 - committed.length) 0
        let theirs ← swap mine
        let both := (List.zipWith (fun a b => a == 1 || b == 1) mine theirs).filter id
        match summand with
        | some summand =>
          if both.length < 4 then return none
          return some summand
        | none => return none
      -- Per contact: id, key share, version of the stored state it was loaded from (0: none).
      -- The registration ceremony (CEREMONY.md): no account exists yet. Its `register` stage
      -- uses the unauthenticated socket; its `certificate` stage the authenticated one, with
      -- this node's XOR share of the new credentials (SIGNAL_LOCAL_CREDENTIALS).
      let ceremonyUpgrade (stage : String) : M (Bytes × List (Nat × Secret Bytes × Nat) × Bool) := do
        if stage == "certificate" then
          let .share share := config.account | throw "the certificate stage needs this node's credentials share"
          let _ ← Secret.inputOwn rpc .accountCredentials share
          let upgrade ← rpc.call .providerUpgradeOpen (uint 8 1)
          insist (upgrade.length == 38) "invalid upgrade receipt"
          TlsApplication.send app ⟨number (upgrade.take 8)⟩ (number ((upgrade.drop 8).take 2))
          pure (upgrade.drop 10, [], true)
        else
          let upgrade ← rpc.call .publicUpgrade []
          insist (upgrade.length == 44) "invalid public upgrade receipt"
          sendPublic (toBytes (anonymousUpgrade (toBits (upgrade.take 16))))
          pure (upgrade.drop 16, [], true)
      let (accept, known, keyed) ← match ceremony, exportPath with
        | some stage, _ => ceremonyUpgrade stage
        | none, none => do
          let catalogue ← rpc.call .providerCatalogue []
          insist (catalogue.length ≥ 10) "invalid provider catalogue"
          let state := number (catalogue.take 8)
          let count := number ((catalogue.drop 8).take 2)
          insist (state != 0 && count == 4 && catalogue.length == 10+8*count) "fixture catalogue changed"
          -- Private upgrade request; the expected accept value is public.
          let upgrade ← rpc.call .providerUpgradeOpen (uint 8 state)
          insist (upgrade.length == 38) "invalid upgrade receipt"
          TlsApplication.send app ⟨number (upgrade.take 8)⟩ (number ((upgrade.drop 8).take 2))
          pure (upgrade.drop 10, [(1, ← freshShare, 0), (2, ← freshShare, 0)], false)
        | none, some path => do
          let text ← liftM (IO.FS.readFile path : IO String)
          let (certificate, identity, records) ← liftResult (readExport text)
          let accountStored ← if dbClient.isSome then do
              let (accountRead, accountShares) ← dbRead ["--account"] "account"
              match dbShare accountShares accountId, dbBlob accountRead accountId with
              | some share, some (_, blob) =>
                let _ ← Secret.inputOwn rpc .accountKey share
                let _ ← rpc.call .accountOpen (← liftResult (fromHex blob))
                pure true
              | _, _ => pure false
            else pure false
          -- TEST: until the account's row exists it is admitted from the export.
          unless accountStored do
            let _ ← Secret.inputOwn rpc .accountAdmit (identity ++ Secret.hide certificate)
          -- Per wanted contact: its TEST record from the export, if it has one.
          let records : List (Nat × Option (Secret Bytes)) := records.map fun (contact, record) => (contact, some record)
          -- Contacts that exist only in the store (received in an earlier session).
          let extra := hooks.extraContacts.map (fun contact => (contact, (none : Option (Secret Bytes))))
          -- (The long-lived session starts with none: each job loads its own, `loadJob`.)
          let wanted := if authenticated || serveDir.isSome then [] else records ++ extra
          -- Through the daemon: exactly the ids of the application's signed request, whose message
          -- hash must be the text's. (TEST: an id of the export is still created from it.)
          let wanted ← match notifyFile, authenticated with
            | some file, false => do
              let text ← liftM (IO.FS.readFile file : IO String)
              let request ← liftResult (Lean.Json.parse (← liftM (IO.FS.readFile (← dbEnv "SIGNAL_DB_REQUEST") : IO String)))
              let ids := ((request.getObjValAs? (Array String) "ids").toOption.getD #[]).toList.filterMap String.toNat?
              insist (!ids.isEmpty) "the notify request lists no ids"
              let signedFor ← liftResult (fromHex ((request.getObjValAs? String "message_hash").toOption.getD ""))
              insist (signedFor == TlsWire.hash text.toUTF8.data.toList) "the message is not the one the notify request was signed for"
              pure (ids.map (fun id => (id, (records.find? (·.1 == id)).bind (·.2))))
            | _, _ => pure wanted
          let known ← if dbClient.isSome && !wanted.isEmpty then do
            -- From the database nodes, under the application's signed request for these ids.
            let (readJson, sharesJson) ← dbRead ["--request", ← dbEnv "SIGNAL_DB_REQUEST"] "contacts"
            -- A contact created moments ago is not served until the nodes' next epoch.
            let waiting := ((readJson.getObjValAs? (Array String) "not_yet_readable").toOption.getD #[]).toList
            -- Through the daemon, such an id, and one the nodes do not hold at all (unless the
            -- TEST export can create it), is that id's result and not the session's end. Both
            -- parties must have found the same ones.
            let wanted ← if notifyFile.isNone then pure wanted else do
              let gone := wanted.filterMap (fun (contact, record) =>
                if waiting.contains (toString contact) then some (contact, true)
                else if record.isNone && ((dbShare sharesJson contact).isNone || (dbBlob readJson contact).isNone) then some (contact, false)
                else none)
              let mine := TlsWire.hash (gone.flatMap (fun (contact, later) => uint 16 contact ++ [(if later then 1 else 0 : UInt8)]))
              insist ((← swap mine) == mine) "the two parties' database reads differ"
              liftM (absent.set gone : IO Unit)
              pure (wanted.filter (fun (contact, _) => !gone.any (·.1 == contact)))
            insist (wanted.all (fun (contact, _) => !waiting.contains (toString contact))) "a contact is not readable until the database's next epoch"
            wanted.mapM (fun (contact, record) => do
              let share := dbShare sharesJson contact
              let blob := dbBlob readJson contact
              match share, blob with
              | some share, some (version, blob) =>
                let _ ← Secret.inputOwn rpc .contactKey (Secret.hide (uint 16 contact) ++ share)
                -- Both parties must have been given the same blob: the request is agreed.
                openState contact (← liftResult (fromHex blob))
                pure (contact, share, version)
              | _, _ =>
                -- TEST: a contact of the export that the database does not have yet is created
                -- there, under a signup token the harness supplies (SIGNAL_DB_TOKENS/<id>.json).
                let some record := record | throw "contact is not in the database"
                let some share ← dbDeal contact s!"{← dbEnv "SIGNAL_DB_TOKENS"}/{contact}.json" | throw "dealing a contact key failed"
                let _ ← Secret.inputOwn rpc .contactAdmit (Secret.hide (uint 16 contact) ++ record)
                let _ ← Secret.inputOwn rpc .contactKey (Secret.hide (uint 16 contact) ++ share)
                pure (contact, share, 0))
          else wanted.mapM (fun (contact, record) => do
            let saved ← match storeDirectory with
              | none => pure none
              | some directory => inBand (Channels.loadStored ((directory : System.FilePath) / toString contact))
            match saved with
            | some (share, rest) =>
              -- A stored contact: key from the shares, then the state from its ciphertext.
              insist (share.length == 32 && rest.length > 24) "stored contact shape"
              let _ ← Secret.inputOwn rpc .contactKey (Secret.hide (uint 16 contact) ++ share)
              openState contact rest
              pure (contact, share, number (rest.take 8))
            | none =>
              let some record := record | throw "contact has no stored state"
              let share ← freshShare
              let _ ← Secret.inputOwn rpc .contactAdmit (Secret.hide (uint 16 contact) ++ record)
              let _ ← Secret.inputOwn rpc .contactKey (Secret.hide (uint 16 contact) ++ share)
              pure (contact, share, 0))
          if authenticated then
            match config.account with
            | .share share =>
              -- The password is shared: neither party can open this socket alone.
              let _ ← Secret.inputOwn rpc .accountCredentials share
              if dbClient.isSome && !accountStored then
                -- TEST: the first session that has the account's key and credentials creates its
                -- row on the database nodes (key dealt under a token for the reserved id).
                let some keyShare ← dbDeal accountId s!"{← dbEnv "SIGNAL_DB_TOKENS"}/{accountId}.json" | throw "dealing the account key failed"
                let _ ← Secret.inputOwn rpc .accountKey keyShare
                let fresh ← nonce
                let stored ← rpc.call .accountSeal fresh
                insist (stored.length > 16) "invalid stored account state"
                insist (← dbSubmit "account" ["--account"] 1 (fresh ++ stored)) "the database did not acknowledge the account's state"
            | _ => insist accountStored "no credentials: the account is not stored and none were given"
            let upgrade ← rpc.call .providerUpgradeOpen (uint 8 1)
            insist (upgrade.length == 38) "invalid upgrade receipt"
            TlsApplication.send app ⟨number (upgrade.take 8)⟩ (number ((upgrade.drop 8).take 2))
            pure (upgrade.drop 10, known, true)
          else
            let upgrade ← rpc.call .publicUpgrade []
            insist (upgrade.length == 44) "invalid public upgrade receipt"
            sendPublic (toBytes (anonymousUpgrade (toBits (upgrade.take 16))))
            pure (upgrade.drop 16, known, true)
      let contacts := known.map (·.1)
      -- Receiving (authenticated socket with an export): a delivered sealed-sender envelope is
      -- opened in the engines as a NEW contact's first message. Public here: our prekey ids the
      -- message names, the Kyber ciphertext, and the message text. The contact's record is
      -- sealed and stored under a new id before the message is acknowledged.
      let receiving ← match exportPath, authenticated with
        | some path, true => do
          pure (some (← liftResult (readReceive (← liftM (IO.FS.readFile path : IO String)))))
        | _, _ => pure none
      let nextContact ← liftM (IO.mkRef hooks.newContact : IO (IO.Ref Nat))
      -- Provisional ids (with the database), one per opened message, from 2^128 - 3 down: the
      -- worker keeps the entry of a contact refused after its session was made (evicted, not
      -- erased) and makes a session only under an id with no entry, so a provisional id is never
      -- reused within a session. Both controllers count the same messages in the same order.
      let provisionals ← liftM (IO.mkRef (0 : Nat) : IO (IO.Ref Nat))
      let decapsulate (key : Secret Bytes) (ciphertext : Bytes) : M (Secret Bytes) := do
        -- Kyber-1024 decapsulation runs outside the engines, with a key both parties hold (OWN):
        -- the key goes to the tool on its standard input (`Channels.kemDecapsulate`).
        let some tool := config.kem | throw "SIGNAL_LOCAL_KEM (decapsulation tool) is required"
        liftResult (← liftM (Channels.kemDecapsulate tool key ([8] ++ ciphertext)))
      -- A refusal of the envelope being handled, with its reason (SIGNAL_RECORD).
      let refusedBecause (reason : String) : M (Option (Nat × String)) := do
        liftM (recordEvent "envelope-refused" [("reason", toJson reason)] : IO Unit)
        return none
      let receiveFirst (keys : ReceiveKeys) : M (Option (Nat × String)) := do
        -- The certificate's expiry is checked against a time both controllers agree on.
        let now ← agreedNow
        let signerId := toBytes (PublicReceive.varint keys.serverId)
        let opened ← rpc.call .envelopeOpen (keys.identityPublic ++ uint 8 now ++ keys.serverKey ++
          uint 2 keys.serverCertificate.length ++ keys.serverCertificate ++ uint 2 signerId.length ++ signerId)
        if opened.head? != some 255 then
          return ← refusedBecause s!"not opened as a new contact's first message (reply {opened.headD 0}: sealed-sender layer, sender certificate, PreKey shape, or no kernel for its shape)"
        insist (opened.length == 14 + 1568) "invalid opened prekey message"
        let find (table : List (Nat × Secret Bytes)) (at_ : Nat) : Option (Secret Bytes) :=
          (table.find? (·.1 == number ((opened.drop at_).take 4))).map (·.2)
        let oneTime := if opened.getD 1 0 == 1 then find keys.oneTime 2 else some (Secret.hide (List.replicate 32 0))
        match oneTime, find keys.signed 6, find keys.kyber 10 with
        | some oneTime, some signed, some kyber =>
          let secret ← decapsulate kyber (opened.drop 14)
          -- With the database, the contact's id is named by the message itself; until then
          -- the contact is held under a provisional id (2^128 - 1, then 2^128 - 3, 2^128 - 4, …).
          let provisional ← liftM (provisionals.modifyGet (fun n => (if n == 0 then 2 ^ 128 - 1 else 2 ^ 128 - 2 - n, n + 1)) : IO Nat)
          let contact ← if dbClient.isSome then pure provisional else liftM (nextContact.modifyGet (fun n => (n, n + 1)) : IO Nat)
          let result ← Secret.inputOwn rpc .envelopeSession
            (Secret.hide (uint 16 contact ++ keys.address) ++ signed ++ oneTime ++ secret ++ Secret.hide (uint 8 (2 ^ 63)))
          if result.head? != some 255 then return ← refusedBecause s!"no session from it (reply {result.headD 0}: keys, MAC, content or text shape)"
          insist (result.length ≥ 3 && result.length == 3 + number ((result.drop 1).take 2)) "invalid received text"
          let text := (String.fromUTF8? ⟨(result.drop 3).toArray⟩).getD ""
          if dbClient.isSome then
            -- The text is the application's signup token (JSON: id, signature). It names the
            -- contact's id and is what authorises the database nodes to create it. A token the
            -- nodes do not accept (forged, or already used) refuses the message.
            let refuse (contact : Nat) : M (Option (Nat × String)) := do
              let _ ← rpc.call .contactEvict (uint 16 contact)
              refusedBecause s!"the text is not a signup token the database nodes accept, or they did not store the contact ({text.length} characters)"
            -- Fixed width: base64 of the id (16 bytes) and the application's signature (64).
            let pasted ← dbWork "token-received"
            liftM (IO.FS.writeFile pasted text : IO Unit)
            let some tool := dbClient | throw "no database client"
            let parsed ← liftM (IO.Process.output { cmd := tool, args := #["token-id", "--signup-token", pasted, "--require-fixed"] })
            let named := if parsed.exitCode == 0 then parsed.stdout.trimAscii.toString.toNat? else none
            match named with
            | none => refuse provisional
            | some id =>
              if id ≥ accountId then return ← refuse provisional
              let token ← dbWork s!"token-{id}"
              liftM (IO.FS.writeFile token text : IO Unit)
              if (← rpc.call .contactAssign (uint 16 provisional ++ uint 16 id)) != [255] then
                return ← refusedBecause s!"the new contact could not take the token's id {id}"
              match ← dbDeal id token with
              | none => refuse id
              | some share =>
                let _ ← Secret.inputOwn rpc .contactKey (Secret.hide (uint 16 id) ++ share)
                -- Stored (acknowledged by the nodes) before the message is acknowledged.
                if !(← dbWrite id 1 ["--signup-token", token]) then return ← refuse id
                return some (id, text)
          else
          -- Stored before it is acknowledged.
          let share ← freshShare
          let fresh ← nonce
          let _ ← Secret.inputOwn rpc .contactKey (Secret.hide (uint 16 contact) ++ share)
          let stored ← rpc.call .contactSeal (uint 16 contact ++ fresh)
          insist (stored.length > 16) "invalid stored contact state"
          match storeDirectory with
          | some directory => inBand (Channels.saveShare ((directory : System.FilePath) / toString contact) share (fresh ++ stored))
          | none => pure ()
          return some (contact, text)
        | _, _, _ =>
          -- The message names a prekey we do not hold.
          TlsWorker.emptyReply rpc .envelopeDrop []
          refusedBecause s!"it names a prekey this account does not hold (one-time {opened.getD 1 0 == 1}, signed {number ((opened.drop 6).take 4)}, Kyber {number ((opened.drop 10).take 4)})"
      -- `SIGNAL_ACK_REFUSED=0` (the same on both nodes): a delivered message this session refused
      -- is left unacknowledged, so the server keeps it for a later session (a fixed build can then
      -- process it). Default: acknowledged, as before. `refusals`: per handled envelope, in order,
      -- whether it was refused (each delivered-message request carries one envelope).
      let keepRefused := config.agreed.keepRefused
      let refusals ← liftM (IO.mkRef ([] : List Bool) : IO (IO.Ref (List Bool)))
      let handleEnvelope (kind size : Nat) : M Unit := do
        liftM (envelopes.modify (· ++ [(kind, size)]) : IO Unit)
        let outcome ← match receiving with
          | some keys => do
            if kind == 6 && size > 0 then
              match ← receiveFirst keys with
              | some entry =>
                liftM (received.modify (· ++ [entry]) : IO Unit)
                -- For the node daemon (SIGNAL_LOCAL_EVENTS): the id that signed up, as soon as it is stored.
                if config.events then
                  liftM (IO.println (Lean.Json.mkObj [("event", toJson "signup"), ("id", toJson (toString entry.1))]).compress : IO Unit)
                  liftM ((do (← IO.getStdout).flush) : IO Unit)
                pure (some entry)
              | none =>
                liftM (refused.modify (· + 1) : IO Unit)
                pure none
            else
              -- Not a sealed-sender message: not supported, dropped.
              liftM (refused.modify (· + 1) : IO Unit)
              TlsWorker.emptyReply rpc .envelopeDrop []
              refusedBecause s!"not a sealed-sender message (envelope type {kind}, {size} bytes of content)"
          | none => do
            TlsWorker.emptyReply rpc .envelopeDrop []
            pure none
        liftM (refusals.modify (· ++ [outcome.isNone]) : IO Unit)
        liftM (recordEvent "envelope" [("type", toJson kind), ("content_bytes", toJson size),
          ("outcome", toJson (match outcome with | some entry => s!"new contact {entry.1}" | none => "refused"))] : IO Unit)
      -- Reveal and parse one authenticated record, byte by byte.
      let record (handle : Nat) (start : PublicReceive.State) : M (PublicReceive.State × Bool) := do
        let mut s := start
        let mut complete := false
        let mut offset := 0
        -- The length alone (an offset past any record reveals no byte).
        let probe ← rpc.call .revealRange (uint 8 handle ++ uint 2 65535 ++ uint 2 1)
        insist (probe.length == 2) "invalid reveal reply"
        let mut length := number probe
        liftM (recordEvent "record" [("connection", toJson (← liftM (current.get : IO Nat))), ("handle", toJson handle),
          ("content_bytes", toJson length)] : IO Unit)
        while offset < length do
          if s.skip > 0 then
            -- A server request's body: passed over, never revealed.
            let count := min s.skip (length - offset)
            liftM (recordEvent "passed-over" [("handle", toJson handle), ("offset", toJson offset), ("bytes", toJson count),
              ("to", toJson (if s.capture then "engines (delivered envelope)" else if s.collect then "engines (prekey response)" else "nowhere"))] : IO Unit)
            if s.capture then
              -- A delivered envelope's sealed content goes to the engines as it is.
              let held ← rpc.call .envelopeTake (uint 8 handle ++ uint 2 offset ++ uint 2 count)
              insist (held.length == 4) "invalid envelope reply"
            if s.collect then
              -- The body of the 200 to the pending prekey fetch goes to the engines as it is.
              let held ← rpc.call .bundleTake (uint 8 handle ++ uint 2 offset ++ uint 2 count)
              insist (held.length == 4) "invalid bundle reply"
            -- As much of it as `passRoom` allows in one step (`passRun_bulk`: the state the byte-by-byte
            -- steps would give), the rest one byte at a time. A response may complete in its body.
            let bulk := min count (PublicReceive.passRoom s)
            s := PublicReceive.passBulk bulk s
            for _ in [0:count - bulk] do
              let (next, done) ← liftResult (PublicReceive.passOne s)
              s := next
              complete := complete || done
            offset := offset + count
            -- A completed envelope is dealt with before anything further is read.
            for (kind, size) in s.envelopes do handleEnvelope kind size
            s := { s with envelopes := [] }
            continue
          insist (PublicReceive.mayReveal s) "refusing to reveal a server-initiated message"
          let count := PublicReceive.budget s
          let out ← rpc.call .revealRange (uint 8 handle ++ uint 2 offset ++ uint 2 count)
          insist (out.length ≥ 2 && out.length ≤ 2 + count) "invalid reveal reply"
          length := number (out.take 2)
          let bytes := out.drop 2
          if offset < length then
            insist (!bytes.isEmpty) "missing revealed bytes"
            liftM (revealed.modify (· + bytes.length) : IO Unit)
            -- Diagnostics: the revealed (public) bytes, on request.
            if hooks.trace then
              liftM (IO.eprintln s!"revealed {TlsWorkerProcess.hex bytes}" : IO Unit)
            liftM (recordEvent "revealed" [("handle", toJson handle), ("offset", toJson offset), ("hex", toJson (TlsWorkerProcess.hex bytes))] : IO Unit)
            for (byte, index) in bytes.zipIdx do
              let (next, done) ← liftResult (PublicReceive.step s (BitVec.ofNat 8 byte.toNat))
              -- What is left of this step must still be within what may be revealed.
              insist (bytes.length - (index + 1) == 0 || (PublicReceive.mayReveal next && bytes.length - (index + 1) ≤ PublicReceive.budget next))
                "revealed range went past what may be revealed"
              s := next
              complete := complete || done
          offset := offset + (if bytes.isEmpty then 1 else bytes.length)
          for (kind, size) in s.envelopes do handleEnvelope kind size
          s := { s with envelopes := [] }
        return (s, complete)
      -- One send: the engines produce and open the sealed-sender envelope; the request
      -- is assembled here; the engines insert the contact's fields and seal the record.
      -- With the database: the contact's advanced state is stored (and acknowledged by the
      -- nodes) BEFORE its message leaves. If the session dies afterwards the stored state is
      -- never behind what was sent, so no message key or counter can be used twice; at worst
      -- a message that was stored for but never sent leaves a gap in the counter.
      let versions ← liftM (IO.mkRef (known.map (fun (contact, _, version) => (contact, version))) : IO (IO.Ref (List (Nat × Nat))))
      let storeAdvanced (contact : Nat) : M Unit := do
        if dbClient.isSome then
          let version := ((← liftM (versions.get : IO (List (Nat × Nat)))).find? (·.1 == contact)).map (·.2) |>.getD 0
          insist (← dbWrite contact (version + 1) ["--request", ← requestFile]) "the database did not acknowledge a contact's state"
          liftM (versions.modify (fun all => all.map (fun (c, v) => if c == contact then (c, version + 1) else (c, v))) : IO Unit)
      -- As `dbSubmit`, for a write whose failure is one contact's and not the session's: a client
      -- that fails, or nodes that do not acknowledge, give `false`. The two parties tell each
      -- other what they saw and both use the conjunction, so they take the same branch.
      let dbSubmitSoft (name : String) (authority : List String) (version : Nat) (blob : Bytes) : M Bool := do
        let file ← dbWork s!"blob-{name}"
        liftM (IO.FS.writeBinFile file ⟨blob.toArray⟩ : IO Unit)
        let arguments := ["write-blob"] ++ (← dbParty) ++ authority ++ ["--version", toString version,
          "--blob-file", file, "--out", ← dbWork s!"write-{name}.json"]
        let first ← dbTry arguments
        let _ ← swap [1]   -- both parties have submitted
        let second ← dbTry arguments
        let mine := first && second &&
          ((← dbJson s!"write-{name}.json").getObjValAs? Bool "acknowledged").toOption.getD false
        let theirs ← swap [if mine then 1 else 0]
        pure (mine && theirs == [1])
      let versionOf (contact : Nat) : M Nat := do
        pure (((← liftM (versions.get : IO (List (Nat × Nat)))).find? (·.1 == contact)).map (·.2) |>.getD 0)
      let bumpVersion (contact : Nat) : M Unit := do
        let version ← versionOf contact
        liftM (versions.modify (fun all => all.map (fun (c, v) => if c == contact then (c, version + 1) else (c, v))) : IO Unit)
      -- `storeAdvanced` as an outcome: `false` when the database nodes did not take the state.
      let storeSoft (contact : Nat) : M Bool := do
        if dbClient.isNone then return true
        let fresh ← nonce
        let stored ← sealState contact fresh
        insist (stored.length > 16) "invalid stored contact state"
        let taken ← dbSubmitSoft (toString contact) (["--request", ← requestFile] ++ ["--id", toString contact])
          ((← versionOf contact) + 1) (fresh ++ stored)
        if taken then bumpVersion contact
        pure taken
      -- A refresh's new device list is SCRATCH in the worker (operation 60 no longer touches the
      -- contact). Here it becomes the contact's state: sealed, stored on the database nodes as
      -- the contact's next version, and only when they acknowledged it committed in the engines.
      -- Otherwise the scratch is dropped: the contact is exactly as before, in the engines and
      -- on the nodes. `kinds`: its entries' kinds, stored after the ciphertext as in `sealState`.
      let commitScratch (contact : Nat) (kinds : List Nat) : M Bool := do
        let fresh ← nonce
        let stored ← rpc.call .scratchSeal (uint 16 contact ++ fresh)
        insist (stored.length > 16) "invalid sealed device list"
        let taken ← if dbClient.isSome then
            dbSubmitSoft (toString contact) (["--request", ← requestFile] ++ ["--id", toString contact])
              ((← versionOf contact) + 1) (fresh ++ stored ++ kinds.map UInt8.ofNat ++ [UInt8.ofNat kinds.length])
          else pure true
        if taken then
          TlsWorker.emptyReply rpc .scratchCommit (uint 16 contact)
          if dbClient.isSome then bumpVersion contact
          setKinds contact kinds
        else TlsWorker.emptyReply rpc .bundleDrop []
        pure taken
      -- Our own address and registration id, for sessions the client starts (a contact's new device).
      let self ← match exportPath with
        | some path => do pure (some (← liftResult (readSelf (← liftM (IO.FS.readFile path : IO String)))))
        | none => pure none
      let lastSent ← liftM (IO.mkRef (none : Option (Nat × Bytes)) : IO (IO.Ref (Option (Nat × Bytes))))
      -- libsignal profile: a message's timestamp is the agreed clock when it is first sent (an
      -- official client stamps each message when it is sent; a broadcast built ahead with
      -- base + index drifts ever further behind the server's clock), strictly increasing within
      -- the session, and kept when the same message is sent again (a resend after a device
      -- refresh). The built content is rebuilt from its text with the new timestamp: the same
      -- size class, since the timestamp's varint keeps its width. `bodies`: built content → text,
      -- for the content `notify` built; `stamped`: contents already restamped.
      let bodies ← liftM (IO.mkRef ([] : List (Bytes × Bytes)) : IO (IO.Ref (List (Bytes × Bytes))))
      let stamped ← liftM (IO.mkRef ([] : List Bytes) : IO (IO.Ref (List Bytes)))
      let lastStamp ← liftM (IO.mkRef 0 : IO (IO.Ref Nat))
      let restamp (send : Nat × Bytes) : M (Nat × Bytes) := do
        if !official then return send
        if hooks.timestamp.isSome then return send
        if (← liftM (stamped.get : IO (List Bytes))).contains send.2 then return send
        let some (_, body) := (← liftM (bodies.get : IO (List (Bytes × Bytes)))).find? (·.1 == send.2) | return send
        -- The contact's per-session preparation (its first send's curve work: tens of seconds
        -- without TLS_WORKER_HINTED) runs BEFORE the stamp, so that the stamp is taken just
        -- before the message is sealed and sent, as an official client's is. Once prepared, this
        -- costs one exchange; a contact with a device list is prepared by its own send.
        if (← kindsOf send.1) == [0] then
          let _ ← rpc.call .contactsPrepare (uint 16 send.1)
        let now := max (← agreedNow) ((← liftM (lastStamp.get : IO Nat)) + 1)
        liftM (lastStamp.set now : IO Unit)
        let some (_, built) := PrivateTextNotification.buildPublicOfficial 4 (toBits body) (toBits (uint 8 now)) | throw "message text rejected"
        insist (built.length == send.2.length) "a new timestamp changed the message's size class"
        liftM (stamped.modify (fun list => toBytes built :: list) : IO Unit)
        pure (send.1, toBytes built)
      -- A private request as far as the controllers know it (SIGNAL_RECORD): the frame with its
      -- private slots (recipient, access key, device and registration ids) still zero. The
      -- worker fills them in the engines and seals the record.
      let recordSend (kind : String) (contact id timestamp : Nat) (frame : List (BitVec 8)) : M Unit := do
        liftM (recordEvent kind [("connection", toJson (← liftM (current.get : IO Nat))), ("contact", toJson (toString contact)),
          ("request_id", toJson (toString id)), ("timestamp", toJson timestamp), ("frame_bytes", toJson frame.length),
          ("template_hex", toJson (TlsWorkerProcess.hex (toBytes frame)))] : IO Unit)
      -- One send to a contact with a device list (MULTI_DEVICE.md, section 5): the engines
      -- produce one envelope per device, all for the same built text; the state is stored
      -- before anything leaves, as for one device; then one request carries all of them.
      let sendDevices (send : Nat × Bytes) (id : Nat) : M Unit := do
        let some (address, _) := self | throw "no account address for a device list"
        let sealed ← rpc.call .devicesSend (uint 16 send.1 ++ address ++ send.2)
        insist (sealed.length ≥ 10) "invalid sealed envelopes reply"
        storeAdvanced send.1
        let timestamp := number (sealed.take 8)
        let count := (← kindsOf send.1).length
        let mut rest := sealed.drop 8
        let mut envelopes : List (List (BitVec 8)) := []
        for _ in [0:count] do
          let length := number (rest.take 2)
          insist (0 < length && length + 2 ≤ rest.length) "invalid sealed envelope length"
          envelopes := envelopes ++ [toBits ((rest.drop 2).take length)]
          rest := rest.drop (2 + length)
        insist rest.isEmpty "invalid sealed envelopes reply"
        let random ← rpc.call .publicRandom []
        insist (random.length == 32) "invalid joint randomness"
        let (frame, payloadAt, offsets) ← liftResult (PublicRequest.buildDevices envelopes timestamp id (toBits (random.take 4)) official)
        -- Both request kernels seal one TLS record (about five unanswered devices; section 5).
        insist (frame.length ≤ 16384) "a send to this many devices does not fit one record"
        recordSend "sent-private" send.1 id timestamp frame
        let handle ← rpc.call .devicesRequest (uint 16 send.1 ++ uint 2 payloadAt ++ uint 2 (offsets.getD 0 0) ++ uint 2 (offsets.getD 1 0) ++
          [UInt8.ofNat count] ++ (offsets.drop 2).flatMap (uint 2) ++ random.take 4 ++ toBytes frame)
        insist (handle.length == 8 && number handle != 0) "invalid request handle"
        TlsApplication.send (← appNow) ⟨number handle⟩ frame.length
      let sendMessage (send : Nat × Bytes) (id : Nat) : M Unit := do
        let send ← restamp send
        liftM (lastSent.set (some send) : IO Unit)
        if (← kindsOf send.1) != [0] then return ← sendDevices send id
        let sealed ← rpc.call .contactSend (uint 16 send.1 ++ send.2)
        insist (sealed.length ≥ 10) "invalid sealed envelope reply"
        storeAdvanced send.1
        let timestamp := number (sealed.take 8)
        let length := number ((sealed.drop 8).take 2)
        insist (0 < length && length ≤ sealed.length - 10) "invalid sealed envelope length"
        let random ← rpc.call .publicRandom []
        insist (random.length == 32) "invalid joint randomness"
        let (frame, offsets) ← liftResult (PublicRequest.build (toBits ((sealed.drop 10).take length)) timestamp id (toBits (random.take 4)) official)
        recordSend "sent-private" send.1 id timestamp frame
        let handle ← rpc.call .contactRequest (uint 16 send.1 ++ offsets.flatMap (uint 2) ++ random.take 4 ++ toBytes frame)
        insist (handle.length == 8 && number handle != 0) "invalid request handle"
        TlsApplication.send (← appNow) ⟨number handle⟩ frame.length
      /- ---- A contact whose device list changed (MULTI_DEVICE.md, sections 3 and 5). ----
      The server answers a send 409 (devices missing or extra) or 410 (stale registration
      ids). Its body lists device ids and is not read. Instead every session of the contact is
      replaced: fetch all its devices' prekey bundles, establish a session per device in the
      engines, store the new device list, send the message again. -/
      -- Wait for the pending response; records are read and answered as in the main loop.
      let rec awaitReply (fuel : Nat) (s : PublicReceive.State) : M PublicReceive.State := do
        match fuel with
        | 0 => throw "receive budget exhausted"
        | fuel+1 =>
          match ← TlsApplication.receive (← appNow) with
          | .application handle =>
            let (s, complete) ← record handle.id s
            let (s, frames) ← liftResult (PublicReceive.replies s (← controlMasks rpc s))
            for (kind, frame) in frames do
              sendPublic (toBytes frame)
              insist (kind != 8) "WebSocket peer closed before completion"
            for request in s.requests do
              let random ← rpc.call .publicRandom []
              insist (random.length == 32) "invalid joint randomness"
              let (frame, message) ← liftResult (PublicReceive.reply request (toBits (random.take 4)))
              unless message do sendPublic (toBytes frame)
            let s := { s with requests := [] }
            if complete then return s
            awaitReply fuel s
          | .control => awaitReply fuel s
          | .closed => throw "TLS closed before a response"
      -- Request ids of the refresh's own requests, apart from the sends' counter from 2^63.
      let extraIds ← liftM (IO.mkRef 0 : IO (IO.Ref Nat))
      let nextId : M Nat := liftM (extraIds.modifyGet (fun n => (2 ^ 63 + 2 ^ 32 + n, n + 1)) : IO Nat)
      -- A clock both controllers use: each reads its own, they tell each other, the later one
      -- counts if the two are within two minutes (`Clock.agreed_within`), as for `agreedNow`.
      let agreedClock : M Nat := do
        let mine := (← liftM (Std.Time.Timestamp.now : IO Std.Time.Timestamp)).toMillisecondsSinceUnixEpoch.val.toNat
        liftResult (Node.Policy.Clock.agree mine (number (← swap (uint 8 mine))))
      -- The server drops a socket that is silent for 90 seconds, and establishing one device's
      -- session takes about that long. Before each step: if 20 seconds have passed on the agreed
      -- clock since the last exchange, a keepalive is sent and its answer awaited.
      let quiet ← liftM (IO.mkRef 0 : IO (IO.Ref Nat))
      let touch : M Unit := do
        let now ← agreedClock
        liftM (quiet.set now : IO Unit)
      let keepAlive (s : PublicReceive.State) : M PublicReceive.State := do
        let now ← agreedClock
        if now < (← liftM (quiet.get : IO Nat)) + 20000 then return s
        let id ← nextId
        let random ← rpc.call .publicRandom []
        insist (random.length == 32) "invalid joint randomness"
        sendPublic (toBytes (← liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
        liftM (quiet.set now : IO Unit)   -- the time it was sent: reading its answer may itself take long
        let s ← awaitReply 64 (PublicReceive.expect s id)
        insist (s.status == 200) "keepalive was refused"
        pure s
      let refreshContact (contact : Nat) (start : PublicReceive.State) : M PublicReceive.State := do
        let some (_, registration) := self | throw "no account for a device refresh"
        insist (0 < registration && registration < 2 ^ 32) "the export has no registration id for the account"
        -- The fetch names the contact: its UUID and access key are inserted by the engines.
        let fetchId ← nextId
        let random ← rpc.call .publicRandom []
        insist (random.length == 32) "invalid joint randomness"
        let (frame, payloadAt, offsets) ← liftResult (PublicRequest.buildFetch fetchId (toBits (random.take 4)))
        recordSend "sent-private-prekey-fetch" contact fetchId 0 frame
        let handle ← rpc.call .bundleFetch (uint 16 contact ++ uint 2 payloadAt ++ uint 2 (offsets.getD 0 0) ++ uint 2 (offsets.getD 1 0) ++
          random.take 4 ++ toBytes frame)
        insist (handle.length == 8 && number handle != 0) "invalid request handle"
        TlsApplication.send (← appNow) ⟨number handle⟩ frame.length
        touch
        -- Its body is collected unrevealed (`PublicReceive.step`: only a 200 with this id).
        let fetched ← awaitReply 64 { PublicReceive.expect start fetchId with fetch := some fetchId, bundle := none }
        let mut s := { fetched with fetch := none }
        -- 404: the account is gone; 401: the access key no longer matches. Neither is retried.
        insist (s.status == 200) s!"the prekey fetch was answered {s.status}"
        let some size := s.bundle | throw "prekey response without a body"
        insist (2540 ≤ size && size ≤ 65536) "prekey response size"
        s ← keepAlive s
        -- The one thing opened about the body: which of its bytes are JSON punctuation.
        let flags ← rpc.call .bundleShape []
        insist (flags.length == size && flags.all (fun b => b == 0 || b == 255)) "invalid bundle shape"
        -- In the clear, by both controllers: the devices' layout, if the flags are exactly a response's.
        let some widths := BundleResponse.layout? (flags.map (· == 255)) | throw "prekey response layout refused"
        let rows := (BundleResponse.starts BundleResponse.firstItem widths).zip widths
        insist (1 ≤ rows.length && rows.length ≤ 6) "device count"
        let slots := config.agreed.bundleSlots
        for ((at_, w), index) in rows.zipIdx do
          for step in [0:9] do
            s ← keepAlive s
            let out ← rpc.call .bundleEstablish (uint 16 contact ++ uint 8 (2 ^ 63) ++ uint 4 registration ++
              [UInt8.ofNat index, UInt8.ofNat rows.length, UInt8.ofNat step] ++ uint 4 at_ ++ establishTail slots w)
            -- One status byte per device and not the reason: bad JSON, a bad signature, a changed
            -- identity key and a failed encapsulation look the same. The contact keeps its old state.
            -- (254 after the first step: the bundle's identity key is a new one, which is accepted.)
            insist (out == [255] || (out == [254] && index == 0 && step == 0)) "a device's session could not be established"
        liftM (IO.eprintln s!"device refresh: {rows.length} sessions established" : IO Unit)
        -- The new device list is stored, and only then becomes the contact's state (`commitScratch`).
        insist (← commitScratch contact (widths.map (fun w => if w.oneTime == 0 then 1 else 2)))
          "the database did not acknowledge a contact's new device list"
        keepAlive s
      -- Contact state at rest (TEST: the two fixture contacts have ids 1 and 2, and each
      -- controller's key share is local randomness standing in for what the database
      -- nodes would deliver). After one send to each contact the state is sealed,
      -- evicted and reloaded from the ciphertext, so the remaining sends prove the
      -- round trip preserved it.
      -- Every seal under a contact's key uses a new version (the version is the cipher's nonce).
      let keyContacts : M Unit := do
        unless keyed do
          for (contact, share, _) in known do
            let _ ← Secret.inputOwn rpc .contactKey (Secret.hide (uint 16 contact) ++ share)
      let reloadContacts : M Unit := do
        for (contact, share, _) in known do
          let version ← nonce
          let stored ← sealState contact version
          insist (stored.length > 16) "invalid stored contact state"
          let _ ← rpc.call .contactEvict (uint 16 contact)
          let _ ← Secret.inputOwn rpc .contactKey (Secret.hide (uint 16 contact) ++ share)
          openState contact (version ++ stored)
        requireLoaded
      -- Before a contact's first send of the session: its per-session curve work (the table its
      -- messages' key agreements are summed from) together with that of the contacts that follow
      -- it, in one worker call whose field rounds they share: the latency of a few dozen rounds
      -- once per batch instead of per contact. Only with the workers' constant-depth programs
      -- (TLS_WORKER_HINTED=1); without them each contact is prepared by its own first send, as
      -- before. An optimisation, never a decision: a contact the call does not prepare (status
      -- other than 255: its key is refused, or it is not loaded) is prepared or refused by its
      -- own send, with that path's per-contact outcome. The contact's state is still stored
      -- before each of its sends; nothing here changes it.
      -- SIGNAL_PREPARE_BATCH: contacts per call (default 32, at most 64; 0: never).
      let preparedContacts ← liftM (IO.mkRef ([] : List Nat) : IO (IO.Ref (List Nat)))
      let ensurePrepared (contact : Nat) (upcoming : List Nat) : M Unit := do
        if !config.agreed.hinted then return
        let size := config.agreed.prepareBatch
        let done ← liftM (preparedContacts.get : IO (List Nat))
        if size == 0 || done.contains contact then return
        let batch := ((contact :: upcoming).eraseDups.filter (fun c => !done.contains c)).take size
        let statuses ← rpc.call .contactsPrepare (batch.flatMap (uint 16))
        insist (statuses.length == batch.length) "invalid contacts-prepare reply"
        liftM (preparedContacts.modify (· ++ batch) : IO Unit)
      /- ---- The long-lived session (`serve` below): one job's contacts. ----
      As the daemon's one-notify session does at its start, for the ids of the job's signed request:
      read them from the database nodes under that request (which also authorises the write-backs),
      compare with the other party what the nodes do not hold or do not serve yet (that id's result,
      `absent`), and load the rest. A contact the engines still hold from an earlier job is kept,
      with its per-session preparation, when the nodes' version of its state is the version this
      session holds (`versions`): the engines then hold what was stored under that version, or are
      at most one unacknowledged store ahead of it (a counter gap, never a key used twice).
      Otherwise (another version, or not held) it is evicted and loaded from the nodes' blob.
      Returns the job's contacts in the request's order. -/
      let residentIds ← liftM (IO.mkRef ([] : List Nat) : IO (IO.Ref (List Nat)))
      let forget (contact : Nat) : M Unit := do
        if (← liftM (residentIds.get : IO (List Nat))).contains contact then
          let _ ← rpc.call .contactEvict (uint 16 contact)
        liftM (residentIds.modify (·.filter (· != contact)) : IO Unit)
        liftM (preparedContacts.modify (·.filter (· != contact)) : IO Unit)
        liftM (deviceKinds.modify (·.filter (·.1 != contact)) : IO Unit)
      let setVersion (contact version : Nat) : M Unit :=
        liftM (versions.modify (fun all => all.filter (·.1 != contact) ++ [(contact, version)]) : IO Unit)
      let loadJob (requestPath text : String) : M (List Nat) := do
        let request ← liftResult (Lean.Json.parse (← liftM (IO.FS.readFile requestPath : IO String)))
        let ids := ((request.getObjValAs? (Array String) "ids").toOption.getD #[]).toList.filterMap String.toNat?
        insist (!ids.isEmpty) "the notify request lists no ids"
        let signedFor ← liftResult (fromHex ((request.getObjValAs? String "message_hash").toOption.getD ""))
        insist (signedFor == TlsWire.hash text.toUTF8.data.toList) "the message is not the one the notify request was signed for"
        -- TEST: an id of the export that the database nodes do not hold yet is created from it.
        let records ← match exportPath with
          | some path => do pure (← liftResult (readExport (← liftM (IO.FS.readFile path : IO String)))).2.2
          | none => pure []
        let wanted := ids.map (fun id => (id, (records.find? (·.1 == id)).map (·.2)))
        let (readJson, sharesJson) ← dbRead ["--request", requestPath] "contacts"
        let waiting := ((readJson.getObjValAs? (Array String) "not_yet_readable").toOption.getD #[]).toList
        let gone := wanted.filterMap (fun (contact, record) =>
          if waiting.contains (toString contact) then some (contact, true)
          else if record.isNone && ((dbShare sharesJson contact).isNone || (dbBlob readJson contact).isNone) then some (contact, false)
          else none)
        let mine := TlsWire.hash (gone.flatMap (fun (contact, later) => uint 16 contact ++ [(if later then 1 else 0 : UInt8)]))
        insist ((← swap mine) == mine) "the two parties' database reads differ"
        liftM (absent.set gone : IO Unit)
        liftM (unreadable.set [] : IO Unit)
        let mut loaded : List Nat := []
        for (contact, record) in wanted do
          if let some (_, later) := gone.find? (·.1 == contact) then
            -- Not on the nodes (deleted, or never signed up): nothing of it stays in the engines.
            -- Not served yet: it is not touched.
            if !later then forget contact
            continue
          match dbShare sharesJson contact, dbBlob readJson contact with
          | some share, some (version, blob) =>
            let held := (← liftM (residentIds.get : IO (List Nat))).contains contact
            unless held && (← versionOf contact) == version do
              forget contact
              let _ ← Secret.inputOwn rpc .contactKey (Secret.hide (uint 16 contact) ++ share)
              openState contact (← liftResult (fromHex blob))
              setVersion contact version
              -- (A blob that does not open leaves the contact unloaded: `unreadable`, its result.)
              unless (← liftM (unreadable.get : IO (List Nat))).contains contact do
                liftM (residentIds.modify (· ++ [contact]) : IO Unit)
          | _, _ =>
            let some record := record | throw "contact is not in the database"
            forget contact
            let some share ← dbDeal contact s!"{← dbEnv "SIGNAL_DB_TOKENS"}/{contact}.json" | throw "dealing a contact key failed"
            let _ ← Secret.inputOwn rpc .contactAdmit (Secret.hide (uint 16 contact) ++ record)
            let _ ← Secret.inputOwn rpc .contactKey (Secret.hide (uint 16 contact) ++ share)
            setVersion contact 0
            liftM (residentIds.modify (· ++ [contact]) : IO Unit)
          loaded := loaded ++ [contact]
        pure loaded
      -- After the sends: every contact's advanced state goes back to the store.
      let writeBack : M Unit := do
        if dbClient.isSome then pure ()   -- stored before each send (storeAdvanced)
        else
        match storeDirectory with
        | none => pure ()
        | some directory =>
          for (contact, share, _) in known do
            let version ← nonce
            let stored ← sealState contact version
            insist (stored.length > 16) "invalid stored contact state"
            inBand (Channels.saveShare ((directory : System.FilePath) / toString contact) share (version ++ stored))
      -- The application's request: `notify(ids, message)`. Ids and text are public to both
      -- parties; it expands to one send per contact. The text is 1..256 bytes of UTF-8. What
      -- goes to the engines is the built message of its size class c in 1..4: a validity byte,
      -- a kind byte, 80c bytes of padded content (Content, 0x80, zeros: Signal's padding in
      -- 80-byte blocks) and the 8-byte timestamp. The envelope's size depends on c alone, so
      -- its observer learns c: the Content's length rounded up to 80 bytes (with today's
      -- timestamps, text of 1..68, 69..146, 147..226 or 227..256 bytes), not the exact length.
      let notify(ids : List Nat) (message : String) (timestamp : Nat) : M (List (Nat × Bytes)) := do
        let body := message.toUTF8.data.toList
        insist (0 < body.length && body.length ≤ 256) "notify message must be 1..256 bytes"
        insist (ids.all (· < 2 ^ 128)) "contact ids are u128"
        -- The text is public, so the message content (protobuf, padding) is built here
        -- with the same definition the private path compiles to a circuit
        -- (`PrivateTextNotification.buildPublic`: the smallest of the four size classes that
        -- holds the content; texts of at most 48 bytes get exactly what `build` gave them).
        ids.zipIdx.mapM (fun (contact, index) => do
          -- (libsignal profile: the official padding, 80c − 1 bytes, `buildPublicOfficial`.)
          let (classes, built) := ((if official then PrivateTextNotification.buildPublicOfficial else PrivateTextNotification.buildPublic)
            4 (toBits body) (toBits (uint 8 (timestamp + index)))).getD (0, [])
          insist (1 ≤ classes && classes ≤ 4 && built.length == (if official then 9 else 10) + 80 * classes && built.head? == some 255) "message text rejected"
          if official then liftM (bodies.modify (fun list => (toBytes built, body) :: list) : IO Unit)
          pure (contact, toBytes built))
      let inputs ← match exportPath with
        | none => do
          -- TEST: the fixture recipient compares each envelope with pre-computed ciphertext
          -- for these exact texts and timestamps, so each call names one contact here.
          pure ((← notify [1] "Hello, Signal! ☕" 0x1ba60d33800) ++ (← notify [2] "你好，世界" 0x1ba60d33801)
            ++ (← notify [1] "Second private notification" 0x1ba60d33802) ++ (← notify [2] "Delivery ready 😀" 0x1ba60d33803))
        | some _ => do
          -- Two broadcasts to every contact. The timestamp is public and must be the same
          -- for both controllers, so the harness supplies it.
          let base ← agreedNow
          -- Through the daemon: the application's one message, to the requested ids the database holds.
          if let some file := notifyFile then
            let text ← liftM (IO.FS.readFile file : IO String)
            notify contacts text base
          else
          -- Further broadcasts on request (SIGNAL_LOCAL_BROADCASTS, for measuring the cost per message).
          let count := hooks.broadcasts
          let more ← ((List.range (count - 2)).mapM (fun k => notify contacts
            -- the third broadcast is 200 bytes long (a larger size class)
            (if k == 0 then "MPC broadcast 3 " ++ String.ofList (List.replicate 184 'x') else s!"MPC broadcast {k + 3}") (base + 1000 * (k + 2))))
          pure ((← notify contacts "MPC broadcast one" base) ++ (← notify contacts "MPC broadcast two ☕" (base + 1000)) ++ more.flatten)
      /- ---- Several circuits (SIGNAL_TOR_CIRCUITS = N ≥ 2, a send session). Connections 1..N-1
      are opened before the first send, each with its own handshake, TLS session (`apps`) and
      unauthenticated WebSocket, whose 101 is read at once. Per connection the controller keeps
      the response parser's state and the request-id counter (`parkedStates`, `counters`); the
      worker keeps its TLS and WebSocket state. Established up front rather than lazily: the
      handshakes then cost nothing on the way to a send, and a proxy or circuit that does not
      work fails the session before any contact's state has advanced. -/
      let sendCircuits := if authenticated then 0 else circuits
      let recipients := inputs.map (·.1)
      let parkedStates ← liftM (IO.mkRef (#[] : Array PublicReceive.State) : IO (IO.Ref (Array PublicReceive.State)))
      let counters ← liftM (IO.mkRef (Array.replicate (max sendCircuits 1) 0) : IO (IO.Ref (Array Nat)))
      let openCircuits : M Unit := do
        -- parkedStates[i]: connection i's state while another is in use (0's is the loop's until then).
        liftM (parkedStates.set #[PublicReceive.start []] : IO Unit)
        for index in [1:sendCircuits] do
          let on := TlsWorker.onConnection rpc active index
          TlsWorker.connectVia on endpoint (← liftM (natural port)) (proxyFor (some index))
          let handshake ← TlsClient.run (TlsWorker.backend on) (TlsWorker.transport on) tlsConfig
          insist (handshake.serverCertificateVerified && handshake.serverFinishedVerified) "handshake not accepted after retirement"
          let waitingFor ← liftM (IO.mkRef (none : Option Bytes) : IO (IO.Ref (Option Bytes)))
          let session ← liftM (TlsWorker.applicationSession on handshake (some (TlsWorker.waitingTransport on waitingFor)))
          let sendOn (bytes : Bytes) : M Unit := do
            let handle ← on.call .publicBuffer bytes
            insist (handle.length == 8 && number handle != 0) "invalid public buffer handle"
            TlsApplication.send session ⟨number handle⟩ bytes.length
          let upgrade ← on.call .publicUpgrade []
          insist (upgrade.length == 44) "invalid public upgrade receipt"
          sendOn (toBytes (anonymousUpgrade (toBits (upgrade.take 16))))
          let mut s : PublicReceive.State := { PublicReceive.start (toBits (upgrade.drop 16)) with lenient := exportPath.isSome }
          let mut fuel := 64
          while !s.upgraded do
            insist (fuel > 0) "receive budget exhausted"
            fuel := fuel - 1
            match ← TlsApplication.receive session with
            | .application handle =>
              let (next, complete) ← record handle.id s
              insist (!complete && next.requests.isEmpty) "unexpected server traffic during the upgrade"
              let (next, frames) ← liftResult (PublicReceive.replies next (← controlMasks on next))
              for (kind, frame) in frames do
                sendOn (toBytes frame)
                insist (kind != 8) "WebSocket peer closed before completion"
              s := next
            | .control => pure ()
            | .closed => throw "TLS closed before the upgrade"
          liftM (apps.modify (·.push session) : IO Unit)
          liftM (parkedStates.modify (·.push s) : IO Unit)
      -- Before each send: move to the contact's connection. Returns that connection's parser
      -- state and the send's request id (2^63 + the sends so far on that connection). One
      -- connection (N ≤ 1): the state and id the loop gave, exactly as without Tor.
      let toCircuit (s : PublicReceive.State) (contact id : Nat) : M (PublicReceive.State × Nat) := do
        let target := Circuits.assign recipients (max sendCircuits 1) contact
        liftM (circuitSends.modify (· ++ [(contact, target)]) : IO Unit)
        if sendCircuits ≤ 1 then return (s, id)
        let here ← liftM (current.get : IO Nat)
        let sent := (← liftM (counters.get : IO (Array Nat))).getD target 0
        liftM (counters.modify (·.set! target (sent + 1)) : IO Unit)
        if target == here then return (s, 2 ^ 63 + sent)
        -- The connection in use parks its state; the target's is taken up.
        liftM (parkedStates.modify (·.set! here s) : IO Unit)
        liftM (current.set target : IO Unit)
        return ((← liftM (parkedStates.get : IO (Array PublicReceive.State))).getD target s, 2 ^ 63 + sent)
      let rec loop (fuel : Nat) (s : PublicReceive.State) (inputs : List (Nat × Bytes)) (completed : Nat) : M Nat := do
        match fuel with
        | 0 => throw "receive budget exhausted"
        | fuel+1 =>
          match ← TlsApplication.receive (← appNow) with
          | .application handle =>
            let wasPending := s.pending
            let (s, complete) ← record handle.id s
            -- The mask is public but must be the same for both controllers: joint randomness.
            let (s, frames) ← liftResult (PublicReceive.replies s (← controlMasks rpc s))
            for (kind, frame) in frames do
              sendPublic (toBytes frame)
              insist (kind != 8) "WebSocket peer closed before completion"
            -- Replies to completed server requests (each with its own joint mask).
            for request in s.requests do
              let random ← rpc.call .publicRandom []
              insist (random.length == 32) "invalid joint randomness"
              let (frame, message) ← liftResult (PublicReceive.reply request (toBits (random.take 4)))
              -- Nothing is received on this socket: a delivered message is left unacknowledged.
              unless message do sendPublic (toBytes frame)
            let s := { s with requests := [] }
            insist (!complete || wasPending) "unsolicited service response"
            -- A send refused for the contact's device list (409, 410): the contact's sessions are
            -- replaced and the message is sent again. Bounded: one refresh and one resend per
            -- message; a second refusal ends the session.
            let s ← if complete && s.lenient && (s.status == 409 || s.status == 410) then do
                let some input ← liftM (lastSent.get : IO (Option (Nat × Bytes))) | throw "no send to repeat"
                let refreshed ← refreshContact input.1 s
                let id ← nextId
                sendMessage input id
                let answered ← awaitReply 64 (PublicReceive.expect refreshed id)
                insist (200 ≤ answered.status && answered.status < 300) s!"the resend after a device refresh was answered {answered.status}"
                pure answered
              else do
                -- (Without `lenient` the parser has already refused anything but a success.)
                insist (!complete || !s.lenient || (200 ≤ s.status && s.status < 300)) s!"service response was not a success: {s.status}"
                pure s
            let finished := completed + (if complete then 1 else 0)
            -- (No KeyUpdate of our own under the libsignal profile: BoringSSL never sends one.)
            if complete && finished == 1 && !official then TlsApplication.keyUpdate (← appNow) false
            if s.upgraded && !s.pending then
              match inputs with
              | [] => insist (finished > 0) "private provider supplied no requests"; return finished
              | input::tail =>
                -- Request ids are public: a counter from 2^63, as the service expects.
                let id := 2 ^ 63 + finished
                if finished == 0 then keyContacts
                if finished == 2 then reloadContacts
                if finished == 2 then liftM (preparedContacts.set [] : IO Unit)   -- reloaded contacts are unprepared
                ensurePrepared input.1 (tail.map (·.1))
                -- Several circuits: the contact's connection, its parser state and request id.
                let (s, id) ← toCircuit s input.1 id
                sendMessage input id
                loop fuel (PublicReceive.expect s id) tail finished
            else loop fuel s inputs finished
          | .control => loop fuel s inputs completed
          | .closed => throw "TLS closed before private responses"
      /- ---- Recovery: a send session with the database nodes (`Recovery`, above `main`). ----
      Instead of `loop`: every input ends in a per-id result and the session carries on. The
      session still ends on what is the session's own failure: an engine or worker rejection, a
      disagreement between the parties, a TLS record that does not authenticate, a handshake
      that fails. `SIGNAL_RECOVERY=0` runs `loop` as before.

      What makes a resend safe: a contact's state is stored on the database nodes before its
      message leaves (`storeSoft`), so sending the same text again always uses the next keys.
      A resend can therefore duplicate a message, never reuse a key. -/
      let recovery := exportPath.isSome && !authenticated && dbClient.isSome && config.agreed.recovery
      let note (event : String) : M Unit := do
        liftM (recoveryLog.modify (· ++ [event]) : IO Unit)
        liftM (IO.eprintln s!"recovery: {event}" : IO Unit)
        liftM (recordEvent "recovery" [("note", toJson event)] : IO Unit)
      -- Per connection: the slot its transport takes the next record from (connection 0's is `kept`).
      let slots ← liftM (IO.mkRef #[kept] : IO (IO.Ref (Array (IO.Ref (Option Bytes)))))
      let states ← liftM (IO.mkRef (#[] : Array PublicReceive.State) : IO (IO.Ref (Array PublicReceive.State)))
      -- The 101 to a connection's upgrade request.
      let readUpgrade (session : TlsApplication.Session TlsWorker.BufferHandle) (on : TlsWorker.Rpc)
          (expected : List (BitVec 8)) : M PublicReceive.State := do
        let mut s : PublicReceive.State := { PublicReceive.start expected with lenient := true }
        let mut fuel := 64
        while !s.upgraded do
          insist (fuel > 0) "receive budget exhausted"
          fuel := fuel - 1
          match ← TlsApplication.receive session with
          | .application handle =>
            let (next, complete) ← record handle.id s
            insist (!complete && next.requests.isEmpty) "unexpected server traffic during the upgrade"
            let (next, frames) ← liftResult (PublicReceive.replies next (← controlMasks on next))
            for (kind, frame) in frames do
              let handle ← on.call .publicBuffer (toBytes frame)
              insist (handle.length == 8 && number handle != 0) "invalid public buffer handle"
              TlsApplication.send session ⟨number handle⟩ frame.length
              insist (kind != 8) "WebSocket peer closed before completion"
            s := next
          | .control => pure ()
          | .closed => throw "TLS closed before the upgrade"
        return s
      -- Connection `index` from nothing: connect (through the proxy, with that connection's
      -- credentials), handshake, unauthenticated WebSocket and its 101. A failure here is the
      -- session's. Returns the connection's parser state.
      let openConnection (index : Nat) : M PublicReceive.State := do
        let on := TlsWorker.onConnection rpc active index
        TlsWorker.connectVia on endpoint (← liftM (natural port)) (proxyFor (some index))
        let handshake ← TlsClient.run (TlsWorker.backend on) (TlsWorker.transport on) tlsConfig
        insist (handshake.serverCertificateVerified && handshake.serverFinishedVerified) "handshake not accepted after retirement"
        let slot ← liftM (IO.mkRef (none : Option Bytes) : IO (IO.Ref (Option Bytes)))
        let session ← liftM (TlsWorker.applicationSession on handshake (some (TlsWorker.waitingTransport on slot)))
        let upgrade ← on.call .publicUpgrade []
        insist (upgrade.length == 44) "invalid public upgrade receipt"
        let request := toBytes (anonymousUpgrade (toBits (upgrade.take 16)))
        let handle ← on.call .publicBuffer request
        insist (handle.length == 8 && number handle != 0) "invalid public buffer handle"
        TlsApplication.send session ⟨number handle⟩ request.length
        liftM (apps.modify (fun all => if index < all.size then all.set! index session else all.push session) : IO Unit)
        liftM (slots.modify (fun all => if index < all.size then all.set! index slot else all.push slot) : IO Unit)
        readUpgrade session on (toBits (upgrade.drop 16))
      -- The next record of the connection in use, or `none`: the worker reported that the server
      -- or the proxy closed the connection (`pollRecord` replies `[0]`; both parties see it at the
      -- same request). The worker and the other connections are unaffected.
      let receiveSoft : M (Option (TlsApplication.Received TlsWorker.BufferHandle)) := do
        let index ← liftM (current.get : IO Nat)
        let on := TlsWorker.onConnection rpc active index
        let slot := (← liftM (slots.get : IO (Array (IO.Ref (Option Bytes))))).getD index kept
        if (← liftM (slot.get : IO (Option Bytes))).isNone then
          let deadline := (← liftM (IO.monoMsNow : IO Nat)) + 30000
          let mut waitingFor := true
          while waitingFor do
            insist ((← liftM (IO.monoMsNow : IO Nat)) < deadline) "no record from the server within 30 seconds"
            let wire ← on.call .pollRecord []
            if wire == [0] then return none
            if wire.isEmpty then liftM (IO.sleep 10)
            else
              liftM (slot.set (some wire) : IO Unit)
              waitingFor := false
        match ← TlsApplication.receive (← appNow) with
        | .closed =>
          -- close_notify: the connection itself goes next.
          for _ in [0:1000] do
            let wire ← on.call .pollRecord []
            if wire == [0] then return none
            insist wire.isEmpty "a record after close_notify"
            liftM (IO.sleep 10)
          throw "the server closed TLS but kept the connection open"
        | other => return some other
      -- Wait for the pending response on the connection in use. `false`: the connection was
      -- closed first (whatever was in flight on it is unanswered).
      let rec awaitSoft (fuel : Nat) (s : PublicReceive.State) : M (PublicReceive.State × Bool) := do
        match fuel with
        | 0 => throw "receive budget exhausted"
        | fuel+1 =>
          match ← receiveSoft with
          | none => return (s, false)
          | some (.application handle) =>
            let (s, complete) ← record handle.id s
            let (s, frames) ← liftResult (PublicReceive.replies s (← controlMasks rpc s))
            -- A close frame from the server is answered; the closed connection is then reported by the worker.
            for (_, frame) in frames do sendPublic (toBytes frame)
            for request in s.requests do
              let random ← rpc.call .publicRandom []
              insist (random.length == 32) "invalid joint randomness"
              let (frame, message) ← liftResult (PublicReceive.reply request (toBits (random.take 4)))
              unless message do sendPublic (toBytes frame)
            let s := { s with requests := [] }
            if complete then return (s, true)
            awaitSoft fuel s
          | some .control => awaitSoft fuel s
          | some .closed => return (s, false)
      -- Replace the connection in use after it was reported closed: a new handshake and upgrade
      -- on the same index (and the same proxy credentials); the other connections are kept.
      let reconnect : M Unit := do
        let index ← liftM (current.get : IO Nat)
        TlsWorker.emptyReply rpc .bundleDrop []   -- a response body half collected on it
        TlsWorker.emptyReply (TlsWorker.onConnection rpc active index) .resetConnection []
        let opened ← openConnection index
        liftM (states.modify (·.set! index opened) : IO Unit)
        note s!"connection {index} was closed and replaced"
      let saveState (s : PublicReceive.State) : M Unit := do
        let index ← liftM (current.get : IO Nat)
        liftM (states.modify (·.set! index s) : IO Unit)
      -- `keepAlive` with a closed connection as an outcome (`false`).
      let keepAliveSoft (s : PublicReceive.State) : M (PublicReceive.State × Bool) := do
        let now ← agreedClock
        if now < (← liftM (quiet.get : IO Nat)) + 20000 then return (s, true)
        let id ← nextId
        let random ← rpc.call .publicRandom []
        insist (random.length == 32) "invalid joint randomness"
        sendPublic (toBytes (← liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
        liftM (quiet.set now : IO Unit)
        awaitSoft 64 (PublicReceive.expect s id)
      -- `refreshContact` with every failure as an outcome (`Recovery.Refreshed`). Nothing of the
      -- contact changes, in the engines or on the database nodes, unless it returns `ok`.
      let refreshSoft (contact : Nat) (start : PublicReceive.State) : M (PublicReceive.State × Recovery.Refreshed) := do
        let some (_, registration) := self | throw "no account for a device refresh"
        insist (0 < registration && registration < 2 ^ 32) "the export has no registration id for the account"
        let drop : M Unit := TlsWorker.emptyReply rpc .bundleDrop []
        drop
        let fetchId ← nextId
        let random ← rpc.call .publicRandom []
        insist (random.length == 32) "invalid joint randomness"
        let (frame, payloadAt, offsets) ← liftResult (PublicRequest.buildFetch fetchId (toBits (random.take 4)))
        recordSend "sent-private-prekey-fetch" contact fetchId 0 frame
        let handle ← rpc.call .bundleFetch (uint 16 contact ++ uint 2 payloadAt ++ uint 2 (offsets.getD 0 0) ++ uint 2 (offsets.getD 1 0) ++
          random.take 4 ++ toBytes frame)
        insist (handle.length == 8 && number handle != 0) "invalid request handle"
        TlsApplication.send (← appNow) ⟨number handle⟩ frame.length
        touch
        let (fetched, alive) ← awaitSoft 64 { PublicReceive.expect start fetchId with fetch := some fetchId, bundle := none }
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
        let (next, alive) ← keepAliveSoft s
        s := next
        if !alive then
          drop
          return (s, .lost)
        -- The one thing opened about the body: which of its bytes are JSON punctuation.
        let flags ← rpc.call .bundleShape []
        if flags.isEmpty then
          -- Strict mode, and the response's size class is not in the manifest (more devices than
          -- the deployment covers): this contact fails, the session goes on.
          drop
          return (s, .stop .fault s!"no circuit for a prekey response of {size} bytes (more devices than the deployment covers)")
        insist (flags.length == size && flags.all (fun b => b == 0 || b == 255)) "invalid bundle shape"
        let layout := BundleResponse.layout? (flags.map (· == 255))
        let widths := layout.getD []
        let rows := (BundleResponse.starts BundleResponse.firstItem widths).zip widths
        if layout.isNone || !(1 ≤ rows.length && rows.length ≤ 6) then
          drop
          return (s, .stop .fault "server fault: the prekey response is not a bundle")
        let mut changed := false
        let slots := config.agreed.bundleSlots
        for ((at_, w), index) in rows.zipIdx do
          for step in [0:9] do
            let (next, alive) ← keepAliveSoft s
            s := next
            if !alive then
              drop
              return (s, .lost)
            let out ← rpc.call .bundleEstablish (uint 16 contact ++ uint 8 (2 ^ 63) ++ uint 4 registration ++
              [UInt8.ofNat index, UInt8.ofNat rows.length, UInt8.ofNat step] ++ uint 4 at_ ++ establishTail slots w)
            -- 254 (first step, first device): the bundle parsed and verified under an identity key
            -- that is not the stored one. Accepted by decision; reported.
            if out == [254] && index == 0 && step == 0 then changed := true
            else if out != [255] then
              -- One status byte and not the reason: bad JSON, a bad signature, a failed
              -- agreement or encapsulation look the same. Nothing is stored.
              drop
              return (s, .stop .fault "server fault: a device's bundle did not verify")
        -- Stored on the database nodes, then (and only then) the contact's state.
        if !(← commitScratch contact (widths.map (fun w => if w.oneTime == 0 then 1 else 2))) then
          return (s, .stop .retryLater "the database nodes did not acknowledge the new device list")
        note s!"contact {contact}: {rows.length} sessions established{if changed then " under a new identity key" else ""}"
        -- TEST hook: a pause here lets the harness change the contact's devices again before the resend.
        if let some pause := hooks.pauseRefresh then
          liftM (IO.sleep (UInt32.ofNat pause) : IO Unit)
        return (s, .ok changed)
      -- `sendMessage` with the contact's failures as outcomes. `none`: the request left. Otherwise
      -- nothing was sent: the result, the reason, and whether to stop sending to this contact.
      let sendSoft (send : Nat × Bytes) (id : Nat) : M (Option (Recovery.Result × String × Bool)) := do
        let send ← restamp send
        let unacknowledged := (Recovery.Result.retryLater, "the database nodes did not acknowledge the contact's state", false)
        let refused := (Recovery.Result.fault, "the contact's stored state cannot produce a message", true)
        let kinds ← kindsOf send.1
        if kinds != [0] then
          let some (address, _) := self | throw "no account address for a device list"
          let sealed ← rpc.call .devicesSend (uint 16 send.1 ++ address ++ send.2)
          if sealed == [0] then return some refused
          insist (sealed.length ≥ 10) "invalid sealed envelopes reply"
          let timestamp := number (sealed.take 8)
          let mut rest := sealed.drop 8
          let mut envelopes : List (List (BitVec 8)) := []
          for _ in [0:kinds.length] do
            let length := number (rest.take 2)
            insist (0 < length && length + 2 ≤ rest.length) "invalid sealed envelope length"
            envelopes := envelopes ++ [toBits ((rest.drop 2).take length)]
            rest := rest.drop (2 + length)
          insist rest.isEmpty "invalid sealed envelopes reply"
          let random ← rpc.call .publicRandom []
          insist (random.length == 32) "invalid joint randomness"
          let (frame, payloadAt, offsets) ← liftResult (PublicRequest.buildDevices envelopes timestamp id (toBits (random.take 4)) official)
          -- Both request kernels seal one TLS record: about five unanswered devices (MULTI_DEVICE.md, section 5).
          if frame.length > 16384 then
            return some (.retryLater, s!"a message to {kinds.length} devices does not fit one request (not supported yet)", true)
          if !(← storeSoft send.1) then return some unacknowledged
          recordSend "sent-private" send.1 id timestamp frame
          let handle ← rpc.call .devicesRequest (uint 16 send.1 ++ uint 2 payloadAt ++ uint 2 (offsets.getD 0 0) ++ uint 2 (offsets.getD 1 0) ++
            [UInt8.ofNat kinds.length] ++ (offsets.drop 2).flatMap (uint 2) ++ random.take 4 ++ toBytes frame)
          insist (handle.length == 8 && number handle != 0) "invalid request handle"
          TlsApplication.send (← appNow) ⟨number handle⟩ frame.length
          return none
        let sealed ← rpc.call .contactSend (uint 16 send.1 ++ send.2)
        if sealed == [0] then return some refused
        insist (sealed.length ≥ 10) "invalid sealed envelope reply"
        let timestamp := number (sealed.take 8)
        let length := number ((sealed.drop 8).take 2)
        insist (0 < length && length ≤ sealed.length - 10) "invalid sealed envelope length"
        if !(← storeSoft send.1) then return some unacknowledged
        let random ← rpc.call .publicRandom []
        insist (random.length == 32) "invalid joint randomness"
        let (frame, offsets) ← liftResult (PublicRequest.build (toBits ((sealed.drop 10).take length)) timestamp id (toBits (random.take 4)) official)
        recordSend "sent-private" send.1 id timestamp frame
        let handle ← rpc.call .contactRequest (uint 16 send.1 ++ offsets.flatMap (uint 2) ++ random.take 4 ++ toBytes frame)
        insist (handle.length == 8 && number handle != 0) "invalid request handle"
        TlsApplication.send (← appNow) ⟨number handle⟩ frame.length
        return none
      -- Connection 0 is connected and its upgrade request sent; then connections 1..N-1.
      let openAll : M PublicReceive.State := do
        let first ← readUpgrade app (TlsWorker.onConnection rpc active 0) (toBits accept)
        liftM (states.set #[first] : IO Unit)
        for index in [1:max sendCircuits 1] do
          let opened ← openConnection index
          liftM (states.modify (·.push opened) : IO Unit)
        pure first
      -- One notify's sends (`inputs`, to the contacts `recipients`) on the open connections. Once
      -- per session, or once per job of the long-lived session (`serve`).
      let deliverJob (inputs : List (Nat × Bytes)) (recipients : List Nat) (notifyId journal : Option String)
          (first : PublicReceive.State) : M Nat := do
        liftM (recoveryUsed.set true : IO Unit)
        let count := max sendCircuits 1
        /- What an earlier session for the SAME notify settled (SIGNAL_NOTIFY_ID names the notify,
        SIGNAL_NOTIFY_JOURNAL is this party's journal). An entry counts only when both parties'
        journals have it: a party that lost its journal, or lies, can cause a duplicate, never
        a message left out. Entries are public values (message number, id, result). -/
        let settled ← match notifyId, journal with
          | some named, some path => do
            let text ← if ← liftM ((path : System.FilePath).pathExists : IO Bool) then liftM (IO.FS.readFile path : IO String) else pure ""
            let mine := Recovery.journalEntries named text
            let code (result : Recovery.Result) : Nat := (Recovery.Result.all.findIdx? (· == result)).getD 255
            let theirs ← swap (mine.flatMap (fun (message, contact, result) => uint 4 message ++ uint 16 contact ++ [UInt8.ofNat (code result)]))
            let both := mine.filter (fun (message, contact, result) =>
              (List.range (theirs.length / 21)).any (fun i =>
                (theirs.drop (21 * i)).take 21 == uint 4 message ++ uint 16 contact ++ [UInt8.ofNat (code result)]))
            if !mine.isEmpty then note s!"{both.length} results settled by an earlier session of this notify"
            pure both
          | _, _ => pure []
        let contactOf (index : Nat) : Nat := (inputs.getD index (0, [])).1
        -- The message's number within the notify, for its contact.
        let messageOf (index : Nat) : Nat := ((inputs.take index).filter (·.1 == contactOf index)).length
        let mut outcomes : Array (Option (Recovery.Result × String)) := Array.replicate inputs.length none
        -- Contacts no longer sent to in this session, with the result that stopped them. From the
        -- start: those whose stored state did not open under their key.
        let mut stopped : List (Nat × Recovery.Result × String) :=
          (← liftM (unreadable.get : IO (List Nat))).map (fun contact =>
            (contact, Recovery.Result.fault, "the contact's stored state does not open under its key"))
        -- Inputs during whose delivery the contact's sessions were replaced (and under a new identity key).
        let mut refreshedInputs : List Nat := []
        let mut changedInputs : List Nat := []
        -- The queue: (input, transient retries so far, not before this agreed time).
        let mut queue : List (Nat × Nat × Nat) := (List.range inputs.length).map (fun index => (index, 0, 0))
        let mut delivered := 0
        let mut rotated := false
        let mut rounds := 0
        -- TEST hook (SIGNAL_LOCAL_PAUSE_AFTER=K:MS): one pause once K inputs have a result, so that
        -- the harness can change something on the server in the middle of a session.
        let pauseAfter := hooks.pauseAfter
        let mut paused := false
        while !queue.isEmpty do
          rounds := rounds + 1
          insist (rounds ≤ 64 + 8 * inputs.length) "delivery budget exhausted"
          if let some (after, pause) := pauseAfter then
            if !paused && (outcomes.toList.filter Option.isSome).length ≥ after then
              paused := true
              note s!"TEST pause of {pause} ms after {after} results"
              liftM (IO.sleep (UInt32.ofNat pause) : IO Unit)
          let now ← agreedClock
          let (index, retries, _) ← match queue.find? (fun (_, _, notBefore) => notBefore ≤ now) with
            | some item => pure item
            | none => do
              -- Everything left is backing off: both controllers wait for the soonest.
              let soonest := (queue.map (·.2.2)).foldl min (now + Recovery.longestWait)
              liftM (IO.sleep (UInt32.ofNat (soonest - now)) : IO Unit)
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
            liftM (circuitSends.modify (· ++ [(contact, target)]) : IO Unit)
            liftM (current.set target : IO Unit)
            let sent := (← liftM (counters.get : IO (Array Nat))).getD target 0
            liftM (counters.modify (·.set! target (sent + 1)) : IO Unit)
            let id := 2 ^ 63 + sent
            let s := (← liftM (states.get : IO (Array PublicReceive.State))).getD target first
            ensurePrepared contact (queue.map (fun (later, _, _) => contactOf later))   -- with the contacts that follow, in the same field rounds
            match ← sendSoft input id with
            | some (result, reason, stop) =>
              final := some (result, reason)
              if stop && !result.stops then stopped := stopped ++ [(contact, result, reason)]
              break
            | none => pure ()
            let (s, alive) ← awaitSoft 64 (PublicReceive.expect s id)
            liftM (recordEvent "response" [("contact", toJson (toString contact)), ("message", toJson message),
              ("request_id", toJson (toString id)), ("answered", toJson alive), ("status", toJson s.status),
              ("retry_after", toJson s.retryAfter)] : IO Unit)
            if !alive then
              -- Sent, not answered: whether the server took it is unknown. It is sent again
              -- (under new keys), accepting a duplicate.
              reconnect
              lost := lost + 1
              if lost > Recovery.reconnects then final := some (.retryLater, s!"the connection was closed {lost} times")
              continue
            saveState s
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
                note s!"contact {contact}: send answered {s.status}, refresh {refreshes}"
                let (s, outcome) ← refreshSoft contact s
                match outcome with
                | .ok changed =>
                  saveState s
                  refreshedInputs := refreshedInputs ++ [index]
                  if changed then changedInputs := changedInputs ++ [index]
                | .lost =>
                  reconnect
                  refreshes := refreshes - 1
                  lost := lost + 1
                  if lost > Recovery.reconnects then final := some (.retryLater, s!"the connection was closed {lost} times")
                | .stop result reason =>
                  saveState s
                  final := some (result, reason)
                | .transient status retryAfter =>
                  saveState s
                  again := some (status, retryAfter)
          match final, again with
          | some (result, reason), _ =>
            outcomes := outcomes.set! index (some (result, reason))
            if !reason.isEmpty then note s!"contact {contact}, message {message}: {result.text} ({reason})"
            if result.stops then stopped := stopped ++ [(contact, result, reason)]
            if result.isDelivered then
              delivered := delivered + 1
              if !rotated then
                rotated := true
                -- (Not under the libsignal profile: BoringSSL never sends a KeyUpdate of its own.)
                unless official do TlsApplication.keyUpdate (← appNow) false
            if result.settled then
              match notifyId, journal with
              | some named, some path =>
                liftM (IO.FS.withFile (path : System.FilePath) .append (fun file => file.putStrLn (Recovery.journalLine named (message, contact, result, reason))) : IO Unit)
              | _, _ => pure ()
          | none, some (status, retryAfter) =>
            match Recovery.delay retries retryAfter with
            | some wait =>
              note s!"contact {contact}, message {message}: answered {status}, retry {retries + 1} in {wait} ms"
              queue := queue ++ [(index, retries + 1, (← agreedClock) + wait)]
            | none =>
              let reason := s!"answered {status}" ++ (match retryAfter with | some seconds => s!", Retry-After {seconds} s" | none => "") ++
                s!", after {retries} retries"
              note s!"contact {contact}, message {message}: retry later ({reason})"
              outcomes := outcomes.set! index (some (.retryLater, reason))
          | none, none => pure ()
        -- The per-id results. Both controllers computed them from agreed values: they compare a
        -- digest (through the worker's exchange) and report only what both arrived at.
        let entries : List Recovery.Entry := (List.range inputs.length).map (fun index =>
          let (result, reason) := (outcomes.getD index none).getD (.fault, "no outcome")
          (messageOf index, contactOf index, result, reason))
        let digest := TlsWire.hash (Recovery.canonical entries).toUTF8.data.toList
        insist ((← swap digest) == digest) "the two parties' per-id results differ"
        liftM (results.set entries : IO Unit)
        return delivered
      let deliver : M Nat := do
        let first ← openAll
        deliverJob inputs recipients config.notifyId config.notifyJournal first
      /- ---- The long-lived send session (SIGNAL_SERVE_DIR = DIR; node_daemon/README.md). ----
      The connections are opened once and kept; the daemon hands over one job at a time (one
      signed notify: DIR/job.json, `{"job", "request", "message", "journal"}`, written whole) and
      reads one result line per job on standard output (`{"job", "status", "results", ...}`, the
      same per-id results the one-notify session reports, agreed the same way). Between jobs the
      session ticks: the two controllers exchange which job each was handed (its name's hash),
      whether its daemon asks the session to end (DIR/stop), and their clocks. A job runs when
      both were handed the same one; the session ends cleanly, between jobs, when either daemon
      asks. While idle, each connection is polled (a closed one is replaced at once; a record that
      arrived is read and answered) and kept alive after 25 s without traffic (WebSocket ping under
      the libsignal profile, as libsignal; otherwise a keepalive request, awaited). The triple
      stocks refill in the background as in any session. A job's failure is the session's (as for
      the one-notify session); the daemon then starts a new session, which resumes from the
      journals. What is kept from job to job: the open connections and their request counters,
      the contacts' loaded state and preparation (`loadJob`), the account, the circuits. -/
      let emit (json : Lean.Json) : M Unit :=
        liftM ((do IO.println json.compress; (← IO.getStdout).flush) : IO Unit)
      -- One record that arrived on the connection in use while nothing was awaited (a pong, a
      -- ping or close of the server). `false`: the connection is gone.
      let drainOne (s : PublicReceive.State) : M (PublicReceive.State × Bool) := do
        match ← receiveSoft with
        | none => return (s, false)
        | some (.application handle) =>
          let (s, complete) ← record handle.id s
          insist (!complete) "unsolicited service response"
          let (s, frames) ← liftResult (PublicReceive.replies s (← controlMasks rpc s))
          for (_, frame) in frames do sendPublic (toBytes frame)
          for request in s.requests do
            let random ← rpc.call .publicRandom []
            insist (random.length == 32) "invalid joint randomness"
            let (frame, message) ← liftResult (PublicReceive.reply request (toBits (random.take 4)))
            unless message do sendPublic (toBytes frame)
          return ({ s with requests := [] }, true)
        | some .control => return (s, true)
        | some .closed => return (s, false)
      let serve (directory : String) : M Nat := do
        let first ← openAll
        let count := max sendCircuits 1
        liftM (recoveryUsed.set true : IO Unit)
        emit (Lean.Json.mkObj [("event", toJson "ready"), ("connections", toJson count)])
        let folder : System.FilePath := directory
        let opened ← agreedClock
        let mut lastUsed : Array Nat := Array.replicate count opened
        let mut lastJob := opened
        let mut finishedJobs : List String := []
        let mut served := 0
        let mut jobsDone := 0
        let mut pings := 0
        let mut running := true
        while running do
          -- The job this party's daemon handed over, if any (one already served is ignored until
          -- the daemon removes its file).
          let path := folder / "job.json"
          let job ← if ← liftM (path.pathExists : IO Bool) then do
              let text ← liftM (IO.FS.readFile path : IO String)
              pure (match Lean.Json.parse text with
                | .ok json => match json.getObjValAs? String "job", json.getObjValAs? String "request",
                    json.getObjValAs? String "message", json.getObjValAs? String "journal" with
                  | .ok named, .ok request, .ok message, .ok journalPath =>
                    if finishedJobs.contains named then none else some (named, request, message, journalPath)
                  | _, _, _, _ => none
                | .error _ => none)
            else pure none
          let stopping ← liftM ((folder / "stop").pathExists : IO Bool)
          let clock := (← liftM (Std.Time.Timestamp.now : IO Std.Time.Timestamp)).toMillisecondsSinceUnixEpoch.val.toNat
          let named := match job with
            | some (n, _, _, _) => TlsWire.hash n.toUTF8.data.toList
            | none => List.replicate 32 0
          let theirs ← swap (named ++ [if stopping then 1 else 0] ++ uint 8 clock)
          insist (theirs.length == 41) "invalid serve tick"
          let now ← liftResult (Node.Policy.Clock.agree clock (number (theirs.drop 33)))
          if job.isSome && theirs.take 32 == named then
            let (jobName, requestPath, messagePath, journalPath) := job.getD ("", "", "", "")
            let begun ← liftM (IO.monoMsNow : IO Nat)
            let text ← liftM (IO.FS.readFile messagePath : IO String)
            liftM (jobRequest.set (some requestPath) : IO Unit)
            liftM (results.set [] : IO Unit)
            liftM (recoveryLog.set [] : IO Unit)
            liftM (circuitSends.set [] : IO Unit)
            liftM (bodies.set [] : IO Unit)
            liftM (stamped.set [] : IO Unit)
            let contactsOfJob ← loadJob requestPath text
            let jobInputs ← notify contactsOfJob text (← agreedNow)
            let delivered ← if jobInputs.isEmpty then pure 0
              else deliverJob jobInputs contactsOfJob (some jobName) (some journalPath) first
            liftM (jobRequest.set none : IO Unit)
            served := served + jobInputs.length
            jobsDone := jobsDone + 1
            finishedJobs := (jobName :: finishedJobs).take 64
            let after ← agreedClock
            lastUsed := Array.replicate count after
            lastJob := after
            let absentNow ← liftM (absent.get : IO (List (Nat × Bool)))
            emit (Lean.Json.mkObj [("job", toJson jobName), ("status", toJson "completed"),
              ("results", toJson ((← liftM (results.get : IO (List Recovery.Entry))).map (fun (message, contact, result, reason) =>
                Lean.Json.mkObj [("message", toJson message), ("id", toJson (toString contact)), ("result", toJson result.text),
                  ("reason", toJson reason)]))),
              ("unknown", toJson ((absentNow.filter (fun entry => !entry.2)).map (fun entry => toString entry.1))),
              ("not_yet_readable", toJson ((absentNow.filter (·.2)).map (fun entry => toString entry.1))),
              ("recovery", toJson (← liftM (recoveryLog.get : IO (List String)))),
              ("messages", toJson jobInputs.length), ("delivered", toJson delivered),
              ("milliseconds", toJson ((← liftM (IO.monoMsNow : IO Nat)) - begun)),
              ("session_messages", toJson served), ("session_jobs", toJson jobsDone)])
          else if stopping || theirs.getD 32 0 == 1 then
            running := false
          else
            for index in [0:count] do
              liftM (current.set index : IO Unit)
              let mut s := (← liftM (states.get : IO (Array PublicReceive.State))).getD index first
              -- Closed by the server or the proxy while idle: replaced now, not at the next send.
              let wire ← (TlsWorker.onConnection rpc active index).call .pollRecord []
              if wire == [0] then
                reconnect
                lastUsed := lastUsed.set! index now
                continue
              if !wire.isEmpty then
                let slot := (← liftM (slots.get : IO (Array (IO.Ref (Option Bytes))))).getD index kept
                liftM (slot.set (some wire) : IO Unit)
                let (next, alive) ← drainOne s
                if !alive then
                  reconnect
                  lastUsed := lastUsed.set! index now
                  continue
                s := next
                saveState s
              if now ≥ lastUsed.getD index 0 + 25000 then
                let random ← rpc.call .publicRandom []
                insist (random.length == 32) "invalid joint randomness"
                if official then
                  pings := pings + 1
                  sendPublic (toBytes (PublicReceive.ping (pings % 256) (toBits (random.take 4))))
                else
                  let id ← nextId
                  sendPublic (toBytes (← liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
                  let (next, alive) ← awaitSoft 64 (PublicReceive.expect s id)
                  if alive then saveState next else reconnect
                lastUsed := lastUsed.set! index now
            -- A quarter of a second between ticks; a second after a minute without a job.
            liftM (IO.sleep (if now > lastJob + 60000 then 1000 else 250) : IO Unit)
        liftM (IO.eprintln s!"serve: {jobsDone} jobs, {served} messages; the session ends between jobs" : IO Unit)
        pure served
      -- The authenticated socket: answer the server's requests, keep the connection alive
      -- while nothing arrives, and stop after the expected number of delivered messages.
      -- A delivered message's body stays unrevealed and is not acknowledged yet.
      let closing ← liftM (IO.mkRef false : IO (IO.Ref Bool))
      let rec waiting (fuel : Nat) (s : PublicReceive.State) (pings : Nat) (expected : Nat) : M Nat := do
        match fuel with
        | 0 => throw "receive budget exhausted"
        | fuel+1 =>
          if (← liftM (delivered.get : IO Nat)) ≥ expected then
            -- Before leaving: one keepalive, answered. The server answers in order, so its
            -- reply shows it has read everything sent before it, the acknowledgements included;
            -- closing straight after an acknowledgement could lose it, and the message would be
            -- delivered again.
            if ← liftM (closing.get : IO Bool) then
              if !s.pending then return pings
            else
              liftM (closing.set true : IO Unit)
              let random ← rpc.call .publicRandom []
              insist (random.length == 32) "invalid joint randomness"
              let id := 2 ^ 63 + pings
              sendPublic (toBytes (← liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
              liftM (keepalives.modify (· + 1) : IO Unit)
              return ← waiting fuel (PublicReceive.expect s id) (pings + 1) expected
          -- libsignal profile: 31 seconds without a record, then a WebSocket ping (libsignal-net
          -- `WS_KEEP_ALIVE_INTERVAL`; its payload is a one-byte ping counter from 1). The pong
          -- is a control frame the parser skips.
          if official && s.upgraded && !(← TlsWorker.awaitRecord rpc kept 124 250) then
            let random ← rpc.call .publicRandom []
            insist (random.length == 32) "invalid joint randomness"
            sendPublic (toBytes (PublicReceive.ping ((pings + 1) % 256) (toBits (random.take 4))))
            liftM (keepalives.modify (· + 1) : IO Unit)
            waiting fuel s (pings + 1) expected
          else
          -- 25 seconds of agreed silence, then a keepalive.
          if !official && s.upgraded && !(← TlsWorker.awaitRecord rpc kept 100 250) then
            insist (!s.pending) "keepalive was not answered"
            let random ← rpc.call .publicRandom []
            insist (random.length == 32) "invalid joint randomness"
            let id := 2 ^ 63 + pings
            sendPublic (toBytes (← liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
            liftM (keepalives.modify (· + 1) : IO Unit)
            waiting fuel (PublicReceive.expect s id) (pings + 1) expected
          else
          match ← TlsApplication.receive app with
          | .application handle =>
            let (s, _) ← record handle.id s
            let (s, frames) ← liftResult (PublicReceive.replies s (← controlMasks rpc s))
            for (kind, frame) in frames do
              sendPublic (toBytes frame)
              insist (kind != 8) "WebSocket peer closed before completion"
            for request in s.requests do
              let random ← rpc.call .publicRandom []
              insist (random.length == 32) "invalid joint randomness"
              let (frame, message) ← liftResult (PublicReceive.reply request (toBits (random.take 4)))
              -- A delivered message was dealt with (stored or refused) while its record was
              -- read; acknowledging it lets the server remove it from the queue.
              -- Whether this message's envelope was refused (`SIGNAL_ACK_REFUSED` above). One left
              -- on the server does not count towards the messages expected: it would be delivered
              -- first again on every connection.
              let wasRefused ← if message then do
                  let queue ← liftM (refusals.get : IO (List Bool))
                  liftM (refusals.set queue.tail : IO Unit)
                  pure (queue.headD false)
                else pure false
              if message && !(wasRefused && keepRefused) then liftM (delivered.modify (· + 1) : IO Unit)
              let acknowledge := (!message || receiving.isSome) && !(wasRefused && keepRefused)
              liftM (recordEvent "server-request" [("delivered_message", toJson message), ("refused", toJson wasRefused),
                ("answered", toJson acknowledge)] : IO Unit)
              if acknowledge then sendPublic (toBytes frame)
            waiting fuel { s with requests := [] } pings expected
          | .control => waiting fuel s pings expected
          | .closed =>
            liftM (recordEvent "closed" [("while", toJson "waiting for messages")] : IO Unit)
            throw "TLS closed while waiting for messages"
      /- ---- The registration ceremony (CEREMONY.md). ----
      Stage `register` (unauthenticated socket): verification session, captcha, SMS code, then
      `POST /v1/registration`. Public to both nodes: the number, captcha token, code, session id
      and the account's public key material (the keys were generated in the clear). The account
      password and the recovery password are made in the engines (`ceremonySecrets`) and enter
      the request only there (`ceremonyRegister`); each node keeps its XOR share of each.
      Stage `certificate` (authenticated socket, opened with those shares): the sender
      certificate and the one-time prekeys. Response bodies are revealed here (`openBody`): they
      are about our own account. What an operator supplies is given to ONE node, which tells the
      other through the workers' link. -/
      if let some stage := ceremony then
        let directory : System.FilePath ← match config.ceremonyDir with
          | some path => pure (path : System.FilePath)
          | none => throw "SIGNAL_CEREMONY_DIR is required"
        let fileText (name : String) : M String := do
          let path := directory / name
          if ← liftM (path.pathExists : IO Bool) then pure (← liftM (IO.FS.readFile path : IO String)).trimAscii.toString else pure ""
        let textOf (bytes : Bytes) : String := (String.fromUTF8? ⟨bytes.toArray⟩).getD ""
        let shared (name : String) : M String := do
          let mine := (← fileText name).toUTF8.data.toList
          let theirs ← swap mine
          insist (mine.isEmpty || theirs.isEmpty || mine == theirs) s!"the two nodes were given different {name}"
          let value := if mine.isEmpty then theirs else mine
          insist (!value.isEmpty) s!"neither node was given {name}"
          if mine.isEmpty then liftM (IO.FS.writeFile (directory / name) (textOf value ++ "\n") : IO Unit)
          pure (textOf value)
        let material (text : String) : M Ceremony.Registration := do
          let keys ← liftResult (Lean.Json.parse text)
          liftResult (do Ceremony.Registration.ofJson? (← keys.getObjVal? "registration"))
        let mut s : PublicReceive.State := { PublicReceive.start (toBits accept) with lenient := true, openBody := true }
        let mut fuel := 64
        while !s.upgraded do
          insist (fuel > 0) "receive budget exhausted"
          fuel := fuel - 1
          match ← TlsApplication.receive (← appNow) with
          | .application handle =>
            let (next, _) ← record handle.id s
            s := next
          | .control => pure ()
          | .closed => throw "TLS closed before the upgrade"
        -- A public request and its response (status 2xx required); the body as JSON.
        let call (s : PublicReceive.State) (verb path : String) (headers : List String) (body : String) :
            M (PublicReceive.State × Lean.Json) := do
          let id ← nextId
          let random ← rpc.call .publicRandom []
          insist (random.length == 32) "invalid joint randomness"
          let request := PublicRequest.field 10 [.bytes (PublicRequest.text verb)] ++ PublicRequest.field 18 [.bytes (PublicRequest.text path)] ++
            (if body.isEmpty then [] else PublicRequest.field 26 [.bytes (PublicRequest.text body)]) ++
            [PublicRequest.Piece.bytes (32 :: PublicRequest.varint id)] ++
            headers.flatMap (fun header => PublicRequest.field 42 [.bytes (PublicRequest.text header)])
          let (frame, _, _) ← liftResult (PublicRequest.assemble (PublicRequest.Piece.bytes [8, 1] :: PublicRequest.field 18 request)
            (toBits (random.take 4)) 0)
          insist (frame.length ≤ 16000) "a ceremony request does not fit one record"
          sendPublic (toBytes frame)
          touch
          let s ← awaitReply 64 (PublicReceive.expect s id)
          liftM (recordEvent "ceremony-response" [("request", toJson s!"{verb} {path}"), ("status", toJson s.status)] : IO Unit)
          insist (200 ≤ s.status && s.status < 300) s!"{verb} {path} was answered {s.status}"
          pure (s, (Lean.Json.parse (textOf (toBytes s.body))).toOption.getD Lean.Json.null)
        let json := ["content-type: application/json"]
        if stage == "register" then
          let phone ← shared "number.txt"
          insist (Ceremony.phoneNumber phone && Ceremony.basicConsistent phone) "the phone number must look like +15551234567"
          let keys ← material (← shared "keys.json")
          let (s1, created) ← call s "POST" "/v1/verification/session" json (Ceremony.sessionBody phone)
          s := s1
          let some session := (created.getObjValAs? String "id").toOption | throw "the verification session has no id"
          insist (Ceremony.plain session) "verification session id shape"
          let mut state := created
          if ((state.getObjValAs? (Array String) "requestedInformation").toOption.getD #[]).contains "captcha" then
            let given ← shared "captcha.txt"
            let captcha := if given.startsWith "signalcaptcha://" then String.ofList (given.toList.drop 16) else given
            insist (Ceremony.plain captcha) "captcha token shape"
            let (s2, patched) ← call s "PATCH" s!"/v1/verification/session/{session}" json (Ceremony.captchaBody captcha)
            s := s2
            state := patched
          insist ((state.getObjValAs? Bool "allowedToRequestCode").toOption == some true)
            "the server does not allow requesting a code for this session"
          let (s3, _) ← call s "POST" s!"/v1/verification/session/{session}/code" (json ++ ["accept-language: en"])
            (Ceremony.requestCodeBody "ceremony")
          s := s3
          -- The SMS code: an operator writes it to code.txt on one node. Until then, keepalives
          -- (the server drops a socket that is silent for 90 seconds).
          let mut code := ""
          let mut waited := 0
          while code.isEmpty do
            insist (waited < 1800) "no verification code was supplied in time"
            let mine := (← fileText "code.txt").toUTF8.data.toList
            let theirs ← swap mine
            insist (mine.isEmpty || theirs.isEmpty || mine == theirs) "the two nodes were given different codes"
            code := String.ofList ((textOf (if mine.isEmpty then theirs else mine)).toList.filter Char.isDigit)
            if code.isEmpty then
              liftM (IO.sleep 1000 : IO Unit)
              waited := waited + 1
              s ← keepAlive s
          let (s4, checked) ← call s "PUT" s!"/v1/verification/session/{session}/code" json (Ceremony.submitCodeBody code)
          s := s4
          insist ((checked.getObjValAs? Bool "verified").toOption == some true)
            "the server did not mark the session verified (wrong code?); nothing was registered"
          -- The password and the recovery password, made in the engines. This node's XOR shares
          -- are on disk before the request leaves: a crash cannot lose what the server accepted.
          -- (Plan 4.2 row 4: the operation's reply is this party's own; held as `Secret` from here.)
          let shares := Secret.hide (← rpc.call .ceremonySecrets [])
          insist (shares.length == Ceremony.passwordBytes + Ceremony.recoveryBytes) "invalid ceremony shares"
          let passwordShare := shares.map (·.take Ceremony.passwordBytes)
          inBand (Channels.saveShare (directory / "password.share") passwordShare)
          inBand (Channels.saveShare (directory / "recovery.share") (shares.map (·.drop Ceremony.passwordBytes)))
          let (basicText, tail) := Ceremony.basic phone
          let (before, after) := Ceremony.registrationBody session keys
          let id ← nextId
          let random ← rpc.call .publicRandom []
          insist (random.length == 32) "invalid joint randomness"
          let request := PublicRequest.field 10 [.bytes (PublicRequest.text "POST")] ++
            PublicRequest.field 18 [.bytes (PublicRequest.text "/v1/registration")] ++
            PublicRequest.field 26 [.bytes (PublicRequest.text before), .slot 1 44, .bytes (PublicRequest.text after)] ++
            [PublicRequest.Piece.bytes (32 :: PublicRequest.varint id)] ++
            PublicRequest.field 42 [.bytes (PublicRequest.text "content-type: application/json")] ++
            PublicRequest.field 42 [.bytes (PublicRequest.text ("authorization: Basic " ++ basicText)), .slot 0 32]
          let (frame, payloadAt, offsets) ← liftResult (PublicRequest.assemble
            (PublicRequest.Piece.bytes [8, 1] :: PublicRequest.field 18 request) (toBits (random.take 4)) 2)
          insist (frame.length ≤ 16384) "the registration request does not fit one record"
          -- The request as the controllers know it: the two private slots are zero bytes.
          liftM (recordEvent "ceremony-register" [("request_id", toJson (toString id)), ("frame_hex", toJson (TlsWorkerProcess.hex (toBytes frame))),
            ("credential_slot", toJson (offsets.getD 0 0)), ("recovery_slot", toJson (offsets.getD 1 0)), ("payload_at", toJson payloadAt),
            ("mask_hex", toJson (TlsWorkerProcess.hex (random.take 4)))] : IO Unit)
          s ← keepAlive s
          let handle ← rpc.call .ceremonyRegister (uint 2 payloadAt ++ uint 2 (offsets.getD 0 0) ++ uint 2 (offsets.getD 1 0) ++
            random.take 4 ++ [UInt8.ofNat tail.length] ++ toBytes tail ++ toBytes frame)
          insist (handle.length == 8 && number handle != 0) "invalid request handle"
          TlsApplication.send (← appNow) ⟨number handle⟩ frame.length
          touch
          s ← awaitReply 64 (PublicReceive.expect s id)
          liftM (recordEvent "ceremony-response" [("request", toJson "POST /v1/registration"), ("status", toJson s.status)] : IO Unit)
          insist (s.status == 200) s!"the registration was answered {s.status}"
          let registered := (Lean.Json.parse (textOf (toBytes s.body))).toOption.getD Lean.Json.null
          let some aci := (registered.getObjValAs? String "uuid").toOption | throw "the registration response has no account id"
          let pni := (registered.getObjValAs? String "pni").toOption.getD ""
          let account ← liftResult (fromHex (String.ofList (aci.toList.filter (· != '-'))))
          insist (account.length == 16) "account id shape"
          -- XOR shares of the socket credentials (account id 16, password 22), the form the
          -- sessions take them in: the public account id is in party 0's share.
          let mine := Secret.hide (if party == "0" then account else List.replicate 16 0) ++ passwordShare
          inBand (Channels.saveShare (directory / "credentials.share") mine)
          liftM (IO.FS.writeFile (directory / "account.json") ((Lean.Json.mkObj [("number", toJson phone), ("aci", toJson aci),
            ("pni", toJson pni), ("verification_session", toJson session)]).compress ++ "\n") : IO Unit)
        else
          insist (stage == "certificate") "SIGNAL_CEREMONY must be register or certificate"
          let (s1, got) ← call s "GET" "/v1/certificate/delivery?includeE164=false" [] ""
          s := s1
          let some certificate := (got.getObjValAs? String "certificate").toOption | throw "no sender certificate in the response"
          insist (Ceremony.plain certificate) "sender certificate shape"
          liftM (IO.FS.writeFile (directory / "certificate.b64") (certificate ++ "\n") : IO Unit)
          let keys ← material (← fileText "keys.json")
          unless keys.oneTime.isEmpty do
            let (s2, _) ← call s "PUT" "/v2/keys?identity=aci" json (Ceremony.oneTimeBody keys)
            s := s2
        liftM (ceremonyDone.set true : IO Unit)
        TlsApplication.abort app
        return 0
      if authenticated then
        let pings ← waiting 4096 (PublicReceive.start (toBits accept)) 0 config.expect
        TlsApplication.abort app
        return pings
      else
        -- Against a Signal server a send may be answered 409/410 (the contact's devices changed):
        -- such a response is completed and handled in the loop instead of ending the session.
        -- With the database nodes: `deliver`, where a contact's failure is that contact's result.
        -- The long-lived session (`serve`) is built on it.
        insist (serveDir.isNone || recovery) "SIGNAL_SERVE_DIR needs the database nodes, the export and recovery"
        let finished ← if recovery then (match serveDir with | some folder => serve folder | none => deliver) else do
          requireLoaded
          openCircuits   -- connections 1..N-1 with several Tor circuits; nothing otherwise
          loop (256 + 16 * inputs.length) { PublicReceive.start (toBits accept) with lenient := exportPath.isSome } inputs 0
        writeBack
        TlsApplication.abort app
        return finished
    let outcome ← action.run
    if !outcome.isOk then
      let _ ← (TlsWorker.emptyReply running.rpc .abort []).run
      pure ()
    let verified ← certificate.get
    let codes ← operations.get
    -- (A recovery session passes when it ended in results both parties agreed on; which
    -- operations it used depends on what happened to its contacts. Operation 15, the client's
    -- own KeyUpdate, is not used under the libsignal profile.)
    let passed := verified && outcome.isOk && (ceremony.isNone || (← ceremonyDone.get)) && !codes.contains 18 &&
      (authenticated || (← ceremonyDone.get) || (← recoveryUsed.get) ||
      ((codes.contains 15 || official) && codes.contains 43 &&codes.contains 41 && codes.contains 42 && codes.contains 37 && codes.contains 38))
    IO.println (Lean.Json.mkObj [("passed",toJson passed),("certificate_verified",toJson verified),
      ("responses_completed",toJson (match outcome with | .ok n => n | .error _ => 0)),
      ("bytes_revealed",toJson (← revealed.get)),("messages_delivered",toJson (← delivered.get)),("keepalives",toJson (← keepalives.get)),
      ("envelopes",toJson ((← envelopes.get).map (fun (kind, size) => [kind, size]))),
      ("received",toJson ((← received.get).map (fun (contact, text) => [toString contact, text]))),("refused",toJson (← refused.get)),("private_receive_parsing_used",toJson (codes.contains 18)),
      ("circuits",toJson circuits),("circuit_sends",toJson ((← circuitSends.get).map (fun (contact, index) => [toString contact, toString index]))),
      ("circuit_labels",toJson ((List.range circuits).map (fun i => [(Circuits.labels session circuits (some i)).1, (Circuits.labels session circuits (some i)).2]))),
      -- Per id of each notify message, once both parties agreed: one of `Recovery.Result.text`.
      ("results",toJson ((← results.get).map (fun (message, contact, result, reason) => Lean.Json.mkObj
        [("message",toJson message),("id",toJson (toString contact)),("result",toJson result.text),("reason",toJson reason)]))),
      ("recovery_used",toJson (← recoveryUsed.get)),("recovery",toJson (← recoveryLog.get)),
      -- Requested ids (daemon notify) left out of the session: not on the database nodes; not served until their next epoch.
      ("unknown",toJson (((← absent.get).filter (fun entry => !entry.2)).map (fun entry => toString entry.1))),
      ("not_yet_readable",toJson (((← absent.get).filter (·.2)).map (fun entry => toString entry.1))),
      ("error",toJson (match outcome with | .ok _ => "" | .error e => e))]).compress
    unless passed do throw (IO.userError "public-receive service session failed")
  finally running.stop
