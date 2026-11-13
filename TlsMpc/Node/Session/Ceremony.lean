import TlsMpc.TlsWorkerProcess
import TlsMpc.CeremonyRequests
import TlsMpc.Node.Policy.Request
import TlsMpc.Node.Session.Common

/-!
# The registration ceremony (CEREMONY.md; REORGANIZATION_PLAN.md stage S7)

- `stage`: the subcommand `ceremony NODE_CONFIG.json NAME register|certificate|store`, run on BOTH
  nodes with the same NAME. Each stage is one two-party session of this controller, started as a
  child with the stage's settings.
- `upgrade`: how a ceremony session opens its socket (`Start`): `register` the unauthenticated one,
  `certificate` the authenticated one with this node's XOR share of the new credentials.
- `run`: the session's stage.
  - `register` (unauthenticated socket): verification session, captcha, SMS code, then
    `POST /v1/registration`. Public to both nodes: the number, captcha token, code, session id and
    the account's public key material (the keys were generated in the clear). The account password
    and the recovery password are made in the engines (`Flow.Ceremony.secrets`) and enter the
    request only there (`Flow.Ceremony.register`); each node keeps its XOR share of each.
  - `certificate` (authenticated socket, opened with those shares): the sender certificate and the
    one-time prekeys.
  Response bodies are revealed here (`openBody`): they are about our own account. What an operator
  supplies is given to ONE node, which tells the other through the workers' link.

Moved from the controller's `main` (stage S7), same operations and order. No I/O primitive.
-/

namespace TlsMpc.Node.Session.Ceremony
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Node TlsMpc.Node.Bytes TlsMpc.Node.Session
open TlsMpc.Node.Channels.Real (inBand)

/-- **The `ceremony` subcommand** (before any configuration of this controller exists).
NODE_CONFIG is the node daemon's configuration (node_daemon/README.md). This node's files are in
STATE/ceremony/. Before `register`, ONE node's operator puts there: number.txt, keys.json (the key
tool's output), captcha.txt (the token is longer than a terminal line: a file, never a prompt), and,
when the SMS arrives, code.txt. `register` leaves this node's shares (credentials.share,
recovery.share) and account.json; `certificate` leaves certificate.b64; `store` puts the account's
row on the database nodes (it needs the sessions' export file: scaffolding). -/
def stage (configPath name stage : String) : IO Unit := do
  let config ← Channels.Real.readJson configPath
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
  Channels.Real.ensureDirectory directory
  let hosts := (((field ["worker", "hosts"]).bind (fun j => j.getArr?.toOption)).getD #[]).toList.filterMap (fun j => j.getStr?.toOption)
  Channels.Real.writePublic directory (.ceremonyHosts hosts)
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
        Channels.Real.ensureDirectory s!"{directory}/db"
        -- The existing session that creates the account's row from the credentials in two
        -- shares (it expects no message and ends at once).
        pure (180, ← text ["worker", "receive_directory"], [("SIGNAL_LOCAL_CREDENTIALS_FILE", shareFile), ("SIGNAL_LOCAL_EXPECT", "0"),
          ("SIGNAL_LOCAL_EXPORT", ← text ["test", "export"]), ("SIGNAL_LOCAL_KEM", ← text ["test", "kem_tool"]),
          ("SIGNAL_DB_CLIENT", ← text ["database", "client"]), ("SIGNAL_DB_NETWORK", ← text ["database", "network"]),
          ("SIGNAL_DB_KEY", ← text ["database", "key"]), ("SIGNAL_DB_WORK", s!"{directory}/db"),
          ("SIGNAL_DB_TOKENS", ← text ["test", "tokens"])])
    | _ => throw (IO.userError "ceremony stages: register, certificate, store")
  unless stage == "register" || (← Channels.Real.loadShare shareFile).any (·.length == 38) do
    throw (IO.userError s!"{directory}/credentials.share is missing: run the register stage first")
  let session := TlsWorkerProcess.hex (TlsWire.hash s!"ceremony {name} {stage}".toUTF8.data.toList)
  let child ← Channels.Real.runChild {
    controller := ← text ["controller"]
    args := [← text ["worker", "binary"], workerDirectory, toString (← count ["party"]), s!"{directory}/hosts",
      toString ((← count ["worker", "port_base"]) + offset), ← text ["circuits", "tool"], session, ← text ["signal", "endpoint"],
      toString (← count ["signal", "port"]), ← text ["signal", "hostname"], ← text ["signal", "certificate_checker"],
      ← text ["signal", "trust_root"], "0"]
    env := environment ++ manifest ++ [("SIGNAL_RECORD", s!"{directory}/record.jsonl")] ++ extra }
  Channels.Real.writePublic directory (.ceremonyLog stage child.stderr)
  Channels.Real.writePublic directory (.ceremonyReport stage child.stdout)
  let report := (Lean.Json.parse ((child.stdout.splitOn "\n").headD "")).toOption.getD Lean.Json.null
  let passed := child.exitCode == 0 && (report.getObjValAs? Bool "passed").toOption == some true
  Channels.Real.report (.ceremonyStage stage passed directory ((report.getObjValAs? String "error").toOption.getD ""))
  unless passed do throw (IO.userError s!"ceremony stage {stage} failed; see {directory}/{stage}.log")

/-- The ceremony session's socket (no account exists yet, so no contacts): `certificate` the
authenticated one with this node's XOR share of the new credentials (SIGNAL_LOCAL_CREDENTIALS_FILE),
`register` the unauthenticated one. Returns the expected accept value. -/
def upgrade (stage : String) : SessionM (Bytes × List (Nat × Secret Bytes × Nat)) := do
  let c ← read
  if stage == "certificate" then
    let .share share := c.config.account | throw "the certificate stage needs this node's credentials share"
    Flow.Account.credentials c.w share
    let (request, size, accept) ← Flow.Upgrade.authenticated c.w 1
    TlsApplication.send (← get).pool.first.session request size
    pure (accept.val, [])
  else
    let opened ← Flow.Upgrade.anonymous c.w
    sendPublic (toBytes (c.anonymousUpgrade (toBits opened.val.1)))
    pure (opened.val.2, [])

/-- **The ceremony session's stage** (SIGNAL_CEREMONY: `register` or `certificate`;
SIGNAL_CEREMONY_DIR: this node's ceremony directory), after `upgrade` (`accept`). -/
def run (stage : String) (accept : Bytes) : SessionM Nat := do
  let c ← read
  let w := c.w
  let directory : System.FilePath ← match c.config.ceremonyDir with
    | some path => pure (path : System.FilePath)
    | none => throw "SIGNAL_CEREMONY_DIR is required"
  let fileText (input : CeremonyInput) : SessionM String := io (c.ch.ceremonyFile directory input)
  let textOf (bytes : Bytes) : String := (String.fromUTF8? ⟨bytes.toArray⟩).getD ""
  -- An operator's input, given to one node: the other node's copy (`PeerMsg.ceremonyInput`).
  let theirInput (input : CeremonyInput) (mine : Bytes) : SessionM Bytes := do
    match ← peer (.ceremonyInput input mine) with
    | .ceremonyInput _ theirs => pure theirs
    | _ => throw "invalid ceremony input reply"
  let shared (input : CeremonyInput) : SessionM String := do
    let name := input.fileName
    let mine := (← fileText input).toUTF8.data.toList
    let theirs ← theirInput input mine
    insist (mine.isEmpty || theirs.isEmpty || mine == theirs) s!"the two nodes were given different {name}"
    let value := if mine.isEmpty then theirs else mine
    insist (!value.isEmpty) s!"neither node was given {name}"
    if mine.isEmpty then c.ch.writePublic directory (.ceremonyInput input (textOf value))
    pure (textOf value)
  let material (text : String) : SessionM Ceremony.Registration := do
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
      SessionM (PublicReceive.State × Lean.Json) := do
    let id ← nextId
    let random := (← Flow.Random.joint w).val
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
    c.ch.record (.ceremonyResponse s!"{verb} {path}" s.status)
    insist (200 ≤ s.status && s.status < 300) s!"{verb} {path} was answered {s.status}"
    pure (s, (Lean.Json.parse (textOf (toBytes s.body))).toOption.getD Lean.Json.null)
  let json := ["content-type: application/json"]
  if stage == "register" then
    let phone ← shared .number
    insist (Ceremony.phoneNumber phone && Ceremony.basicConsistent phone) "the phone number must look like +15551234567"
    let keys ← material (← shared .keys)
    let (s1, created) ← call s "POST" "/v1/verification/session" json (Ceremony.sessionBody phone)
    s := s1
    let some session := (created.getObjValAs? String "id").toOption | throw "the verification session has no id"
    insist (Ceremony.plain session) "verification session id shape"
    let mut state := created
    if ((state.getObjValAs? (Array String) "requestedInformation").toOption.getD #[]).contains "captcha" then
      let given ← shared .captcha
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
    -- The SMS code: an operator writes it to code.txt on one node. Until then, keepalives (the
    -- server drops a socket that is silent for 90 seconds).
    let mut code := ""
    let mut waited := 0
    while code.isEmpty do
      insist (waited < 1800) "no verification code was supplied in time"
      let mine := (← fileText .code).toUTF8.data.toList
      let theirs ← theirInput .code mine
      insist (mine.isEmpty || theirs.isEmpty || mine == theirs) "the two nodes were given different codes"
      code := String.ofList ((textOf (if mine.isEmpty then theirs else mine)).toList.filter Char.isDigit)
      if code.isEmpty then
        c.ch.sleep 1000
        waited := waited + 1
        s ← keepAlive s
    let (s4, checked) ← call s "PUT" s!"/v1/verification/session/{session}/code" json (Ceremony.submitCodeBody code)
    s := s4
    insist ((checked.getObjValAs? Bool "verified").toOption == some true)
      "the server did not mark the session verified (wrong code?); nothing was registered"
    -- The password and the recovery password, made in the engines. This node's XOR shares are on
    -- disk before the request leaves: a crash cannot lose what the server accepted. (Plan 4.2 row
    -- 4: the operation's reply is this party's own; held as `Secret` from here.)
    let shares ← Flow.Ceremony.secrets w
    insist (shares.length == Ceremony.passwordBytes + Ceremony.recoveryBytes) "invalid ceremony shares"
    let passwordShare := shares.map (·.take Ceremony.passwordBytes)
    inBand (c.ch.saveShare directory .password passwordShare [])
    inBand (c.ch.saveShare directory .recovery (shares.map (·.drop Ceremony.passwordBytes)) [])
    let (basicText, tail) := Ceremony.basic phone
    let (before, after) := Ceremony.registrationBody session keys
    let id ← nextId
    let random := (← Flow.Random.joint w).val
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
    c.ch.record (.ceremonyRegister id (toBytes frame) (offsets.getD 0 0) (offsets.getD 1 0) payloadAt (random.take 4))
    s ← keepAlive s
    let handle ← Flow.Ceremony.register w payloadAt offsets (random.take 4) (toBytes tail) (toBytes frame)
    TlsApplication.send (← appNow) handle frame.length
    touch
    s ← awaitReply 64 (PublicReceive.expect s id)
    c.ch.record (.ceremonyResponse "POST /v1/registration" s.status)
    insist (s.status == 200) s!"the registration was answered {s.status}"
    let registered := (Lean.Json.parse (textOf (toBytes s.body))).toOption.getD Lean.Json.null
    let some aci := (registered.getObjValAs? String "uuid").toOption | throw "the registration response has no account id"
    let pni := (registered.getObjValAs? String "pni").toOption.getD ""
    let account ← liftResult (fromHex (String.ofList (aci.toList.filter (· != '-'))))
    insist (account.length == 16) "account id shape"
    -- XOR shares of the socket credentials (account id 16, password 22), the form the sessions
    -- take them in: the public account id is in party 0's share.
    let mine := Secret.hide (if c.party == "0" then account else List.replicate 16 0) ++ passwordShare
    inBand (c.ch.saveShare directory .credentials mine [])
    c.ch.writePublic directory (.ceremonyAccount phone aci pni session)
  else
    insist (stage == "certificate") "SIGNAL_CEREMONY must be register or certificate"
    let (s1, got) ← call s "GET" "/v1/certificate/delivery?includeE164=false" [] ""
    s := s1
    let some certificate := (got.getObjValAs? String "certificate").toOption | throw "no sender certificate in the response"
    insist (Ceremony.plain certificate) "sender certificate shape"
    c.ch.writePublic directory (.senderCertificate certificate)
    let keys ← material (← fileText .keys)
    unless keys.oneTime.isEmpty do
      let (s2, _) ← call s "PUT" "/v2/keys?identity=aci" json (Ceremony.oneTimeBody keys)
      s := s2
  modifyReport fun r => { r with ceremonyDone := true }
  TlsApplication.abort (← get).pool.first.session
  return 0

end TlsMpc.Node.Session.Ceremony
