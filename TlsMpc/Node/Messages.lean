import Lean
import TlsMpc.TlsWire
import TlsMpc.Node.Policy.Recovery

/-!
# Every message that leaves the controller (REORGANIZATION_PLAN.md section 3.1, stage S5)

One type per channel, each constructor one kind of message, its encoder next to it. Together with
`TlsMpc/Node/Channels.lean` (the only file that performs the I/O) this is what a reviewer reads to
see everything a node's controller sends (plan section 2.1):

| Channel                                   | Type            | Encoder                  |
|-------------------------------------------|-----------------|--------------------------|
| the other node (worker op 39, control link) | `PeerMsg`     | `PeerMsg.encode`, replies `PeerMsg.decodeReply` |
| the database client (`handoff_client`)    | `DbCall`        | `DbCall.encode`          |
| the node daemon / operator (stdout)       | `DaemonLine`    | `DaemonLine.encode`      |
| the event record (`SIGNAL_RECORD`)        | `RecordEvent`   | `RecordEvent.encode`     |
| standard error                            | `LogLine`       | `LogLine.encode`         |
| the notify journal (own disk)             | `JournalLine`   | `JournalLine.encode`     |
| public files on own disk                  | `PublicFile`    | `PublicFile.name/contents` |
| this party's secret files on own disk     | `ShareFile`     | `ShareFile.name` (the secret is given to `Channels.saveShare` beside it) |
| the certificate checker (`public_auth`)   | `CertificateQuery` | `CertificateQuery.args` |
| the ceremony's child session              | `ChildSession`  | its fields               |

The server and the engines are not here: what reaches the server is what the engines open (worker
operations today; `Engine` instructions from stage S9).

**No field of any type in this file is a `Secret` or an engine handle** (plan 3.1, theorem T9 "by
type"). Two checks enforce it: `scripts/lint_node.py` (check `message-fields`: the words do not
occur in this file outside comments and strings) and `checkPublic` at the end of this file, which
fails the build if any constructor of a type declared here mentions `TlsMpc.Node.Secret`,
`TlsMpc.Node.Handle` or `TlsMpc.TlsWorker.BufferHandle`, directly or through the types it uses.

Classes (SECURITY_MAP; plan 2.1): **P** public (a function of configuration, the application's
request, opened values and public replies), **O** an opened value (released by the engines),
**OWN** this party's own key material that the owner's policy allows in the clear, **S** to this
node's own disk. No emitter imports this module.
-/

namespace TlsMpc.Node
open TlsMpc.TlsWire
open Lean (toJson Json)

namespace Messages

/-- Lower-case hex (the same as `TlsWorkerProcess.hex`). -/
def hex (bytes : Bytes) : String := String.ofList (bytes.flatMap fun byte =>
  let digits := "0123456789abcdef".toList.toArray
  [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!])

/-- A result entry as the application reads it (`results` of a job or a session). -/
def entryJson (entry : Recovery.Entry) : Json :=
  let (message, contact, result, reason) := entry
  Json.mkObj [("message", toJson message), ("id", toJson (toString contact)), ("result", toJson result.text),
    ("reason", toJson reason)]

end Messages
open Messages

/-! ## The other node (through the worker's control link, operation 39) -/

/-- What the operator gives ONE node for the registration ceremony (CEREMONY.md section 2); the
node tells the other through the workers' link. -/
inductive CeremonyInput where
  | number | keys | captcha | code
  deriving BEq, Repr

def CeremonyInput.fileName : CeremonyInput → String
  | .number => "number.txt"
  | .keys => "keys.json"
  | .captcha => "captcha.txt"
  | .code => "code.txt"

/-- A settled journal entry as the two controllers compare them: (message number within the
notify, contact id, result). -/
abbrev JournalEntry := Nat × Nat × Recovery.Result

/-- Its 21 bytes on the link: message (4), contact (16), the result's index in `Result.all`. -/
def JournalEntry.encode (entry : JournalEntry) : Bytes :=
  let (message, contact, result) := entry
  uint 4 message ++ uint 16 contact ++ [UInt8.ofNat ((Recovery.Result.all.findIdx? (· == result)).getD 255)]

def JournalEntry.decode (chunk : Bytes) : Option JournalEntry :=
  (Recovery.Result.all[(chunk.getD 20 0).toNat]?).map fun result =>
    (number (chunk.take 4), number ((chunk.drop 4).take 16), result)

/-- **To the other controller** (plan 3.1; T9: every field public by type). Each is sent with
`Channels.exchange`, which gets the other node's message of the SAME kind back
(`decodeReply`, `decodeReply_kind`). Every value here is one both nodes compute from public
inputs, or one the protocol makes public between the two nodes. -/
inductive PeerMsg where
  /-- **P.** SHA-256 of `Config.agreedText` (S4; SECURITY_MAP D.11): the settings that must be the
  same on both nodes. The first message of every two-party session; one exchange of 32 bytes. -/
  | settingsDigest (digest : Bytes)
  /-- **P.** This node's clock in milliseconds; both use `Policy.Clock.agree` of the two
  (`Clock.agreed_within`). -/
  | clock (ms : Nat)
  /-- **P.** "My write of this blob reached the database nodes" (the blob itself is the same
  on both sides). -/
  | submitted
  /-- **P.** Whether this node's database client saw the write acknowledged. -/
  | acknowledged (yes : Bool)
  /-- **P (designed public).** This party's parity shares of a database read (the client's
  `parity` output): their sums must be zero; trusted `handoff_client` output, SECURITY_MAP A.3. -/
  | parity (file : Bytes)
  /-- **P.** Which of the (at most 16) database nodes this party saw commit a dealt key. -/
  | committedNodes (nodes : List Bool)
  /-- **P.** SHA-256 of the requested ids the database does not hold or does not serve yet. -/
  | absentDigest (digest : Bytes)
  /-- **P.** This node's settled journal entries for the notify being resumed. -/
  | journal (entries : List JournalEntry)
  /-- **P.** SHA-256 of the per-id results (`Recovery.canonical`); reported only when equal (T11). -/
  | resultsDigest (digest : Bytes)
  /-- **P.** The long-lived session's tick: the SHA-256 of the job's name this node was handed,
  whether its daemon asks to stop, and its clock. -/
  | serveTick (job : Option Bytes) (stop : Bool) (ms : Nat)
  /-- **P / OWN.** An operator's input to the ceremony, given to one node (empty from the other).
  `keys.json` holds the account's private keys too: both nodes see them by the owner's policy
  (CEREMONY.md section 4; plan 4.2 row 7, **Default:** no split). -/
  | ceremonyInput (input : CeremonyInput) (bytes : Bytes)

namespace PeerMsg

def name : PeerMsg → String
  | .settingsDigest _ => "settings digest"
  | .clock _ => "clock"
  | .submitted => "submitted"
  | .acknowledged _ => "acknowledged"
  | .parity _ => "parity"
  | .committedNodes _ => "committed nodes"
  | .absentDigest _ => "absent digest"
  | .journal _ => "journal"
  | .resultsDigest _ => "results digest"
  | .serveTick .. => "serve tick"
  | .ceremonyInput .. => "ceremony input"

/-- The bytes given to the link. -/
def encode : PeerMsg → Bytes
  | .settingsDigest digest => digest
  | .clock ms => uint 8 ms
  | .submitted => [1]
  | .acknowledged yes => [if yes then 1 else 0]
  | .parity file => file
  | .committedNodes nodes => nodes.map (fun b => if b then 1 else 0) ++ List.replicate (16 - nodes.length) 0
  | .absentDigest digest => digest
  | .journal entries => entries.flatMap JournalEntry.encode
  | .resultsDigest digest => digest
  | .serveTick job stop ms => job.getD (List.replicate 32 0) ++ [if stop then 1 else 0] ++ uint 8 ms
  | .ceremonyInput _ bytes => bytes

/-- `false` only for the settings digest: one exchange of fixed size. Every other message goes
as its length (4 bytes) and then chunks of at most 60000 bytes (`Channels.exchange`). -/
def sized : PeerMsg → Bool
  | .settingsDigest _ => false
  | _ => true

/-- The other node's message of the same kind as `mine`, from its bytes. -/
def decodeReply (mine : PeerMsg) (theirs : Bytes) : Except String PeerMsg :=
  match mine with
  | .settingsDigest _ => .ok (.settingsDigest theirs)
  | .clock _ => .ok (.clock (number theirs))
  | .submitted => .ok .submitted
  | .acknowledged _ => .ok (.acknowledged (theirs == [1]))
  | .parity _ => .ok (.parity theirs)
  | .committedNodes _ => .ok (.committedNodes (theirs.map (· == 1)))
  | .absentDigest _ => .ok (.absentDigest theirs)
  | .journal _ => .ok (.journal ((List.range (theirs.length / 21)).filterMap fun i =>
      JournalEntry.decode ((theirs.drop (21 * i)).take 21)))
  | .resultsDigest _ => .ok (.resultsDigest theirs)
  | .serveTick .. =>
      if theirs.length == 41 then
        let job := theirs.take 32
        .ok (.serveTick (if job == List.replicate 32 0 then none else some job) (theirs.getD 32 0 == 1)
          (number (theirs.drop 33)))
      else .error "invalid serve tick"
  | .ceremonyInput input _ => .ok (.ceremonyInput input theirs)

/-- **The reply's constructor is the message's** (plan 3.2, "the reply's constructor is checked
here"): whatever bytes the other node sends, the controller reads them as a message of the kind
it sent itself, or the session ends. -/
theorem decodeReply_kind {mine reply : PeerMsg} {theirs : Bytes} (h : decodeReply mine theirs = .ok reply) :
    reply.name = mine.name := by
  cases mine <;> simp only [decodeReply] at h
  all_goals first
    | (cases h; rfl)
    | (split at h
       · cases h; rfl
       · cases h)

end PeerMsg

/-! ## The database client (`handoff_client` of secret-shared-db; SECURITY_MAP A.3) -/

/-- What authorises a read. -/
inductive ReadAuthority where
  /-- The account's own row (a reserved id; no application request). -/
  | account
  /-- The application's signed request (a file). -/
  | request (path : String)

def ReadAuthority.args : ReadAuthority → List String
  | .account => ["--account"]
  | .request path => ["--request", path]

/-- What authorises a write. -/
inductive WriteAuthority where
  | account
  /-- The application's signed request, for contact `id`. -/
  | request (path : String) (id : Nat)
  /-- A signup token (a file), for the contact `id` it names. -/
  | signupToken (path : String) (id : Nat)

def WriteAuthority.args : WriteAuthority → List String
  | .account => ["--account"]
  | .request path id => ["--request", path, "--id", toString id]
  | .signupToken path id => ["--signup-token", path, "--id", toString id]

/-- **To the database client**: each is one command line, or one input file the client reads, in
its scratch directory (`SIGNAL_DB_WORK`). Each party runs the client itself; its key shares never
leave it (they come back in output files, read by `Channels.readKeyShares` / `readDealt` as
`Secret`). `name` tells apart the files of different reads and writes. -/
inductive DbCall where
  /-- **P.** Read this party's shares and the blobs of the ids `auth` covers. -/
  | read (auth : ReadAuthority) (name : String)
  /-- **P.** Compute this party's parity shares of that read. -/
  | parity (name : String)
  /-- **P (input file).** The other party's parity shares (`PeerMsg.parity`). -/
  | theirParity (name : String) (file : Bytes)
  /-- **P.** Check the nodes' signatures on the other party's reports. -/
  | verifySignatures (name : String)
  /-- **P.** Sum the parity shares (the sums must be zero). -/
  | paritySum (name : String)
  /-- **P.** Combine this party's summands into its key shares (output: `Secret`). -/
  | combine (name : String)
  /-- **P.** Deal this party's half of a new key for contact `id` under a signup token (a file),
  with the session's joint randomness (16 bytes). -/
  | deal (token : String) (id : Nat) (session : Bytes)
  /-- **P (input file, T10).** A sealed state: nonce ‖ check ‖ ciphertext (‖ kinds ‖ count). -/
  | blob (name : String) (bytes : Bytes)
  /-- **P (T10).** Store blob `name` as `version` under `auth`. -/
  | writeBlob (name : String) (auth : WriteAuthority) (version : Nat)
  /-- **O (input file).** A received message's text (`receivedText`), to be read as a token. -/
  | receivedToken (text : String)
  /-- **P.** The id the received token names (fixed-width tokens only). -/
  | tokenId
  /-- **O (input file).** That token, kept for the deal and the first write of contact `id`. -/
  | keptToken (id : Nat) (text : String)
  /-- **P.** The application's signed delete request (`db-delete`). -/
  | delete (request : String)

/-- A command line, or a file for the client to read. -/
inductive DbWire where
  | command (args : List String)
  | file (path : String) (bytes : Bytes)

namespace DbCall

/-- The command's name (for its log line). -/
def command : DbCall → String
  | .read .. => "read" | .parity _ => "parity" | .theirParity .. => "(file)" | .verifySignatures _ => "verify-signatures"
  | .paritySum _ => "parity-sum" | .combine _ => "combine" | .deal .. => "deal" | .blob .. => "(file)"
  | .writeBlob .. => "write-blob" | .receivedToken _ => "(file)" | .tokenId => "token-id" | .keptToken .. => "(file)"
  | .delete _ => "delete"

/-- The client's output file of a call (in the scratch directory), named as the controller reads it. -/
def readOut (name : String) : String := s!"{name}-read.json"
def parityMine (name : String) : String := s!"{name}-parity-mine.json"
def parityTheirs (name : String) : String := s!"{name}-parity-theirs.json"
def sumsOut (name : String) : String := s!"{name}-sums.json"
def sharesOut (name : String) : String := s!"{name}-shares.json"
def dealOut (id : Nat) : String := s!"deal-{id}.json"
def writeOut (name : String) : String := s!"write-{name}.json"
def deleteOut : String := "delete.json"
/-- A kept token (`keptToken`), named again by `deal` and `WriteAuthority.signupToken`. -/
def keptTokenFile (id : Nat) : String := s!"token-{id}"

/-- The encoding: `setting` gives `SIGNAL_DB_NETWORK`, `_KEY`, `_WORK` (or the error that it is
missing); `party` is this party's index. -/
def encode (party : String) (setting : String → Except String String) (call : DbCall) : Except String DbWire := do
  let work (file : String) : Except String String := do pure s!"{← setting "SIGNAL_DB_WORK"}/{file}"
  let partyArgs : Except String (List String) := do
    pure ["--network", ← setting "SIGNAL_DB_NETWORK", "--key", ← setting "SIGNAL_DB_KEY", "--party", party]
  match call with
  | .read auth name => do
      let out ← work (readOut name)
      pure (.command (["read"] ++ (← partyArgs) ++ auth.args ++ ["--out", out]))
  | .parity name => pure (.command ["parity", "--summands", ← work (readOut name), "--out", ← work (parityMine name)])
  | .theirParity name file => pure (.file (← work (parityTheirs name)) file)
  | .verifySignatures name => do
      let theirs ← work (parityTheirs name)
      pure (.command ["verify-signatures", "--network", ← setting "SIGNAL_DB_NETWORK", "--reports", theirs])
  | .paritySum name =>
      pure (.command ["parity-sum", "--mine", ← work (parityMine name), "--theirs", ← work (parityTheirs name),
        "--out", ← work (sumsOut name)])
  | .combine name =>
      pure (.command ["combine", "--summands", ← work (readOut name), "--parity-sums", ← work (sumsOut name),
        "--out", ← work (sharesOut name)])
  | .deal token id session =>
      pure (.command (["deal"] ++ (← partyArgs) ++ ["--signup-token", token, "--id", toString id,
        "--session", hex session, "--out", ← work (dealOut id)]))
  | .blob name bytes => pure (.file (← work s!"blob-{name}") bytes)
  | .writeBlob name auth version =>
      pure (.command (["write-blob"] ++ (← partyArgs) ++ auth.args ++ ["--version", toString version,
        "--blob-file", ← work s!"blob-{name}", "--out", ← work (writeOut name)]))
  | .receivedToken text => pure (.file (← work "token-received") text.toUTF8.data.toList)
  | .tokenId => pure (.command ["token-id", "--signup-token", ← work "token-received", "--require-fixed"])
  | .keptToken id text => pure (.file (← work (keptTokenFile id)) text.toUTF8.data.toList)
  | .delete request => do
      let out ← work deleteOut
      pure (.command (["delete"] ++ (← partyArgs) ++ ["--request", request, "--out", out]))

end DbCall

/-! ## The node daemon (standard output; node_daemon/README.md) -/

/-- A two-party session's report (its last line on standard output). -/
structure FinalReport where
  passed : Bool
  certificateVerified : Bool
  responsesCompleted : Nat
  bytesRevealed : Nat
  messagesDelivered : Nat
  keepalives : Nat
  envelopes : List (Nat × Nat)
  received : List (Nat × String)
  refused : Nat
  privateReceiveParsingUsed : Bool
  circuits : Nat
  circuitSends : List (Nat × Nat)
  circuitLabels : List (String × String)
  results : List Recovery.Entry
  recoveryUsed : Bool
  recovery : List String
  unknown : List Nat
  notYetReadable : List Nat
  error : String

/-- One job's result in the long-lived session. -/
structure JobResult where
  job : String
  results : List Recovery.Entry
  unknown : List Nat
  notYetReadable : List Nat
  recovery : List String
  messages : Nat
  delivered : Nat
  milliseconds : Nat
  sessionMessages : Nat
  sessionJobs : Nat

/-- **To the node daemon or the operator: one line on standard output.** -/
inductive DaemonLine where
  /-- **P.** The long-lived session's connections are open (T11's channel). -/
  | ready (connections : Nat)
  /-- **P (T11).** A job's per-id results, as both controllers agreed them (`resultsDigest`). -/
  | jobResult (result : JobResult)
  /-- **O.** A contact signed up (`receivedText` named its id), as soon as it is stored. -/
  | signup (id : Nat)
  /-- **P (T11).** The session's report. -/
  | finalReport (report : FinalReport)
  /-- **P.** `recovery-check`: the unit check's outcome. -/
  | recoveryCheck (passed : Bool) (checks : Nat) (failed : List String)
  /-- **P.** `policy-check`: the reveal policy's property test (`ReceiveTest.checks`, T1). -/
  | policyCheck (passed : Bool) (checks : Nat) (failed : List String)
  /-- **P.** `ceremony`: a stage's outcome (its child session's report). -/
  | ceremonyStage (stage : String) (passed : Bool) (directory : String) (error : String)
  /-- **P.** `db-delete`: the nodes confirmed the delete. -/
  | deleted
  /-- **P.** `request-shape` (circuit production only): a request kernel's name and shape. -/
  | kernelShape (parts : List String)

def DaemonLine.encode : DaemonLine → String
  | .ready connections => (Json.mkObj [("event", toJson "ready"), ("connections", toJson connections)]).compress
  | .jobResult r => (Json.mkObj [("job", toJson r.job), ("status", toJson "completed"),
      ("results", toJson (r.results.map entryJson)),
      ("unknown", toJson (r.unknown.map toString)), ("not_yet_readable", toJson (r.notYetReadable.map toString)),
      ("recovery", toJson r.recovery), ("messages", toJson r.messages), ("delivered", toJson r.delivered),
      ("milliseconds", toJson r.milliseconds), ("session_messages", toJson r.sessionMessages),
      ("session_jobs", toJson r.sessionJobs)]).compress
  | .signup id => (Json.mkObj [("event", toJson "signup"), ("id", toJson (toString id))]).compress
  | .finalReport r => (Json.mkObj [("passed", toJson r.passed), ("certificate_verified", toJson r.certificateVerified),
      ("responses_completed", toJson r.responsesCompleted), ("bytes_revealed", toJson r.bytesRevealed),
      ("messages_delivered", toJson r.messagesDelivered), ("keepalives", toJson r.keepalives),
      ("envelopes", toJson (r.envelopes.map fun (kind, size) => [kind, size])),
      ("received", toJson (r.received.map fun (contact, text) => [toString contact, text])), ("refused", toJson r.refused),
      ("private_receive_parsing_used", toJson r.privateReceiveParsingUsed), ("circuits", toJson r.circuits),
      ("circuit_sends", toJson (r.circuitSends.map fun (contact, index) => [toString contact, toString index])),
      ("circuit_labels", toJson (r.circuitLabels.map fun (user, password) => [user, password])),
      ("results", toJson (r.results.map entryJson)), ("recovery_used", toJson r.recoveryUsed),
      ("recovery", toJson r.recovery), ("unknown", toJson (r.unknown.map toString)),
      ("not_yet_readable", toJson (r.notYetReadable.map toString)), ("error", toJson r.error)]).compress
  | .recoveryCheck passed checks failed | .policyCheck passed checks failed =>
      (Json.mkObj [("passed", toJson passed), ("checks", toJson checks), ("failed", toJson failed)]).compress
  | .ceremonyStage stage passed directory error => (Json.mkObj [("ceremony", toJson stage), ("passed", toJson passed),
      ("directory", toJson directory), ("error", toJson error)]).compress
  | .deleted => "{\"deleted\":true}"
  | .kernelShape parts => " ".intercalate ("kernel" :: parts)

/-! ## The event record (`SIGNAL_RECORD`; real_signal/REAL_TEST_PLAN.md, "Recording") -/

/-- Where the bytes passed over (unrevealed) go. -/
inductive PassedTo where
  | envelope | prekeyResponse | nowhere

def PassedTo.text : PassedTo → String
  | .envelope => "engines (delivered envelope)"
  | .prekeyResponse => "engines (prekey response)"
  | .nowhere => "nowhere"

/-- **To this node's event record** (one JSON line per event, with this party's clock; class S,
values P or O only: by type, no secret reaches it). One constructor per kind of event. -/
inductive RecordEvent where
  /-- The server's certificate chain and the checker's verdict. -/
  | serverCertificate (hostname trust : String) (scheme : Nat) (transcript : Bytes) (chain : List Bytes)
      (accepted : Bool) (checkerError : String)
  | connect (endpoint port hostname : String) (authenticated : Bool) (proxy : Option String) (circuits : Nat)
      (official : Bool)
  | connected
  | handshake (certificateVerified finishedVerified : Bool)
  /-- **P.** A public record this node sends (upgrade, replies, keepalives, pings). -/
  | sentPublic (connection : Nat) (bytes : Bytes)
  | envelopeRefused (reason : String)
  | envelope (kind size : Nat) (newContact : Option Nat)
  /-- An authenticated record's length (`revealRange` probe). -/
  | record (connection handle length : Nat)
  /-- Bytes passed over unrevealed (T1). -/
  | passedOver (handle offset count : Nat) (to : PassedTo)
  /-- **O.** Revealed server bytes (T1). -/
  | revealed (handle offset : Nat) (bytes : Bytes)
  /-- **P (T7, T8).** A private request as the controllers know it: its private slots are zero. -/
  | sentPrivate (connection contact id timestamp : Nat) (template : Bytes)
  /-- **P (T8).** The prekey fetch's template (private slots zero). -/
  | sentPrekeyFetch (connection contact id : Nat) (template : Bytes)
  | recovery (note : String)
  | response (contact message id : Nat) (answered : Bool) (status : Nat) (retryAfter : Option Nat)
  | serverRequest (deliveredMessage refused answered : Bool)
  | closedWhileWaiting
  | ceremonyResponse (request : String) (status : Nat)
  /-- **P.** The registration request with its two private slots zero, and its public mask. -/
  | ceremonyRegister (id : Nat) (frame : Bytes) (credentialSlot recoverySlot payloadAt : Nat) (mask : Bytes)

/-- The event's name and fields (`time_ms` is added by `Channels.record`). -/
def RecordEvent.encode : RecordEvent → String × List (String × Json)
  | .serverCertificate hostname trust scheme transcript chain accepted checkerError =>
      ("server-certificate", [("hostname", toJson hostname), ("trust", toJson trust), ("scheme", toJson scheme),
        ("transcript_sha256", toJson (hex transcript)), ("chain_der_hex", toJson (chain.map hex)),
        ("accepted", toJson accepted), ("checker_error", toJson checkerError)])
  | .connect endpoint port hostname authenticated proxy circuits official =>
      ("connect", [("endpoint", toJson endpoint), ("port", toJson port), ("hostname", toJson hostname),
        ("socket", toJson (if authenticated then "authenticated" else "unauthenticated")), ("proxy", toJson proxy),
        ("circuits", toJson circuits), ("profile", toJson (if official then "libsignal" else "legacy"))])
  | .connected => ("connected", [])
  | .handshake certificate finished =>
      ("handshake", [("certificate_verified", toJson certificate), ("finished_verified", toJson finished)])
  | .sentPublic connection bytes => ("sent-public", [("connection", toJson connection), ("hex", toJson (hex bytes))])
  | .envelopeRefused reason => ("envelope-refused", [("reason", toJson reason)])
  | .envelope kind size newContact => ("envelope", [("type", toJson kind), ("content_bytes", toJson size),
      ("outcome", toJson (match newContact with | some id => s!"new contact {id}" | none => "refused"))])
  | .record connection handle length =>
      ("record", [("connection", toJson connection), ("handle", toJson handle), ("content_bytes", toJson length)])
  | .passedOver handle offset count to => ("passed-over", [("handle", toJson handle), ("offset", toJson offset),
      ("bytes", toJson count), ("to", toJson to.text)])
  | .revealed handle offset bytes =>
      ("revealed", [("handle", toJson handle), ("offset", toJson offset), ("hex", toJson (hex bytes))])
  | .sentPrivate connection contact id timestamp template =>
      ("sent-private", sendFields connection contact id timestamp template)
  | .sentPrekeyFetch connection contact id template =>
      ("sent-private-prekey-fetch", sendFields connection contact id 0 template)
  | .recovery note => ("recovery", [("note", toJson note)])
  | .response contact message id answered status retryAfter => ("response", [("contact", toJson (toString contact)),
      ("message", toJson message), ("request_id", toJson (toString id)), ("answered", toJson answered),
      ("status", toJson status), ("retry_after", toJson retryAfter)])
  | .serverRequest delivered refused answered => ("server-request", [("delivered_message", toJson delivered),
      ("refused", toJson refused), ("answered", toJson answered)])
  | .closedWhileWaiting => ("closed", [("while", toJson "waiting for messages")])
  | .ceremonyResponse request status => ("ceremony-response", [("request", toJson request), ("status", toJson status)])
  | .ceremonyRegister id frame credentialSlot recoverySlot payloadAt mask =>
      ("ceremony-register", [("request_id", toJson (toString id)), ("frame_hex", toJson (hex frame)),
        ("credential_slot", toJson credentialSlot), ("recovery_slot", toJson recoverySlot),
        ("payload_at", toJson payloadAt), ("mask_hex", toJson (hex mask))])
where
  sendFields (connection contact id timestamp : Nat) (template : Bytes) : List (String × Json) :=
    [("connection", toJson connection), ("contact", toJson (toString contact)), ("request_id", toJson (toString id)),
      ("timestamp", toJson timestamp), ("frame_bytes", toJson template.length), ("template_hex", toJson (hex template))]

/-! ## Standard error -/

/-- **To standard error** (the operator's log; class S: P or O values only). -/
inductive LogLine where
  /-- TEST hooks set in the environment but ignored (started without `--test`). -/
  | hooksIgnored (names : List String)
  /-- The database client failed; its standard error. -/
  | dbClientFailed (command stderr : String)
  /-- **O.** Revealed server bytes (TEST trace, `SIGNAL_LOCAL_TRACE`). -/
  | revealed (bytes : Bytes)
  | deviceRefresh (sessions : Nat)
  | recovery (note : String)
  | serveEnded (jobs messages : Nat)

def LogLine.encode : LogLine → String
  | .hooksIgnored names => s!"TEST hooks ignored (the controller was not started with --test): {", ".intercalate names}"
  | .dbClientFailed command stderr => s!"database client {command}: {stderr}"
  | .revealed bytes => s!"revealed {hex bytes}"
  | .deviceRefresh sessions => s!"device refresh: {sessions} sessions established"
  | .recovery note => s!"recovery: {note}"
  | .serveEnded jobs messages => s!"serve: {jobs} jobs, {messages} messages; the session ends between jobs"

/-! ## Own disk -/

/-- **To the notify's journal** (`SIGNAL_NOTIFY_JOURNAL`, appended; class S, P values): a settled
result of notify `notify`. -/
structure JournalLine where
  notify : String
  entry : Recovery.Entry

def JournalLine.encode (line : JournalLine) : String := Recovery.journalLine line.notify line.entry

/-- **Public files this node writes to its own disk** (class S, P values), in a directory the
caller names (the ceremony's). -/
inductive PublicFile where
  /-- The worker hosts of the ceremony's child sessions. -/
  | ceremonyHosts (hosts : List String)
  /-- A ceremony stage's child session: its standard error, its report. -/
  | ceremonyLog (stage : String) (stderr : String)
  | ceremonyReport (stage : String) (stdout : String)
  /-- An operator's input that the OTHER node was given (`PeerMsg.ceremonyInput`). -/
  | ceremonyInput (input : CeremonyInput) (text : String)
  /-- The registered account's public ids. -/
  | ceremonyAccount (number aci pni session : String)
  /-- The sender certificate (base64). -/
  | senderCertificate (base64 : String)

def PublicFile.name : PublicFile → String
  | .ceremonyHosts _ => "hosts"
  | .ceremonyLog stage _ => s!"{stage}.log"
  | .ceremonyReport stage _ => s!"{stage}.json"
  | .ceremonyInput input _ => input.fileName
  | .ceremonyAccount .. => "account.json"
  | .senderCertificate _ => "certificate.b64"

def PublicFile.contents : PublicFile → String
  | .ceremonyHosts hosts => String.join (hosts.map (· ++ "\n"))
  | .ceremonyLog _ stderr => stderr
  | .ceremonyReport _ stdout => stdout
  | .ceremonyInput _ text => text ++ "\n"
  | .ceremonyAccount number aci pni session => (Json.mkObj [("number", toJson number), ("aci", toJson aci),
      ("pni", toJson pni), ("verification_session", toJson session)]).compress ++ "\n"
  | .senderCertificate base64 => base64 ++ "\n"

/-- **This party's secret files** (class S; plan 4.2 rows 1, 3, 4). Only the name: the secret goes
to `Channels.saveShare` beside it, which writes it with mode 0600. -/
inductive ShareFile where
  /-- The ceremony's XOR share of the account password. -/
  | password
  /-- The ceremony's XOR share of the recovery password. -/
  | recovery
  /-- The XOR share of the socket credentials (account id, password). -/
  | credentials
  /-- TEST store (`SIGNAL_LOCAL_STORE`): a contact's key share, then its public stored state. -/
  | testStore (id : Nat)

def ShareFile.name : ShareFile → String
  | .password => "password.share"
  | .recovery => "recovery.share"
  | .credentials => "credentials.share"
  | .testStore id => toString id

/-! ## Local tools and child processes -/

/-- **To the certificate checker** (`public_auth NAME TRUST SCHEME HASH SIGNATURE CHAIN...`; P: the
server's public certificate chain and the handshake's public transcript hash). -/
structure CertificateQuery where
  hostname : String
  trust : String
  scheme : Nat
  transcript : Bytes
  signature : Bytes
  chain : List Bytes

def CertificateQuery.args (q : CertificateQuery) : List String :=
  [q.hostname, q.trust, toString q.scheme, hex q.transcript, hex q.signature] ++ q.chain.map hex

/-- **A ceremony stage's two-party session** (`ceremony`): the controller started as a child with
these arguments and environment (P: paths and settings; this node's credentials share is passed
as a file's path, `SIGNAL_LOCAL_CREDENTIALS_FILE`, never as its value; plan 4.2 row 3). -/
structure ChildSession where
  controller : String
  args : List String
  env : List (String × String)

/-! ## The check that no message carries a secret (T9 by type; `Messages.noSecret` of plan S5) -/

namespace Messages
open Lean Elab Command

/-- Fails unless no constructor of an inductive type declared in the current file mentions a
forbidden type (this party's `Secret`, an engine handle, a worker buffer handle), directly or
through any type of this repository it uses (followed transitively; Lean's own types cannot
mention them). -/
def checkPublic : CommandElabM Unit := do
  let env ← getEnv
  let forbidden : List Name :=
    ["TlsMpc.Node.Secret", "TlsMpc.Node.Handle", "TlsMpc.TlsWorker.BufferHandle"].map String.toName
  let ours (n : Name) : Bool := match env.getModuleIdxFor? n with
    | none => true
    | some idx => match env.header.moduleNames[idx.toNat]? with
      | some m => m.getRoot == `TlsMpc
      | none => false
  let roots := env.constants.foldStage2 (fun acc n info => if info.isInductive then n :: acc else acc) []
  if roots.isEmpty then throwError "checkPublic: no inductive type declared in this file"
  let mut stack : List (Name × Name) := roots.map fun n => (n, n)
  let mut seen : NameSet := {}
  let mut fuel := 100000
  while true do
    match stack with
    | [] => break
    | (n, root) :: rest =>
      stack := rest
      fuel := fuel - 1
      if fuel == 0 then throwError "checkPublic: too many constants"
      if forbidden.contains n then
        throwError m!"checkPublic: {root} reaches {n}: a message may not carry a secret or an engine handle"
      if seen.contains n || !ours n then continue
      seen := seen.insert n
      let some info := env.find? n | continue
      let next : List Name := match info with
        | .inductInfo v => v.ctors ++ v.type.getUsedConstants.toList
        | .defnInfo v => v.type.getUsedConstants.toList ++ v.value.getUsedConstants.toList
        | other => other.type.getUsedConstants.toList
      stack := next.map (fun m => (m, root)) ++ stack

run_cmd checkPublic

end Messages
end TlsMpc.Node
