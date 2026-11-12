import Lean.Data.Json
import Std.Time
import TlsMpc.TlsWorkerProcess
import TlsMpc.Node.Config
import TlsMpc.Node.Secret
import TlsMpc.Node.Messages
import TlsMpc.Node.Export
import TlsMpc.Node.Bench

/-!
# The controller's I/O module (REORGANIZATION_PLAN.md section 3.2; stages S4, S5)

**The only file of the controller with I/O primitives** (besides the worker pipe:
`TlsWorkerProcess`/`TlsWorkerPipe`/`TlsWorker`, which become `Worker.lean` and the flow API in
later stages). `scripts/lint_node.py` (check `io-baseline`) holds every other file of the
controller's import closure to its recorded count, which stage S5 brought to zero for the
controller itself.

What each channel carries is a type of `TlsMpc/Node/Messages.lean` (none has a secret field);
this file only performs it:

| Channel | Function | Message |
|---|---|---|
| the other node (worker op 39) | `exchange` | `PeerMsg` (reply of the same kind) |
| the database client | `db` (+ the readers of its output files) | `DbCall` |
| the node daemon / operator (stdout) | `report` | `DaemonLine` |
| the event record (`SIGNAL_RECORD`) | `record` | `RecordEvent` |
| standard error | `log` | `LogLine` |
| the certificate checker | `checkCertificate` | `CertificateQuery` |
| the KEM tool | `kemDecapsulate` (eliminator: the key on its stdin) | ciphertext |
| own disk: journal, public files, shares | `journal`, `writePublic`, `saveShare` (eliminator) | `JournalLine`, `PublicFile`, `ShareFile` |
| a ceremony stage's child session | `runChild` | `ChildSession` |
| the process: clock, sleep, randomness, environment | `clock`, `monotonic`, `sleep`, `random`, `Config.read` | — |

Inbound (read here, typed): the configuration (`Config.read`, the ONE reader of the environment),
the export file (scaffolding), the application's signed request and message, the long-lived
session's job and stop files, the journal, the ceremony's inputs, the database client's output
files (key shares as `Secret`), this party's share files.

The implementations are in `Channels.Real`; the controller uses the record `Channels` built once by
`Channels.real` (plan 3.2), and the subcommands that run before a configuration exists
(`ceremony`, `db-delete`, `recovery-check`, `request-shape`, `parse-bench`) call `Channels.Real`
directly. No emitter imports this module.
-/

namespace TlsMpc.Node.Channels.Real
open TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Node
open Lean (Json toJson)

private def hex (bytes : Bytes) : String := TlsWorkerProcess.hex bytes

/-- An I/O step whose failure is the session's (an error string in `M`), not an exception. -/
def inBand (step : IO α) : M α := ExceptT.mk do
  match ← step.toBaseIO with
  | .ok value => pure (.ok value)
  | .error e => pure (.error (toString e))

/-- A step of `M` as `IO` (its error string as a user error): for the subcommands. -/
def runIO (step : M α) : IO α := do
  match ← step.run with
  | .ok value => pure value
  | .error e => throw (IO.userError e)

/-! ### The process -/

/-- This node's wall clock, milliseconds since the Unix epoch (agreement: `Policy.Clock`). -/
def clock : IO Nat := do
  pure (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val.toNat

/-- A monotonic clock in milliseconds (deadlines, durations). -/
def monotonic : IO Nat := IO.monoMsNow

def sleep (ms : Nat) : IO Unit := IO.sleep (UInt32.ofNat ms)

/-- `n` bytes from the operating system's generator: this party's own randomness (plan rule 5). -/
def random (n : Nat) : IO (Secret Bytes) := do
  pure (Secret.hide (← IO.getRandomBytes (USize.ofNat n)).data.toList)

/-- `parse-bench` (measurement only). -/
def benchIO : Bench.BenchIO := { zero := IO.rand 0 0, clock := IO.monoNanosNow, say := IO.println }

/-! ### Standard output, standard error, the event record -/

/-- One line to the node daemon or the operator (flushed: the daemon reads line by line). -/
def report (line : DaemonLine) : IO Unit := do
  IO.println line.encode
  (← IO.getStdout).flush

def log (line : LogLine) : IO Unit := IO.eprintln line.encode

/-- `SIGNAL_RECORD=FILE` (real_signal/REAL_TEST_PLAN.md, "Recording"): one JSON line per event
with this party's clock in milliseconds, appended to FILE. Only `RecordEvent`s, so only values
this controller holds in the clear: nothing secret-shared reaches it. -/
def record (file : Option String) (event : RecordEvent) : IO Unit := do
  let some path := file | return
  let now ← clock
  let (name, fields) := event.encode
  let line := (Json.mkObj ([("time_ms", toJson now), ("event", toJson name)] ++ fields)).compress
  IO.FS.withFile path .append (fun handle => handle.putStrLn line)

/-! ### The other node -/

/-- The worker's exchange (operation 39) of bytes of any length: the length (4 bytes), then
chunks of at most 60000 bytes; the shorter side is padded with zeros. -/
def swapBytes (rpc : TlsWorker.Rpc) (mine : Bytes) : M Bytes := do
  let size ← rpc.call .exchange (uint 4 mine.length)
  insist (size.length == 4) "invalid exchange reply"
  let width := max mine.length (number size)
  let mut rest := mine ++ List.replicate (width - mine.length) 0
  let mut theirs : Bytes := []
  while !rest.isEmpty do
    theirs := theirs ++ (← rpc.call .exchange (rest.take 60000))
    rest := rest.drop 60000
  pure (theirs.take (number size))

/-- **To the other node**: `msg` through the worker's control link; the other node's message of
the same kind back (`PeerMsg.decodeReply_kind`). -/
def exchange (rpc : TlsWorker.Rpc) (msg : PeerMsg) : M PeerMsg := do
  let theirs ← if msg.sized then swapBytes rpc msg.encode else rpc.call .exchange msg.encode
  liftResult (msg.decodeReply theirs)

/-! ### The database client -/

/-- The client's exit status and output (its standard error is logged by the caller). -/
structure DbOutcome where
  ok : Bool
  stdout : String
  stderr : String

/-- A setting of the database client (`SIGNAL_DB_*`), or the error that it is missing. -/
def dbSetting (config : Node.Config.Config) (context : String) (name : String) : Except String String :=
  let field : Config.Database → Option String := match name with
    | "SIGNAL_DB_NETWORK" => (·.network) | "SIGNAL_DB_KEY" => (·.key) | "SIGNAL_DB_WORK" => (·.work)
    | "SIGNAL_DB_REQUEST" => (·.request) | "SIGNAL_DB_TOKENS" => (·.tokens) | _ => fun _ => none
  Config.required name (config.database.bind field) context

/-- **To the database client**: one command (run, its outcome returned) or one input file
(written). `context`: how a missing setting is reported. -/
def db (config : Node.Config.Config) (party : String) (call : DbCall) (context : String := " with SIGNAL_DB_CLIENT") : M DbOutcome := do
  match ← liftResult (call.encode party (dbSetting config context)) with
  | .file path bytes =>
    liftM (IO.FS.writeBinFile path ⟨bytes.toArray⟩ : IO Unit)
    pure { ok := true, stdout := "", stderr := "" }
  | .command args =>
    let some tool := config.database.map (·.client) | throw "no database client"
    let out ← liftM (IO.Process.output { cmd := tool, args := args.toArray })
    pure { ok := out.exitCode == 0, stdout := out.stdout, stderr := out.stderr }

/-- A file of the client's scratch directory. -/
def dbFile (config : Node.Config.Config) (file : String) (context : String := " with SIGNAL_DB_CLIENT") : M String := do
  pure s!"{← liftResult (dbSetting config context "SIGNAL_DB_WORK")}/{file}"

/-- This party's parity shares of read `name` (`DbCall.parity`'s output; `PeerMsg.parity`). -/
def readParity (config : Node.Config.Config) (name : String) : M Bytes := do
  pure (← liftM (IO.FS.readBinFile (← dbFile config (DbCall.parityMine name)) : IO ByteArray)).data.toList

/-- What a read returned that the controller uses (public): per id in the client's order, its
blob (version, hex) if it has a well-formed one, and the ids not served until the next epoch.
This party's summands, also in the client's read output, are not kept. -/
structure DbRead where
  entries : List (String × Option (Nat × String))
  notYetReadable : List String

/-- An id's blob, as the client listed it (the first entry with that id). -/
def DbRead.blob (read : DbRead) (contact : Nat) : Option (Nat × String) :=
  ((read.entries.find? (·.1 == toString contact)).map (·.2)).join

def readDbRead (config : Node.Config.Config) (name : String) : M DbRead := do
  let json ← liftResult (Json.parse (← liftM (IO.FS.readFile (← dbFile config (DbCall.readOut name)) : IO String)))
  let entries := ((json.getObjValAs? (Array Json) "ids").toOption.getD #[]).toList.filterMap fun entry =>
    (entry.getObjValAs? String "id").toOption.map fun id =>
      (id, (entry.getObjVal? "blob").toOption.bind fun b =>
        match b.getObjValAs? Nat "version", b.getObjValAs? String "hex" with
        | .ok version, .ok hex => some (version, hex)
        | _, _ => none)
  pure { entries, notYetReadable := ((json.getObjValAs? (Array String) "not_yet_readable").toOption.getD #[]).toList }

/-- The database client's combined shares (`combine --out`): per id (as the client writes it),
this party's share of the contact's key. Plan 4.2 row 1. -/
def readKeySharesFile (path : System.FilePath) : IO (List (String × Secret Bytes)) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let entries := ((json.getObjValAs? (Array Json) "ids").toOption.getD #[]).toList
  entries.filterMapM fun entry => do
    match (entry.getObjValAs? String "id").toOption, (entry.getObjValAs? String "share").toOption with
    | some id, some hexShare => match Secret.ofHex hexShare with
      | .ok share => pure (some (id, share))
      | .error _ => throw (IO.userError "the database client's share is not hex")
    | _, _ => pure none

def readKeyShares (config : Node.Config.Config) (name : String) : M (List (String × Secret Bytes)) := do
  inBand (readKeySharesFile (← dbFile config (DbCall.sharesOut name)))

/-- The database client's `deal --out`: which nodes committed (public), and the dealt summand,
this party's share of the new key (plan 4.2 rows 1, 2). -/
def readDealtFile (path : System.FilePath) : IO (List String × Option (Secret Bytes)) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let nodes := ((json.getObjValAs? (Array String) "nodes").toOption.getD #[]).toList
  let summand ← match (json.getObjValAs? String "summand").toOption with
    | none => pure none
    | some hexShare => match Secret.ofHex hexShare with
      | .ok share => pure (some share)
      | .error _ => throw (IO.userError "the dealt summand is not hex")
  pure (nodes, summand)

def readDealt (config : Node.Config.Config) (id : Nat) : M (List String × Option (Secret Bytes)) := do
  inBand (readDealtFile (← dbFile config (DbCall.dealOut id)))

/-- Whether the nodes acknowledged write `name` (`write-blob --out`). -/
def writeAcknowledged (config : Node.Config.Config) (name : String) : M Bool := do
  let json ← liftResult (Json.parse (← liftM (IO.FS.readFile (← dbFile config (DbCall.writeOut name)) : IO String)))
  pure ((json.getObjValAs? Bool "acknowledged").toOption.getD false)

/-- Whether the nodes confirmed the delete (`delete --out`; unreadable: not yet). -/
def deleteAcknowledged (config : Node.Config.Config) : M Bool := do
  let text ← liftM (IO.FS.readFile (← dbFile config DbCall.deleteOut "") : IO String)
  pure (match Json.parse text with
    | .ok json => (json.getObjValAs? Bool "acknowledged").toOption.getD false
    | .error _ => false)

/-! ### Local tools -/

/-- **To the certificate checker** (`public_auth`): whether it printed `authenticated`, and its
standard error. -/
def checkCertificate (checker : String) (query : CertificateQuery) : IO (Bool × String) := do
  let result ← IO.Process.output { cmd := checker, args := query.args.toArray }
  pure (result.exitCode == 0 && result.stdout.trimAscii.toString == "authenticated", result.stderr.trimAscii.toString)

/-- **Eliminator: Kyber-1024 decapsulation by the KEM tool** (plan 4.1 `Channels.kemDecapsulate`):
`TOOL kem-decapsulate CIPHERTEXT_HEX`, our Kyber private key (OWN) as hex on its standard input,
the 32-byte shared secret as hex on its standard output. -/
def kemDecapsulate (tool : String) (key : Secret Bytes) (ciphertext : Bytes) : IO (Except String (Secret Bytes)) := do
  let out ← IO.Process.output { cmd := tool, args := #["kem-decapsulate", hex ciphertext] } (some (hex key.expose ++ "\n"))
  if out.exitCode != 0 then return .error "decapsulation failed"
  match Secret.ofHex out.stdout.trimAscii.toString with
  | .ok secret => return if secret.length == 32 then .ok secret else .error "decapsulated secret shape"
  | .error _ => return .error "decapsulated secret shape"

/-- **A ceremony stage's child session**: run to completion; its exit code and output. -/
def runChild (child : ChildSession) : IO IO.Process.Output :=
  let env : Array (String × Option String) := (child.env.map (fun (key, value) => (key, some value))).toArray
  IO.Process.output { cmd := child.controller, args := child.args.toArray, env }

/-! ### Own disk -/

/-- **Eliminator: a secret to this node's own disk** (plan 4.1 `Channels.saveShare`): its hex,
written to a temporary file readable by this user only, then renamed into place. With
`publicTail`: bytes stored after it in the same file (the TEST store's version and sealed state). -/
def saveShareAt (path : System.FilePath) (share : Secret Bytes) (publicTail : Bytes := []) : IO Unit := do
  let temporary := path.toString ++ ".partial"
  IO.FS.writeFile temporary ""
  IO.setAccessRights temporary { user := { read := true, write := true } }
  IO.FS.writeFile temporary (hex (share.expose ++ publicTail) ++ "\n")
  IO.FS.rename temporary path

/-- `saveShareAt` of share file `file` in `directory`. -/
def saveShare (directory : System.FilePath) (file : ShareFile) (share : Secret Bytes) (publicTail : Bytes := []) : IO Unit :=
  saveShareAt (directory / file.name) share publicTail

/-- A secret from this node's own disk (`saveShare`'s format); `none` when the file is absent. -/
def loadShare (path : System.FilePath) : IO (Option (Secret Bytes)) := do
  if !(← path.pathExists) then return none
  match Secret.ofHex (← IO.FS.readFile path).trimAscii.toString with
  | .ok share => pure (some share)
  | .error _ => throw (IO.userError s!"{path} does not hold hex")

/-- TEST store (`SIGNAL_LOCAL_STORE`): a contact's file is this party's 32-byte key share, then
the public version and sealed state (the caller checks the shape). -/
def loadStored (directory : System.FilePath) (id : Nat) : IO (Option (Secret Bytes × Bytes)) := do
  let path := directory / (ShareFile.testStore id).name
  if !(← path.pathExists) then return none
  match Node.Bytes.fromHex (← IO.FS.readFile path).trimAscii.toString with
  | .ok bytes => pure (some (Secret.hide (bytes.take 32), bytes.drop 32))
  | .error _ => throw (IO.userError s!"{path} does not hold hex")

/-- A public file to own disk. -/
def writePublic (directory : System.FilePath) (file : PublicFile) : IO Unit :=
  IO.FS.writeFile (directory / file.name) file.contents

def ensureDirectory (path : System.FilePath) : IO Unit := IO.FS.createDirAll path

/-- **To the notify's journal**: one settled result, appended. -/
def journal (path : String) (line : JournalLine) : IO Unit :=
  IO.FS.withFile (path : System.FilePath) .append (fun handle => handle.putStrLn line.encode)

/-- The settled entries of notify `notify` in the journal at `path` (none when it is absent). -/
def readJournal (path : String) (notify : String) : IO (List JournalEntry) := do
  let text ← if ← (path : System.FilePath).pathExists then IO.FS.readFile path else pure ""
  pure (Recovery.journalEntries notify text)

/-! ### Inbound files -/

/-- A JSON file (the node daemon's configuration, for `ceremony`). -/
def readJson (path : String) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

/-- The export file (scaffolding: the account's exported state; `Export`'s parsers). -/
def readExport (path : String) := do pure (Export.readExport (← IO.FS.readFile path))
def readSelf (path : String) := do pure (Export.readSelf (← IO.FS.readFile path))
def readReceive (path : String) := do pure (Export.readReceive (← IO.FS.readFile path))

/-- The application's message text (`SIGNAL_NOTIFY_MESSAGE_FILE`, a job's message file). -/
def readMessage (path : String) : IO String := IO.FS.readFile path

/-- The application's signed request, as far as the controller reads it: the ids (decimal) and
the hex of the message's SHA-256 (empty when missing). -/
structure SignedRequest where
  ids : List Nat
  messageHash : String

def readRequest (path : String) : IO (Except String SignedRequest) := do
  let text ← IO.FS.readFile path
  pure (do
    let request ← Json.parse text
    pure { ids := ((request.getObjValAs? (Array String) "ids").toOption.getD #[]).toList.filterMap String.toNat?,
           messageHash := (request.getObjValAs? String "message_hash").toOption.getD "" })

/-- A job of the long-lived session (`DIR/job.json`, written whole by the daemon). -/
structure Job where
  name : String
  request : String
  message : String
  journal : String

/-- The job the daemon handed over in `directory`, if any (unreadable: none). -/
def nextJob (directory : String) : IO (Option Job) := do
  let path := (directory : System.FilePath) / "job.json"
  if ← path.pathExists then
    let text ← IO.FS.readFile path
    pure (match Json.parse text with
      | .ok json => match json.getObjValAs? String "job", json.getObjValAs? String "request",
          json.getObjValAs? String "message", json.getObjValAs? String "journal" with
        | .ok name, .ok request, .ok message, .ok journal => some { name, request, message, journal }
        | _, _, _, _ => none
      | .error _ => none)
  else pure none

/-- Whether the daemon asks the long-lived session to end (`DIR/stop`). -/
def stopAsked (directory : String) : IO Bool := ((directory : System.FilePath) / "stop").pathExists

/-- An operator's ceremony input on this node (trimmed; empty when absent). -/
def ceremonyFile (directory : System.FilePath) (input : CeremonyInput) : IO String := do
  let path := directory / input.fileName
  if ← path.pathExists then pure (← IO.FS.readFile path).trimAscii.toString else pure ""

end TlsMpc.Node.Channels.Real

namespace TlsMpc.Node
open TlsMpc.TlsWire TlsMpc.TlsClient

/-- **The channel record** (plan 3.2): every channel of a two-party session. The session code
reaches the outside only through it (and the worker pipe). Built once by `Channels.real`. -/
structure Channels where
  /-- The other node (the worker's control link): a message, and theirs of the same kind. -/
  exchange : TlsWorker.Rpc → PeerMsg → M PeerMsg
  /-- The database client: a command or an input file. -/
  db : DbCall → M Channels.Real.DbOutcome
  /-- The database client's output files. -/
  readParity : String → M Bytes
  readDbRead : String → M Channels.Real.DbRead
  readKeyShares : String → M (List (String × Secret Bytes))
  readDealt : Nat → M (List String × Option (Secret Bytes))
  writeAcknowledged : String → M Bool
  /-- A path in the client's scratch directory (for a kept token). -/
  dbFile : String → M String
  /-- The node daemon (stdout). -/
  report : DaemonLine → IO Unit
  /-- The event record (`SIGNAL_RECORD`). -/
  record : RecordEvent → IO Unit
  /-- Standard error. -/
  log : LogLine → IO Unit
  /-- The certificate checker (the checker's path; the query). -/
  checkCertificate : String → CertificateQuery → IO (Bool × String)
  /-- The KEM tool (eliminator; the key on its stdin). -/
  kemDecapsulate : String → Secret Bytes → Bytes → IO (Except String (Secret Bytes))
  /-- The export file (scaffolding). -/
  readExport : String → IO (Except String (Bytes × Secret Bytes × List (Nat × Secret Bytes)))
  readSelf : String → IO (Except String (Bytes × Nat))
  readReceive : String → IO (Except String Export.ReceiveKeys)
  /-- The application's message and signed request. -/
  readMessage : String → IO String
  readRequest : String → IO (Except String Channels.Real.SignedRequest)
  /-- The long-lived session's directory: the next job, a stop request. -/
  nextJob : String → IO (Option Channels.Real.Job)
  stopAsked : String → IO Bool
  /-- The notify's journal. -/
  readJournal : String → String → IO (List JournalEntry)
  journal : String → JournalLine → IO Unit
  /-- The ceremony's directory: an operator's input, a public file. -/
  ceremonyFile : System.FilePath → CeremonyInput → IO String
  writePublic : System.FilePath → PublicFile → IO Unit
  /-- This party's share files (eliminator) and the TEST store. -/
  saveShare : System.FilePath → ShareFile → Secret Bytes → Bytes → IO Unit
  loadStored : System.FilePath → Nat → IO (Option (Secret Bytes × Bytes))
  /-- The process. -/
  clock : IO Nat
  monotonic : IO Nat
  sleep : Nat → IO Unit
  random : Nat → IO (Secret Bytes)

/-- The real channels of a session of party `party` with configuration `config`. -/
def Channels.real (config : Node.Config.Config) (party : String) : Channels where
  exchange := Channels.Real.exchange
  db call := Channels.Real.db config party call
  readParity := Channels.Real.readParity config
  readDbRead := Channels.Real.readDbRead config
  readKeyShares := Channels.Real.readKeyShares config
  readDealt := Channels.Real.readDealt config
  writeAcknowledged := Channels.Real.writeAcknowledged config
  dbFile file := Channels.Real.dbFile config file
  report := Channels.Real.report
  record := Channels.Real.record config.record
  log := Channels.Real.log
  checkCertificate := Channels.Real.checkCertificate
  kemDecapsulate := Channels.Real.kemDecapsulate
  readExport := Channels.Real.readExport
  readSelf := Channels.Real.readSelf
  readReceive := Channels.Real.readReceive
  readMessage := Channels.Real.readMessage
  readRequest := Channels.Real.readRequest
  nextJob := Channels.Real.nextJob
  stopAsked := Channels.Real.stopAsked
  readJournal := Channels.Real.readJournal
  journal := Channels.Real.journal
  ceremonyFile := Channels.Real.ceremonyFile
  writePublic := Channels.Real.writePublic
  saveShare directory file share tail := Channels.Real.saveShare directory file share tail
  loadStored := Channels.Real.loadStored
  clock := Channels.Real.clock
  monotonic := Channels.Real.monotonic
  sleep := Channels.Real.sleep
  random := Channels.Real.random

end TlsMpc.Node

namespace TlsMpc.Node.Config

/-- **The one reader of the environment** (stage S4: `IO.getEnv` appears nowhere else in the
controller; plan 3.2). `test`: the controller was started with `--test`. A credentials file
(`SIGNAL_LOCAL_CREDENTIALS_FILE`) is loaded here into `account`. -/
def read (test : Bool) : IO Config := do
  let values ← names.mapM fun name => do pure (name, ← IO.getEnv name)
  let env := fun name => (values.find? (·.1 == name)).bind (·.2)
  let config ← IO.ofExcept ((ofEnv env test).mapError IO.userError)
  unless config.ignoredHooks.isEmpty do
    Channels.Real.log (.hooksIgnored config.ignoredHooks)
  match config.credentialsFile with
  | none => pure config
  | some path =>
    let some share ← Channels.Real.loadShare path | throw (IO.userError s!"SIGNAL_LOCAL_CREDENTIALS_FILE {path} is missing")
    pure { config with account := .share share }

end TlsMpc.Node.Config
