import Lean.Data.Json
import TlsMpc.TlsWorkerProcess
import TlsMpc.Node.Config
import TlsMpc.Node.Secret

/-!
# The controller's I/O module (REORGANIZATION_PLAN.md section 3; begun in stage S4)

Plan section 3.2: the only controller file with I/O primitives (with the worker pipe). Stage S5
moves every other I/O site of the controller here, behind the `Channels` record and the message
types of `Messages.lean`. Stage S4 put here, in their final place, the I/O that S4 had to touch:
- `Config.read`: the ONE reader of the process environment (plan 3.2: "Config is read once by
  Config.read, which lives in Channels.lean"; `scripts/lint_node.py` counts `IO.getEnv` sites);
- the eliminators of `Secret` that are I/O (plan 4.1): `saveShare`, `loadShare`, the TEST store
  (`saveStored`, `loadStored`), `kemDecapsulate` (the Kyber key on the tool's standard input,
  never on its argv), and the readers of the database client's outputs that carry this party's
  key shares (`readKeyShares`, `readDealt`; plan 4.2 row 1, `DbReply.shares` from S5);
- `random`: the operating system's generator, returning `Secret` (plan rule 5).
No emitter imports this module.
-/

namespace TlsMpc.Node.Channels
open TlsMpc.TlsWire TlsMpc.Node

private def hex (bytes : Bytes) : String := TlsWorkerProcess.hex bytes

/-- **Eliminator: a secret to this node's own disk** (plan 4.1 `Channels.saveShare`): its hex,
written to a temporary file readable by this user only, then renamed into place. With
`publicTail`: bytes stored after it in the same file (the TEST store's version and sealed state). -/
def saveShare (path : System.FilePath) (share : Secret Bytes) (publicTail : Bytes := []) : IO Unit := do
  let temporary := path.toString ++ ".partial"
  IO.FS.writeFile temporary ""
  IO.setAccessRights temporary { user := { read := true, write := true } }
  IO.FS.writeFile temporary (hex (share.expose ++ publicTail) ++ "\n")
  IO.FS.rename temporary path

/-- A secret from this node's own disk (`saveShare`'s format); `none` when the file is absent. -/
def loadShare (path : System.FilePath) : IO (Option (Secret Bytes)) := do
  if !(← path.pathExists) then return none
  match Secret.ofHex (← IO.FS.readFile path).trimAscii.toString with
  | .ok share => pure (some share)
  | .error _ => throw (IO.userError s!"{path} does not hold hex")

/-- TEST store (`SIGNAL_LOCAL_STORE`): a contact's file is this party's 32-byte key share, then
the public version and sealed state (the caller checks the shape). -/
def loadStored (path : System.FilePath) : IO (Option (Secret Bytes × Bytes)) := do
  if !(← path.pathExists) then return none
  match Node.Bytes.fromHex (← IO.FS.readFile path).trimAscii.toString with
  | .ok bytes => pure (some (Secret.hide (bytes.take 32), bytes.drop 32))
  | .error _ => throw (IO.userError s!"{path} does not hold hex")

/-- **Eliminator: Kyber-1024 decapsulation by the KEM tool** (plan 4.1 `Channels.kemDecapsulate`):
`TOOL kem-decapsulate CIPHERTEXT_HEX`, our Kyber private key (OWN) as hex on its standard input,
the 32-byte shared secret as hex on its standard output. -/
def kemDecapsulate (tool : String) (key : Secret Bytes) (ciphertext : Bytes) : IO (Except String (Secret Bytes)) := do
  let out ← IO.Process.output { cmd := tool, args := #["kem-decapsulate", hex ciphertext] } (some (hex key.expose ++ "\n"))
  if out.exitCode != 0 then return .error "decapsulation failed"
  match Secret.ofHex out.stdout.trimAscii.toString with
  | .ok secret => return if secret.length == 32 then .ok secret else .error "decapsulated secret shape"
  | .error _ => return .error "decapsulated secret shape"

/-- `n` bytes from the operating system's generator: this party's own randomness. -/
def random (n : Nat) : IO (Secret Bytes) := do
  pure (Secret.hide (← IO.getRandomBytes (USize.ofNat n)).data.toList)

/-- The database client's combined shares (`combine --out`): per id (as the client writes it),
this party's share of the contact's key. Plan 4.2 row 1. -/
def readKeyShares (path : System.FilePath) : IO (List (String × Secret Bytes)) := do
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let entries := ((json.getObjValAs? (Array Lean.Json) "ids").toOption.getD #[]).toList
  entries.filterMapM fun entry => do
    match (entry.getObjValAs? String "id").toOption, (entry.getObjValAs? String "share").toOption with
    | some id, some hexShare => match Secret.ofHex hexShare with
      | .ok share => pure (some (id, share))
      | .error _ => throw (IO.userError "the database client's share is not hex")
    | _, _ => pure none

/-- The database client's `deal --out`: which nodes committed (public), and the dealt summand,
this party's share of the new key (plan 4.2 rows 1, 2). -/
def readDealt (path : System.FilePath) : IO (List String × Option (Secret Bytes)) := do
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let nodes := ((json.getObjValAs? (Array String) "nodes").toOption.getD #[]).toList
  let summand ← match (json.getObjValAs? String "summand").toOption with
    | none => pure none
    | some hexShare => match Secret.ofHex hexShare with
      | .ok share => pure (some share)
      | .error _ => throw (IO.userError "the dealt summand is not hex")
  pure (nodes, summand)

end TlsMpc.Node.Channels

namespace TlsMpc.Node.Config

/-- **The one reader of the environment** (stage S4: `IO.getEnv` appears nowhere else in the
controller; plan 3.2). `test`: the controller was started with `--test`. A credentials file
(`SIGNAL_LOCAL_CREDENTIALS_FILE`) is loaded here into `account`. -/
def read (test : Bool) : IO Config := do
  let values ← names.mapM fun name => do pure (name, ← IO.getEnv name)
  let env := fun name => (values.find? (·.1 == name)).bind (·.2)
  let config ← IO.ofExcept ((ofEnv env test).mapError IO.userError)
  unless config.ignoredHooks.isEmpty do
    IO.eprintln s!"TEST hooks ignored (the controller was not started with --test): {", ".intercalate config.ignoredHooks}"
  match config.credentialsFile with
  | none => pure config
  | some path =>
    let some share ← Channels.loadShare path | throw (IO.userError s!"SIGNAL_LOCAL_CREDENTIALS_FILE {path} is missing")
    pure { config with account := .share share }

end TlsMpc.Node.Config
