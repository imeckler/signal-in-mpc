import Lean
import TlsMpc.Signal.PrivateSpqrSend
open TlsMpc.Signal TlsMpc
-- PUBLIC preflight only: sender/root136 || sendPQ44 || local/remote IDs64 || plaintext80.
def evaluateReply (raw : List (BitVec 8)) : List (BitVec 8) :=
  let field := fun start count => (raw.drop start).take count
  let i : SpqrSend.Input (BitVec 8) := ⟨68,field 128 4,field 132 4,field 64 32,
    field 96 32,field 144 32,field 176 4,field 136 8,0,[],[],field 180 32,field 212 32,
    field 244 80,[]⟩
  PrivateSpqrSend.output ByteAuth.concrete (PrivateSpqrSend.oldState i)
    (PrivateSpqrSend.prepare Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete false false i)
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let raw ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
      | .ok values => pure (values.map (BitVec.ofNat 8))
      | .error e => throw (IO.userError e)
    if raw.length != 324 then throw (IO.userError "reply preflight expects324 bytes")
    stdout.putStrLn (Lean.toJson ((evaluateReply raw).map BitVec.toNat)).compress
