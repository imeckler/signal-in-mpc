import Lean
import TlsMpc.Signal.PrivateSessionReceiveV1
open TlsMpc

def main : IO Unit := do
 let stdin ← IO.getStdin
 let stdout ← IO.getStdout
 repeat
  let line ← stdin.getLine
  if line.isEmpty then break
  let raw ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
   | .ok values => pure (values.map (BitVec.ofNat 8))
   | .error e => throw (IO.userError e)
  if raw.length != 64 then throw (IO.userError "point fixture expects64 bytes")
  stdout.putStrLn (Lean.toJson [ (ByteAuth.equalMask ByteAuth.concrete (raw.take 32) (raw.drop 32)).toNat ]).compress
