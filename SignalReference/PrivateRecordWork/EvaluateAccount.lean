import Lean
import TlsMpc.Signal.PrivateAccountAdmissionV2
open TlsMpc TlsMpc.Signal
 def main : IO Unit := do
  let input ← IO.getStdin;let output ← IO.getStdout
  repeat
   let line ← input.getLine
   if line.isEmpty then break
   let parsed := do
    let json ← Lean.Json.parse line
    let n ← json.getObjValAs? Nat "conversations"
    let raw ← json.getObjValAs? (List Nat) "raw"
    pure (n,raw)
   let (n,raw) ← match parsed with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
   output.putStrLn (Lean.toJson ((PrivateAccountAdmissionV2.validate n Sha256.concrete Word64.concrete ByteAuth.concrete (raw.map (BitVec.ofNat 8))).map BitVec.toNat)).compress
