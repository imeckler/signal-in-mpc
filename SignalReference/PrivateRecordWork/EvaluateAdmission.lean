import Lean
import TlsMpc.Signal.PrivateRecordAdmissionV1
open TlsMpc TlsMpc.Signal
 def main : IO Unit := do
  let input ← IO.getStdin; let output ← IO.getStdout
  repeat
   let line ← input.getLine
   if line.isEmpty then break
   let raw ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
    | .ok raw => pure raw
    | .error error => throw (IO.userError error)
   let result := PrivateRecordAdmissionV1.validate Sha256.concrete Word64.concrete ByteAuth.concrete (raw.map (BitVec.ofNat 8))
   output.putStrLn (Lean.toJson (result.map BitVec.toNat)).compress
