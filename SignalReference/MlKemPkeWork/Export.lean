import Lean
import TlsMpc.Signal.MlKemPke
open TlsMpc Std.Tactic.BVDecide

def main (args : List String) : IO Unit := do
  match args with
  | [mode,variant] =>
    let rank := if variant == "mlkem512" then 2 else if variant == "mlkem768" then 3 else 4
    unless ["mlkem512","mlkem768","mlkem1024","kyber1024"].contains variant do throw (IO.userError "variant")
    let eta := if rank == 2 then 3 else 2
    let du := if rank == 4 then 11 else 10
    let dv := if rank == 4 then 5 else 4
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      let raw ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
        | .ok ns => pure (ns.map (BitVec.ofNat 8))
        | .error e => throw (IO.userError e)
      let out ← match mode with
        | "keygen" =>
          unless raw.length == 32 do throw (IO.userError "seed32")
          let result := Signal.MlKemPke.keygen Signal.MlKemArithmetic.concrete Sha256.concrete ByteAuth.concrete Signal.Word64.concrete Signal.Keccak.concrete rank eta 224 (variant == "kyber1024") raw
          pure (result.success :: result.secretKey++result.publicKey)
        | "encrypt" =>
          unless raw.length == 384*rank+96 do throw (IO.userError "pk,message32,coins32")
          let result := Signal.MlKemPke.encrypt Signal.MlKemArithmetic.concrete Signal.MlKemEncoding.concrete Sha256.concrete ByteAuth.concrete Signal.Word64.concrete Signal.Keccak.concrete rank eta du dv 224 (raw.take (384*rank+32)) ((raw.drop (384*rank+32)).take 32) (raw.drop (384*rank+64))
          pure (result.success :: result.bytes)
        | "decrypt" =>
          unless raw.length == 384*rank+32*(du*rank+dv) do throw (IO.userError "skPKE,ciphertext")
          pure (Signal.MlKemPke.decrypt Signal.MlKemArithmetic.concrete Signal.MlKemEncoding.concrete Sha256.concrete ByteAuth.concrete rank du dv (raw.take (384*rank)) (raw.drop (384*rank)))
        | _ => throw (IO.userError "mode")
      stdout.putStrLn ((Lean.toJson (out.map BitVec.toNat)).compress)
  | _ => throw (IO.userError "keygen|encrypt|decrypt VARIANT")
