import Lean
import TlsMpc.Signal.MlKem
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
      let operation ← match mode with
        | "keygen" => pure Signal.MlKem.Operation.keygen
        | "encapsulate" => pure Signal.MlKem.Operation.encapsulate
        | "decapsulate" => pure Signal.MlKem.Operation.decapsulate
        | _ => throw (IO.userError "operation")
      let expected := match operation with
        | .keygen => 64
        | .encapsulate => 384*rank+64
        | .decapsulate => 768*rank+96+32*(du*rank+dv)
      unless raw.length == expected do throw (IO.userError "input length")
      let out := Signal.MlKem.run Signal.MlKemArithmetic.concrete Signal.MlKemEncoding.concrete Sha256.concrete ByteAuth.concrete Signal.Word64.concrete Signal.Keccak.concrete rank eta du dv 224 (variant == "kyber1024") operation raw
      stdout.putStrLn ((Lean.toJson (out.map BitVec.toNat)).compress)
  | _ => throw (IO.userError "keygen|encapsulate|decapsulate VARIANT")
