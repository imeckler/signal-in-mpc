import Lean
import TlsMpc.Signal.MlKemNtt
open TlsMpc Std.Tactic.BVDecide
structure MlKemNttImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "shared canonical coefficients0..3328,256 LE16 coefficients per polynomial; output256 LE16 coefficients; forward/inverse NTT or baseMultiply; no full KEM or actual libcrux refinement"
  deriving Lean.ToJson, Lean.FromJson, BEq

def main (args : List String) : IO Unit := do
  match args with
  | [command,mode] =>
    let op ← match mode with
      | "forward" => pure Signal.MlKemNtt.Operation.forward
      | "inverse" => pure Signal.MlKemNtt.Operation.inverse
      | "multiply" => pure Signal.MlKemNtt.Operation.multiply
      | _ => throw (IO.userError "operation")
    let inputBytes := if mode == "multiply" then 1024 else 512
    if command == "signal-mlkem-ntt" then
      let bytes := Signal.MlKemNtt.run Signal.MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic op (ByteCircuit.inputBytes 0 inputBytes)
      let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
      let image : MlKemNttImage := {
        name := s!"signal-mlkem-ntt-{mode}"
        input_bits := inputBytes*8
        input_widths := Array.replicate inputBytes 8
        nodes := AigExport.exportNodes circuit.aig
        outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
      let text := (Lean.toJson image).compress
      match Lean.Json.parse text >>= Lean.fromJson? (α := MlKemNttImage) with
        | .error e => throw (IO.userError e)
        | .ok decoded => unless decoded == image do throw (IO.userError "JSON roundtrip")
      (← IO.getStdout).putStrLn text
    else if command == "evaluate" then
      let stdin ← IO.getStdin
      let stdout ← IO.getStdout
      repeat
        let line ← stdin.getLine
        if line.isEmpty then break
        let raw ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
          | .ok ns => pure (ns.map (BitVec.ofNat 8))
          | .error e => throw (IO.userError e)
        unless raw.length == inputBytes do throw (IO.userError "input length")
        stdout.putStrLn ((Lean.toJson ((Signal.MlKemNtt.run Signal.MlKemArithmetic.concrete Sha256.concrete ByteAuth.concrete op raw).map BitVec.toNat)).compress)
    else throw (IO.userError "command")
  | _ => throw (IO.userError "expected signal-mlkem-ntt|evaluate forward|inverse|multiply")
