import Lean
import TlsMpc.Signal.MlKemPoly
open TlsMpc Std.Tactic.BVDecide
structure MlKemPolyImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "shared canonical coefficients0..3328,256 LE16 coefficients per polynomial; output256 LE16 coefficients; modular polynomial add/sub; no full KEM or actual libcrux refinement"
  deriving Lean.ToJson, Lean.FromJson, BEq

def main (args : List String) : IO Unit := do
  match args with
  | [command,mode] =>
    unless mode == "add" || mode == "sub" do throw (IO.userError "operation")
    let op := mode == "sub"
    let inputBytes := 1024
    if command == "signal-mlkem-poly" then
      let bytes := Signal.MlKemPoly.run Signal.MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic op (ByteCircuit.inputBytes 0 inputBytes)
      let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
      let image : MlKemPolyImage := {
        name := s!"signal-mlkem-poly-{mode}"
        input_bits := inputBytes*8
        input_widths := Array.replicate inputBytes 8
        nodes := AigExport.exportNodes circuit.aig
        outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
      let text := (Lean.toJson image).compress
      match Lean.Json.parse text >>= Lean.fromJson? (α := MlKemPolyImage) with
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
        stdout.putStrLn ((Lean.toJson ((Signal.MlKemPoly.run Signal.MlKemArithmetic.concrete Sha256.concrete ByteAuth.concrete op raw).map BitVec.toNat)).compress)
    else throw (IO.userError "command")
  | _ => throw (IO.userError "expected signal-mlkem-poly|evaluate add|sub")
