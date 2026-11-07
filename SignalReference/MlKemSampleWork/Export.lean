import Lean
import TlsMpc.Signal.MlKemSample
open TlsMpc Std.Tactic.BVDecide
structure MlKemSampleImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "shared raw candidate bytes or SHAKE128 seed32||indexByte||indexByte; output shared status1 and fixed-count LE16 coefficients; public bounded budget; abort zeroes coefficients; no full KEM or actual libcrux refinement"
  deriving Lean.ToJson, Lean.FromJson, BEq

def main (args : List String) : IO Unit := do
  match args with
  | [command,mode,countText,pairsText] =>
    unless mode == "sample" || mode == "matrix" do throw (IO.userError "mode")
    let count ← match countText.toNat? with
      | some n => pure n
      | none => throw (IO.userError "count")
    let pairs ← match pairsText.toNat? with
      | some n => pure n
      | none => throw (IO.userError "pairs")
    unless count ≤ 256 && pairs ≤ 336 do throw (IO.userError "public limits")
    let inputBytes := if mode == "sample" then 3*pairs else 34
    if command == "signal-mlkem-sample" then
      let bytes := if mode == "sample" then Signal.MlKemSample.run Signal.Word64.symbolic ByteAuth.symbolic count pairs (ByteCircuit.inputBytes 0 inputBytes) else Signal.MlKemSample.matrix Signal.Word64.symbolic ByteAuth.symbolic Signal.Keccak.symbolic count pairs (ByteCircuit.inputBytes 0 inputBytes)
      let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
      let image : MlKemSampleImage := {
        name := s!"signal-mlkem-sample-{mode}-{count}-{pairs}"
        input_bits := inputBytes*8
        input_widths := Array.replicate inputBytes 8
        nodes := AigExport.exportNodes circuit.aig
        outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
      let text := (Lean.toJson image).compress
      match Lean.Json.parse text >>= Lean.fromJson? (α := MlKemSampleImage) with
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
        stdout.putStrLn ((Lean.toJson ((if mode == "sample" then Signal.MlKemSample.run Signal.Word64.concrete ByteAuth.concrete count pairs raw else Signal.MlKemSample.matrix Signal.Word64.concrete ByteAuth.concrete Signal.Keccak.concrete count pairs raw).map BitVec.toNat)).compress)
    else throw (IO.userError "command")
  | _ => throw (IO.userError "expected signal-mlkem-sample|evaluate sample|matrix COUNT PAIRS")
