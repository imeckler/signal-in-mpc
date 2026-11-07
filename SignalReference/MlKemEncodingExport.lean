import Lean
import TlsMpc.Signal.MlKemEncoding
open TlsMpc Std.Tactic.BVDecide
structure MlKemEncodingImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "shared 256 canonical LE16 coefficients for compression; raw width-bit coefficients for encoding; fixed-width packed little-endian bytes for decoding/decompression; no full KEM or actual libcrux refinement"
  deriving Lean.ToJson, Lean.FromJson, BEq

def main (args : List String) : IO Unit := do
  match args with
  | [command,mode,widthText] =>
    let op ← match mode with
      | "encode" => pure Signal.MlKemEncoding.Operation.encode
      | "decode" => pure Signal.MlKemEncoding.Operation.decode
      | "compress" => pure Signal.MlKemEncoding.Operation.compress
      | "decompress" => pure Signal.MlKemEncoding.Operation.decompress
      | _ => throw (IO.userError "operation")
    let width ← match widthText.toNat? with
      | some n => pure n
      | none => throw (IO.userError "width")
    unless width > 0 && width ≤ 12 do throw (IO.userError "width1..12")
    let inputBytes := if mode == "encode" || mode == "compress" then 512 else 32*width
    if command == "signal-mlkem-encoding" then
      let bytes := Signal.MlKemEncoding.run Signal.MlKemArithmetic.symbolic Signal.MlKemEncoding.symbolic Sha256.symbolic ByteAuth.symbolic op width (ByteCircuit.inputBytes 0 inputBytes)
      let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
      let image : MlKemEncodingImage := {
        name := s!"signal-mlkem-encoding-{mode}-{width}"
        input_bits := inputBytes*8
        input_widths := Array.replicate inputBytes 8
        nodes := AigExport.exportNodes circuit.aig
        outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
      let text := (Lean.toJson image).compress
      match Lean.Json.parse text >>= Lean.fromJson? (α := MlKemEncodingImage) with
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
        stdout.putStrLn ((Lean.toJson ((Signal.MlKemEncoding.run Signal.MlKemArithmetic.concrete Signal.MlKemEncoding.concrete Sha256.concrete ByteAuth.concrete op width raw).map BitVec.toNat)).compress)
    else throw (IO.userError "command")
  | _ => throw (IO.userError "expected signal-mlkem-encoding|evaluate encode|decode|compress|decompress WIDTH")
