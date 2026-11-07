import Lean
import TlsMpc.Signal.KemWire
open TlsMpc Std.Tactic.BVDecide
structure KemWireImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "shared headers2,candidate status1,payload; fixed Signal KEM tags/sizes; output accepted1 and gated typed payload; separate from actual Rust refinement"
  deriving Lean.ToJson, Lean.FromJson, BEq

def main (args : List String) : IO Unit := do
  match args with
  | [command,mode,variant] =>
    let profile ← match variant with
      | "kyber768" => pure Signal.KemWire.Profile.kyber768
      | "kyber1024" => pure Signal.KemWire.Profile.kyber1024
      | "mlkem1024" => pure Signal.KemWire.Profile.mlkem1024
      | _ => throw (IO.userError "profile")
    let op ← match mode with
      | "keygen" => pure Signal.MlKem.Operation.keygen
      | "encapsulate" => pure Signal.MlKem.Operation.encapsulate
      | "decapsulate" => pure Signal.MlKem.Operation.decapsulate
      | _ => throw (IO.userError "operation")
    let size := match op with
      | .keygen => Signal.KemWire.secretSize profile+Signal.KemWire.publicSize profile
      | .encapsulate => Signal.KemWire.ciphertextSize profile+32
      | .decapsulate => 32
    let inputBytes := 3+size
    if command == "signal-kem-wire" then
      let bytes := Signal.KemWire.finishBytes ByteAuth.symbolic profile op (ByteCircuit.inputBytes 0 inputBytes)
      let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
      let image : KemWireImage := {
        name := s!"signal-kem-wire-{mode}-{variant}"
        input_bits := inputBytes*8
        input_widths := Array.replicate inputBytes 8
        nodes := AigExport.exportNodes circuit.aig
        outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
      let text := (Lean.toJson image).compress
      match Lean.Json.parse text >>= Lean.fromJson? (α := KemWireImage) with
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
        stdout.putStrLn ((Lean.toJson ((Signal.KemWire.finishBytes ByteAuth.concrete profile op raw).map BitVec.toNat)).compress)
    else throw (IO.userError "command")
  | _ => throw (IO.userError "expected signal-kem-wire|evaluate keygen|encapsulate|decapsulate VARIANT")
