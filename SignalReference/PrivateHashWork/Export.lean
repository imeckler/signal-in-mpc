import Lean
import TlsMpc.Signal.PrivateHash
open TlsMpc Std.Tactic.BVDecide
structure BufferImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def emit (name : String) (count : Nat) (bytes : List (BVExpr 8)) : IO Unit := do
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let image : BufferImage := {
    name := name
    input_bits := 8*count
    input_widths := Array.replicate count 8
    nodes := AigExport.exportNodes circuit.aig
    outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef
      (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
  (← IO.getStdout).putStrLn (Lean.toJson image).compress

def main (args : List String) : IO Unit := do
  match args with
  | [mode,text] =>
    let some cap := text.toNat? | throw (IO.userError "expected capacity")
    unless cap≤16384 do throw (IO.userError "capacity exceeds TLS contract")
    let a := ByteAuth.symbolic
    let keyed := mode == "hmac"
    let offset := if keyed then 32 else 0
    let input := Signal.PrivateBuffer.fromWire a cap (ByteCircuit.inputBytes offset (cap+3))
    let output := if keyed then Signal.PrivateHash.hmac Sha256.symbolic a
      (ByteCircuit.inputBytes 0 32) cap input else Signal.PrivateHash.hash Sha256.symbolic a cap input
    emit ("signal-private-"++mode) (offset+cap+3) (Signal.PrivateBuffer.output a output)
  | _ => throw (IO.userError "expected hash|hmac CAP")
