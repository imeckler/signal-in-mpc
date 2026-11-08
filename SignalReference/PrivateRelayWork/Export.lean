import Lean
import TlsMpc.Signal.PrivateRelay
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
  | [capText] =>
    let some cap := capText.toNat? | throw (IO.userError "expected sealed capacity")
    unless cap≤8192 do throw (IO.userError "bounded relay")
    let a := ByteAuth.symbolic
    let sealed := Signal.PrivateBuffer.fromWire a cap (ByteCircuit.inputBytes 57 (cap+3))
    let result := Signal.PrivateRelay.encode Sha256.symbolic Signal.RelayEncoding.decimalSymbolic
      Signal.Varint64.symbolic a (ByteCircuit.inputBytes 0 57) sealed
    emit "private-length-relay-put" (57+cap+3) (Signal.PrivateBuffer.output a result)
  | _ => throw (IO.userError "expected SEALED_CAPACITY")
