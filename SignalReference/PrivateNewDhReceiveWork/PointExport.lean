import Lean
import TlsMpc.Signal.PrivateProtoParseV1Proofs
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

def main : IO Unit :=
  emit "signal-private-new-dh-point-256" 259
    (Signal.PrivateProtoParseV1.parseCore Signal.VarintDecode.Spqr.symbolic Signal.Word64.symbolic ByteAuth.symbolic
      (ByteCircuit.inputBytes 3 256) (.var 1) (.var 2) (.var 0))
