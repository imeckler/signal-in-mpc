import Lean
import TlsMpc.Signal.PrivateSealedSender
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
  | [certText,capText] =>
    let some cert := certText.toNat? | throw (IO.userError "expected certificate size")
    let some cap := capText.toNat? | throw (IO.userError "expected inner capacity")
    unless cert≤1024 ∧ cap≤4096 do throw (IO.userError "bounded SSv1")
    let a := ByteAuth.symbolic
    let field := ByteCircuit.inputBytes
    let inner := Signal.PrivateBuffer.fromWire a cap (field (160+cert+32) (cap+3))
    let result := Signal.PrivateSealedSender.boundSeal Aes.symbolic Sha256.symbolic a
      (field 0 32) (field 32 32) (field 64 32) (field 96 32) (field 128 32)
      (field 160 cert) (field (160+cert) 32) inner
    emit "private-length-sealed-sender" (160+cert+32+cap+3) (Signal.PrivateBuffer.output a result)
  | _ => throw (IO.userError "expected CERT_BYTES INNER_CAPACITY")
