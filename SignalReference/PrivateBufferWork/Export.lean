import Lean
import TlsMpc.Signal.PrivateVarint
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
  let a := ByteAuth.symbolic
  match args with
  | ["append",text] =>
    let some cap := text.toNat? | throw (IO.userError "expected capacity")
    unless cap≤16384 do throw (IO.userError "capacity exceeds TLS contract")
    emit "signal-private-append" (2*(cap+3)) (Signal.PrivateBuffer.appendWire a cap
      (ByteCircuit.inputBytes 0 (cap+3)) (ByteCircuit.inputBytes (cap+3) (cap+3)))
  | ["varint32"] =>
    emit "signal-private-varint32" 4 (Signal.PrivateBuffer.output a (Signal.PrivateVarint.uint32 Sha256.symbolic a
      (Signal.Varint.pack Sha256.symbolic a (ByteCircuit.inputBytes 0 4))))
  | ["varint64"] =>
    emit "signal-private-varint64" 8 (Signal.PrivateBuffer.output a (Signal.PrivateVarint.uint64 Signal.Varint64.symbolic a
      (Signal.Varint64.pack Signal.Varint64.symbolic a (ByteCircuit.inputBytes 0 8))))
  | ["counter-chunk"] =>
    let value := Signal.PrivateVarint.uint32 Sha256.symbolic a
      (Signal.Varint.pack Sha256.symbolic a (ByteCircuit.inputBytes 0 4))
    let before :=  Signal.PrivateBuffer.fromPublic a 16 [a.const 16]
    let after :=  Signal.PrivateBuffer.fromPublic a 16 ("payload".toUTF8.data.toList.map (fun b => a.const b.toNat))
    emit "signal-private-counter-chunk" 4 (Signal.PrivateBuffer.output a
      (Signal.PrivateBuffer.append a 16 (Signal.PrivateBuffer.append a 16 before value) after))
  | _ => throw (IO.userError "expected append CAP | varint32 | varint64 | counter-chunk")
