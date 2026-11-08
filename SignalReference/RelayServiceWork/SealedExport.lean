import Lean
import TlsMpc.Signal.SealedSenderV1
open TlsMpc Std.Tactic.BVDecide
structure SealedImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-sealed-sender-v1"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def main (args : List String) : IO Unit := do
  match args with
  | [certText,innerText] =>
    let some cert := certText.toNat? | throw (IO.userError "expected certificate size")
    let some inner := innerText.toNat? | throw (IO.userError "expected inner wire size")
    unless 0<cert ∧ cert≤1024 ∧ 0<inner ∧ inner≤4096 do throw (IO.userError "bounded sealed sender shape")
    let bytes := Signal.SealedSenderV1.sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic
      (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 32) (ByteCircuit.inputBytes 64 32)
      (ByteCircuit.inputBytes 96 32) (ByteCircuit.inputBytes 128 32)
      (ByteCircuit.inputBytes 160 cert) (ByteCircuit.inputBytes (160+cert) inner)
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : SealedImage := {
      input_bits := 8 * (160 + cert + inner)
      input_widths := Array.replicate (160 + cert + inner) 8
      nodes := AigExport.exportNodes circuit.aig
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef
        (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }

    (← IO.getStdout).putStrLn (Lean.toJson image).compress
  | _ => throw (IO.userError "expected CERTIFICATE_BYTES INNER_SIGNAL_WIRE_BYTES")
