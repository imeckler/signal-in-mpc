import Lean
import TlsMpc.Signal.PrivateAccountOutboxV1
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
structure AccountOutboxImage where
 format : String := "tls-mpc-aig-v1"
 name : String := "signal-private-account-outbox-v1"
 input_bits : Nat
 input_widths : Array Nat
 ordinal : Nat
 logical_bytes : Nat
 nodes : Array (List Nat)
 outputs : Array (Nat × Nat)
 deriving Lean.ToJson

def main (args : List String) : IO Unit := do
 let n := (args.headD "1").toNat!
 if !(n<4) then throw (IO.userError "account conversation capacity")
 let count := 5213
 let raw := ByteCircuit.inputBytes 0 count
 let output := PrivateAccountOutboxV1.select ByteAuth.symbolic n raw
 let circuit := AigExport.compile (ByteCircuit.joinExpr output)
 let image : AccountOutboxImage := {
  input_bits := 8*count
  input_widths := Array.replicate count 8
  ordinal := n
  logical_bytes := count
  nodes := AigExport.exportNodes circuit.aig
  outputs := Array.ofFn (fun (i : Fin (8*output.length)) => AigExport.exportRef
    (circuit.vec.get (8*output.length-1-i.val) (by omega))) }
 (← IO.getStdout).putStrLn (Lean.toJson image).compress
