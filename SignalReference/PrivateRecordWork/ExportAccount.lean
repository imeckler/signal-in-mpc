import Lean
import TlsMpc.Signal.PrivateAccountAdmissionV2
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
structure AccountAdmissionImage where
 format : String := "tls-mpc-aig-v1"
 name : String := "signal-private-account-admit-v2"
 input_bits : Nat
 input_widths : Array Nat
 conversations : Nat
 logical_bytes : Nat
 nodes : Array (List Nat)
 outputs : Array (Nat × Nat)
 deriving Lean.ToJson

def main (args : List String) : IO Unit := do
 let n := (args.headD "1").toNat!
 if !(1<=n && n<=4) then throw (IO.userError "account conversation capacity")
 let count := PrivateAccountAdmissionV2.globalBytes+n*PrivateAccountAdmissionV2.conversationBytes
 let raw := ByteCircuit.inputBytes 0 count
 let output := PrivateAccountAdmissionV2.validate n Sha256.symbolic Word64.symbolic ByteAuth.symbolic raw
 let circuit := AigExport.compile (ByteCircuit.joinExpr output)
 let image : AccountAdmissionImage := {
  input_bits := 8*count
  input_widths := Array.replicate count 8
  conversations := n
  logical_bytes := count
  nodes := AigExport.exportNodes circuit.aig
  outputs := Array.ofFn (fun (i : Fin (8*output.length)) => AigExport.exportRef
    (circuit.vec.get (8*output.length-1-i.val) (by omega))) }
 (← IO.getStdout).putStrLn (Lean.toJson image).compress
