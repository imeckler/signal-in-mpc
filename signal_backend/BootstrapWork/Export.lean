import Lean
import TlsMpc.Sha256Backend
import TlsMpc.Signal.PrivateBootstrapKeysV1
import TlsMpc.Signal.PrivateInitialSpqrV1Proofs
import TlsMpc.Signal.PrivatePreKeyMessageV1
open TlsMpc Std.Tactic.BVDecide
structure BootstrapImage where
 format : String := "tls-mpc-aig-v1"
 name : String
 sha_profile : String := "gate-efficient"
 input_bits : Nat
 input_widths : Array Nat
 nodes : Array (List Nat)
 outputs : Array (Nat × Nat)
 deriving Lean.ToJson
private def emit (name : String) (count : Nat) (bytes : List (BVExpr 8)) : IO Unit := do
 let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
 let image : BootstrapImage := {
   name := name
   input_bits := 8*count
   input_widths := Array.replicate count 8
   nodes := AigExport.exportNodes circuit.aig
   outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef
     (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }

 (← IO.getStdout).putStrLn (Lean.toJson image).compress

def main (args : List String) : IO Unit := do
 let [profile] := args | throw (IO.userError "keys|spqr-start|spqr-second|prekey")
 let s := Sha256Backend.select .gateEfficient Sha256.symbolic
 let a := ByteAuth.symbolic
 let get := ByteCircuit.inputBytes
 match profile with
 | "keys" =>
   emit "signal-bootstrap-keys-v1-ge" 1955
     (Signal.PrivateBootstrapKeysV1.prepareKeys s a (.var 0) (get 1 32) (get 33 32) (get 65 288) (get 353 1602))
 | "spqr-start" =>
   emit "signal-bootstrap-spqr-start-v1-ge" 3617
     (Signal.PrivateInitialSpqrV1.start s a (get 0 32) (get 32 3585))
 | "spqr-second" =>
   emit "signal-bootstrap-spqr-second-v1-ge" 3842
     (Signal.PrivateInitialSpqrV1.second s a (get 0 3842))
 | "prekey" =>
   let signal : Signal.PrivateBuffer.Buffer (BVExpr 8) :=
    ⟨.var 1650,Signal.PrivateBuffer.decodeLength a (get 1651 2),get 1653 256⟩
   let result := Signal.PrivatePreKeyMessageV1.message s a (.var 0)
    (get 1 4) (get 5 4) (get 9 4) (get 13 4) (get 17 32) (get 49 32) (get 81 1569) signal
   emit "signal-bootstrap-prekey-v1-ge" 1909 (Signal.PrivateBuffer.output a result)
 | _ => throw (IO.userError "unknown bootstrap profile")
