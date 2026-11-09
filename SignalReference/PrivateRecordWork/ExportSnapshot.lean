import Lean
import TlsMpc.Signal.PrivateRecordSchemaV1
import TlsMpc.Signal.PrivateRecordSendV1
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
structure RecordImage where
 format : String := "tls-mpc-aig-v1"
 name : String
 input_bits : Nat
 input_widths : Array Nat
 schema_sha256 : String
 snapshot_bytes : Nat
 nodes : Array (List Nat)
 outputs : Array (Nat × Nat)
 deriving Lean.ToJson

def main (args : List String) : IO Unit := do
 let mode := args.headD ""
 if mode != "send" && mode != "receive" then throw (IO.userError "expected send|receive")
 let n := PrivateRecordSchemaV1.byteCount
 let count := n+(if mode="send" then 81 else 608)
 let raw := ByteCircuit.inputBytes 0 count
 let a := ByteAuth.symbolic
 let restored := PrivateRecordSnapshotV1.restore a 16 (PrivateRecordSchemaV1.schema a) (raw.take n)
 let result := raw.drop n
 let updated := if mode="send" then PrivateRecordSendV1.applySend Sha256.symbolic a restored.1 result
   else PrivateRecordUpdateV1.applyReceive a restored.1 result
 let output := ByteAuth.eqMask a (OpenResult.get a result 0) (a.const 255) ::
   (PrivateRecordSnapshotV1.project Word64.symbolic a updated ++ PrivateRecordSnapshotV1.flatten a 16 updated)
 let circuit := AigExport.compile (ByteCircuit.joinExpr output)
 let image : RecordImage := {
  name := "signal-private-record-"++mode++"-v1"
  input_bits := 8*count
  input_widths := Array.replicate count 8
  schema_sha256 := PrivateRecordSchemaV1.digest
  snapshot_bytes := n
  nodes := AigExport.exportNodes circuit.aig
  outputs := Array.ofFn (fun (i : Fin (8*output.length)) => AigExport.exportRef
    (circuit.vec.get (8*output.length-1-i.val) (by omega))) }
 (← IO.getStdout).putStrLn (Lean.toJson image).compress
