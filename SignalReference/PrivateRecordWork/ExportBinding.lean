import Lean
import TlsMpc.Signal.PrivateRecordSchemaV1
import TlsMpc.Signal.PrivateRecordBindingV1
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
structure RecordBindingImage where
 format : String := "tls-mpc-aig-v1"
 name : String := "signal-private-record-bind-v1"
 input_bits : Nat
 input_widths : Array Nat
 schema_sha256 : String
 snapshot_bytes : Nat
 nodes : Array (List Nat)
 outputs : Array (Nat × Nat)
 deriving Lean.ToJson

-- Internal public-capacity snapshot -> actual-call/actual-producer binding.
-- No field/value or acceptance flag is imported as a public witness.
def main : IO Unit := do
 let n := PrivateRecordSchemaV1.byteCount
 let count := n+611+81
 let raw := ByteCircuit.inputBytes 0 count
 let a := ByteAuth.symbolic
 let restored := PrivateRecordSnapshotV1.restore a 16 (PrivateRecordSchemaV1.schema a) (raw.take n)
 let result := PrivateRecordBindingV1.bind Sha256.symbolic Word64.symbolic a restored.1
   ((raw.drop n).take 611) (raw.drop (n+611))
 let output := result.1 ++ PrivateRecordSnapshotV1.project Word64.symbolic a result.2 ++
   PrivateRecordSnapshotV1.flatten a 16 result.2
 let circuit := AigExport.compile (ByteCircuit.joinExpr output)
 let image : RecordBindingImage := {
  input_bits := 8*count
  input_widths := Array.replicate count 8
  schema_sha256 := PrivateRecordSchemaV1.digest
  snapshot_bytes := n
  nodes := AigExport.exportNodes circuit.aig
  outputs := Array.ofFn (fun (i : Fin (8*output.length)) => AigExport.exportRef
    (circuit.vec.get (8*output.length-1-i.val) (by omega))) }
 (← IO.getStdout).putStrLn (Lean.toJson image).compress
