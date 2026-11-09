import Lean
import TlsMpc.Signal.PrivateRecordSchemaV1
import TlsMpc.Signal.PrivateRecordAdmissionV1
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
structure RecordAdmissionImage where
 format : String := "tls-mpc-aig-v1"
 name : String := "signal-private-record-admit-v1"
 input_bits : Nat
 input_widths : Array Nat
 schema_sha256 : String
 snapshot_bytes : Nat
 nodes : Array (List Nat)
 outputs : Array (Nat × Nat)
 deriving Lean.ToJson

-- Internal public-capacity restored snapshot/projection/service coherence.
-- No field/value or acceptance flag is imported as a public witness.
def main : IO Unit := do
 let n := PrivateRecordSchemaV1.byteCount
 let count := 6686
 let raw := ByteCircuit.inputBytes 0 count
 let output := PrivateRecordAdmissionV1.validate Sha256.symbolic Word64.symbolic ByteAuth.symbolic raw
 let circuit := AigExport.compile (ByteCircuit.joinExpr output)
 let image : RecordAdmissionImage := {
  input_bits := 8*count
  input_widths := Array.replicate count 8
  schema_sha256 := PrivateRecordSchemaV1.digest
  snapshot_bytes := n
  nodes := AigExport.exportNodes circuit.aig
  outputs := Array.ofFn (fun (i : Fin (8*output.length)) => AigExport.exportRef
    (circuit.vec.get (8*output.length-1-i.val) (by omega))) }
 (← IO.getStdout).putStrLn (Lean.toJson image).compress
