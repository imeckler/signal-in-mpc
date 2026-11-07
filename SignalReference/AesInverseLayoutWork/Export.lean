import Lean
import TlsMpc.Signal.AesInverseWrite

/-! Unverified serialization of the proved writer's numeric wiring circuit. -/

namespace AesInverseWriteExport
open TlsMpc Std.Tactic.BVDecide

structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String := "aes-inverse-write-reordered"
  input_bits : Nat := 160
  input_widths : Array Nat := #[64] ++ Array.replicate 12 8
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "secret u64 column MSB-first, then twelve secret initial bytes; output twelve secret write-back bytes"
  deriving Lean.ToJson, Lean.FromJson, BEq

def artifact : Image :=
  let bytes := Signal.AesInverseWrite.expr (.var 0) (fun byte => .var (byte + 1))
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { nodes := AigExport.exportNodes circuit.aig, outputs }

end AesInverseWriteExport

def main : IO Unit := do
  let image := AesInverseWriteExport.artifact
  let serialized := (Lean.toJson image).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := AesInverseWriteExport.Image) with
  | .error message => throw (IO.userError message)
  | .ok decoded => unless decoded == image do throw (IO.userError "serialization changed artifact")
  (← IO.getStdout).putStrLn serialized
