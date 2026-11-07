import Lean
import AesAddRoundKeyWork.Circuit

namespace AesXorAssignExport
open TlsMpc Std.Tactic.BVDecide

structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String := "aes-core-u64-xor-assign"
  input_bits : Nat := 128
  input_widths : Array Nat := #[64, 64]
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "two secret u64 operands MSB-first; secret resulting u64 MSB-first"
  deriving Lean.ToJson, Lean.FromJson, BEq

def artifact : Image :=
  let circuit := AigExport.compile (Signal.AesXorAssign.expr (.var 0) (.var 1))
  let outputs := Array.ofFn (fun (i : Fin 64) =>
    AigExport.exportRef (circuit.vec.get (63 - i.val) (by omega)))
  { nodes := AigExport.exportNodes circuit.aig, outputs }

end AesXorAssignExport

def main : IO Unit := do
  let image := AesXorAssignExport.artifact
  let serialized := (Lean.toJson image).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := AesXorAssignExport.Image) with
  | .error message => throw (IO.userError message)
  | .ok decoded => unless decoded == image do throw (IO.userError "serialization changed artifact")
  (← IO.getStdout).putStrLn serialized
