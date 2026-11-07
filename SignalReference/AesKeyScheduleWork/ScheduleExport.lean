import Lean
import TlsMpc.Signal.AesKeyInput

/-! Native JSON serialization is unverified; its numeric payload uses the
proved compiler. This does not itself prove equivalence to the Rust entrypoint. -/

namespace Aes256ScheduleExport
open TlsMpc Std.Tactic.BVDecide

structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String := "aes256-fixslice-key-schedule"
  input_bits : Nat := 256
  input_widths : Array Nat := Array.replicate 32 8
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "32 secret key bytes; output120 secret little-endian u64 fixslice round-key words"
  deriving Lean.ToJson, Lean.FromJson, BEq

def artifact : Image :=
  let bytes := Signal.AesKeySchedule.keyExpr (fun i => .var i)
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { nodes := AigExport.exportNodes circuit.aig, outputs }

end Aes256ScheduleExport

def main : IO Unit := do
  let image := Aes256ScheduleExport.artifact
  let serialized := (Lean.toJson image).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := Aes256ScheduleExport.Image) with
  | .error message => throw (IO.userError message)
  | .ok decoded => unless decoded == image do throw (IO.userError "serialization changed artifact")
  (← IO.getStdout).putStrLn serialized
