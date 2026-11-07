import Lean
import AesLayoutWork.Circuit

/-! Unverified native serialization used only to inspect the proved circuit. -/

namespace AesLayoutExport
open TlsMpc Std.Tactic.BVDecide

structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String := "aes-bitslice"
  input_bits : Nat := 512
  input_widths : Array Nat := Array.replicate 64 8
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "four secret 16-byte AES blocks; output eight secret little-endian u64 bitplanes"
  deriving Lean.ToJson, Lean.FromJson, BEq

def artifact : Image :=
  let bytes := Signal.AesLayout.expr (fun block index => .var (block * 16 + index))
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { nodes := AigExport.exportNodes circuit.aig, outputs }

end AesLayoutExport

def main : IO Unit := do
  let image := AesLayoutExport.artifact
  let serialized := (Lean.toJson image).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := AesLayoutExport.Image) with
  | .error message => throw (IO.userError message)
  | .ok decoded => unless decoded == image do throw (IO.userError "serialization changed artifact")
  (← IO.getStdout).putStrLn serialized
