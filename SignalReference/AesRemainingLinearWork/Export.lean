import Lean
import TlsMpc.Signal.AesMixPhases

/-! Unverified serialization of the proved phase-conjugation circuits. -/

namespace AesRemainingLinearExport
open TlsMpc Std.Tactic.BVDecide

structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat := 512
  input_widths : Array Nat := Array.replicate 64 8
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "four secret 16-byte blocks; selected actual MixColumns phase; output eight secret little-endian bitplanes"
  deriving Lean.ToJson, Lean.FromJson, BEq

def artifact (phase : Nat) : Image :=
  let bytes := Signal.AesRemainingLinear.expr phase (fun block index => .var (block * 16 + index))
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { name := "aes-mix-columns-" ++ toString phase, nodes := AigExport.exportNodes circuit.aig, outputs }

end AesRemainingLinearExport

def main : IO Unit := do
  let images := [1,2,3].map AesRemainingLinearExport.artifact
  let serialized := (Lean.toJson images).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := List AesRemainingLinearExport.Image) with
  | .error message => throw (IO.userError message)
  | .ok decoded => unless decoded == images do throw (IO.userError "serialization changed artifacts")
  (← IO.getStdout).putStrLn serialized
