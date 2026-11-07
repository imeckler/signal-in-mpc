import Lean
import TlsMpc.Signal.AesShift

/-! Unverified native serialization used only to inspect the proved circuits. -/

namespace AesLinearExport
open TlsMpc Std.Tactic.BVDecide

structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat := 512
  input_widths : Array Nat := Array.replicate 64 8
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "four secret 16-byte AES blocks; output eight secret little-endian u64 bitplanes"
  deriving Lean.ToJson, Lean.FromJson, BEq

def artifact (name : String) (bytes : List (BVExpr 8)) : Image :=
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { name, nodes := AigExport.exportNodes circuit.aig, outputs }

def images : List Image :=
  let input := fun block index => BVExpr.var (block * 16 + index)
  [artifact "aes-mix-columns-0" (Signal.AesLinear.expr input),
   artifact "aes-shift-rows-1" (Signal.AesLinear.shiftExpr input),
   artifact "aes-shift-rows-2" (Signal.AesLinear.shiftNExpr 2 input),
   artifact "aes-shift-rows-3" (Signal.AesLinear.shiftNExpr 3 input)]

end AesLinearExport

def main : IO Unit := do
  let images := AesLinearExport.images
  let serialized := (Lean.toJson images).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := List AesLinearExport.Image) with
  | .error message => throw (IO.userError message)
  | .ok decoded => unless decoded == images do throw (IO.userError "serialization changed artifacts")
  (← IO.getStdout).putStrLn serialized
