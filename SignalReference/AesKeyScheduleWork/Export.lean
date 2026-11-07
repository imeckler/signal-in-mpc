import Lean
import TlsMpc.Signal.AesKeyColumns

/-! Unverified native serialization for the proved key-schedule helper circuits. -/

namespace AesKeyHelpersExport
open TlsMpc Std.Tactic.BVDecide

structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  operation : String
  offset : Nat
  distance : Nat := 0
  rotation : Nat := 0
  input_description : String := "secret u64 words MSB-first; output all secret words as little-endian bytes"
  deriving Lean.ToJson, Lean.FromJson, BEq

def artifact (operation : String) (length offset : Nat) (distance rotation : Nat := 0) : Image :=
  let words := (List.range length).map (BVExpr.var (w := 64))
  let bytes := if operation == "copy" then Signal.AesKeyCopy.expr offset words
    else Signal.AesKeyColumns.expr offset distance rotation words
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { name := s!"aes-key-{operation}-{length}-{offset}-{distance}-{rotation}",
    input_bits := 64 * length, input_widths := Array.replicate length 64,
    nodes := AigExport.exportNodes circuit.aig, outputs, operation, offset, distance, rotation }

def images : List Image :=
  [artifact "copy" 16 0,
   artifact "copy" 24 8,
   artifact "columns" 24 16 16 28,
   artifact "columns" 32 24 16 12]

end AesKeyHelpersExport

def main : IO Unit := do
  let images := AesKeyHelpersExport.images
  let serialized := (Lean.toJson images).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := List AesKeyHelpersExport.Image) with
  | .error message => throw (IO.userError message)
  | .ok decoded => unless decoded == images do throw (IO.userError "serialization changed artifacts")
  (← IO.getStdout).putStrLn serialized
