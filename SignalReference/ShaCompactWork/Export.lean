import Lean
import TlsMpc.Signal.ShaCompact

/-! Unverified native serialization; no input values or secrets are opened. -/

namespace ShaCompactExport

open TlsMpc Std.Tactic.BVDecide

structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String := "rustcrypto-sha256-compress"
  input_bits : Nat := 768
  input_widths : Array Nat := Array.replicate 24 32
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "eight secret state words then sixteen secret block words, all big-endian u32; output eight secret big-endian u32 state words"
  deriving Lean.ToJson, Lean.FromJson, BEq

def artifact : Image :=
  let state : Sha256.State (BVExpr 32) :=
    ⟨.var 0,.var 1,.var 2,.var 3,.var 4,.var 5,.var 6,.var 7⟩
  let block := (List.range 16).map (fun index => (BVExpr.var (index + 8) : BVExpr 32))
  let bytes := Signal.ShaCompact.bytes Sha256.symbolic state block
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { nodes := AigExport.exportNodes circuit.aig, outputs }

end ShaCompactExport

def main : IO Unit := do
  let image := ShaCompactExport.artifact
  let serialized := (Lean.toJson image).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := ShaCompactExport.Image) with
  | .error message => throw (IO.userError message)
  | .ok decoded => unless decoded == image do throw (IO.userError "serialization changed artifact")
  (← IO.getStdout).putStrLn serialized
