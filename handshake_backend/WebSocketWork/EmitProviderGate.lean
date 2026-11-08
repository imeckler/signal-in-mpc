import Lean
import TlsMpc.TlsProviderGate
open TlsMpc
open Std.Tactic.BVDecide
structure ProviderGateImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "tls-provider-validity"
  input_bits : Nat := 16
  input_widths : Array Nat := #[8,8]
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson,Lean.FromJson,BEq
def main : IO Unit := do
  let [producer,upstream] := ByteCircuit.inputBytes 0 2 | throw (IO.userError "provider input layout")
  let out := [TlsProviderGate.gate ByteAuth.symbolic producer upstream]
  let circuit := AigExport.compile (ByteCircuit.joinExpr out)
  let image : ProviderGateImage := {
    nodes := AigExport.exportNodes circuit.aig,
    outputs := Array.ofFn (fun i : Fin 8 => AigExport.exportRef (circuit.vec.get (7-i.val) (by simp only [out,List.length_cons,List.length_nil]; omega)))}
  let encoded := (Lean.toJson image).compress
  let decoded ← match Lean.Json.parse encoded >>= Lean.fromJson? (α := ProviderGateImage) with
    | .ok value => pure value | .error _ => throw (IO.userError "provider gate image decode")
  unless decoded==image do throw (IO.userError "provider gate image mismatch")
  (← IO.getStdout).putStrLn encoded
