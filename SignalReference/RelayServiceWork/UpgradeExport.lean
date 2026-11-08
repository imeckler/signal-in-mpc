import Lean
import TlsMpc.Signal.RelayUpgrade
open TlsMpc Std.Tactic.BVDecide
structure UpgradeImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-relay-upgrade"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def main (args : List String) : IO Unit := do
  match args with
  | [text] =>
    let some count := text.toNat? | throw (IO.userError "expected password byte length")
    unless count≤256 do throw (IO.userError "bounded upgrade password")
    let bytes := Signal.RelayUpgrade.request ByteAuth.symbolic count (ByteCircuit.inputBytes 0 (32+count))
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : UpgradeImage := {
      input_bits := 8 * (32 + count)
      input_widths := Array.replicate (32 + count) 8
      nodes := AigExport.exportNodes circuit.aig
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef
        (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }
    (← IO.getStdout).putStrLn (Lean.toJson image).compress
  | _ => throw (IO.userError "expected PASSWORD_BYTES")
