import Lean
import TlsMpc.Signal.ServicePayload
open TlsMpc Std.Tactic.BVDecide
structure GateImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-service-payload"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def main (args : List String) : IO Unit := do
  let fixedMode := args.head? == some "fixed"
  match (if fixedMode then args.drop 1 else args) with
  | [text] =>
    let some cap := text.toNat? | throw (IO.userError "expected fixed service capacity")
    unless cap≤16384 do throw (IO.userError "capacity exceeds TLS contract")
    let count := cap + (if fixedMode then 1 else 2)
    let bytes := if fixedMode then Signal.ServicePayload.fixed ByteAuth.symbolic (ByteCircuit.inputBytes 0 (cap+1)) else
      Signal.ServicePayload.compose ByteAuth.symbolic (.var 0) (ByteCircuit.inputBytes 1 (cap+1))
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : GateImage := {
      name := "signal-service-payload"
      input_bits := 8 * count
      input_widths := Array.replicate count 8
      nodes := AigExport.exportNodes circuit.aig
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef
        (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }
    (← IO.getStdout).putStrLn (Lean.toJson image).compress
  | _ => throw (IO.userError "expected SERVICE_FRAME_CAPACITY")
