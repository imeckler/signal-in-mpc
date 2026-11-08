import Lean
import TlsMpc.Signal.RelayRequest
open TlsMpc Std.Tactic.BVDecide
structure RequestImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-relay-websocket-request"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def main (args : List String) : IO Unit := do
  match args with
  | [size,dw,rw,tw,iw] =>
    let some size := size.toNat? | throw (IO.userError "expected sealed size")
    let some dw := dw.toNat? | throw (IO.userError "expected device digits")
    let some rw := rw.toNat? | throw (IO.userError "expected registration digits")
    let some tw := tw.toNat? | throw (IO.userError "expected timestamp digits")
    let some iw := iw.toNat? | throw (IO.userError "expected request id width")
    let shape : Signal.RelayRequest.Shape := ⟨size,dw,rw,tw,iw⟩
    unless shape.valid do throw (IO.userError "invalid relay request shape")
    let bytes := Signal.RelayRequest.encodeCore Signal.RelayEncoding.decimalSymbolic
      Signal.Varint64.symbolic ByteAuth.symbolic shape (ByteCircuit.inputBytes 0 (Signal.RelayRequest.inputBytes shape))
    unless bytes.length≤16384 do throw (IO.userError "request requires private fragmentation")
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : RequestImage := {
      input_bits := 8 * (Signal.RelayRequest.inputBytes shape)
      input_widths := Array.replicate (Signal.RelayRequest.inputBytes shape) 8
      nodes := AigExport.exportNodes circuit.aig
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef
        (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }
    (← IO.getStdout).putStrLn (Lean.toJson image).compress
  | _ => throw (IO.userError "expected SEALED_BYTES DEVICE_DIGITS REGISTRATION_DIGITS TIMESTAMP_DIGITS ID_VARINT_WIDTH")
