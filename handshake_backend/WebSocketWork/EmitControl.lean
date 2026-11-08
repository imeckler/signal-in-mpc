import Lean
import TlsMpc.TlsWebSocketControl
open TlsMpc
structure ControlImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  initial_state : List Nat
  input_description : String
  deriving Lean.ToJson,Lean.FromJson,BEq
def main (args : List String) : IO Unit := do
  let [mode] := args | throw (IO.userError "collect|encode")
  unless mode=="collect" || mode=="encode" do throw (IO.userError "invalid control mode")
  let inputs := if mode=="collect" then 640 else 133
  let out := if mode=="collect" then TlsWebSocketControl.run ByteAuth.symbolic (ByteCircuit.inputBytes 0 inputs)
    else TlsWebSocketControl.encode ByteAuth.symbolic (ByteCircuit.inputBytes 0 inputs)
  let circuit := AigExport.compile (ByteCircuit.joinExpr out)
  let outputs := Array.ofFn (fun i : Fin (8*out.length) =>
    AigExport.exportRef (circuit.vec.get (8*out.length-1-i.val) (by omega)))
  unless out.length==(if mode=="collect" then 636 else 134) do throw (IO.userError "control shape mismatch")
  let value : ControlImage := {
    name := "tls-websocket-control-"++mode,input_bits := 8*inputs,input_widths := Array.replicate inputs 8,
    nodes := AigExport.exportNodes circuit.aig,outputs,
    initial_state := (TlsWebSocketControl.stateBytes (TlsWebSocketControl.initial ByteAuth.concrete)).map BitVec.toNat,
    input_description := "bounded four-response queue/125-byte private controls; native encode generates fresh32 random mask bits inside VM, not through external inputs; preserve validity/BE16 length into TLS"}
  let encoded := (Lean.toJson value).compress
  let decoded ← match Lean.Json.parse encoded >>= Lean.fromJson? (α := ControlImage) with
    | .ok x => pure x | .error _ => throw (IO.userError "control artifact roundtrip failure")
  unless decoded==value do throw (IO.userError "control artifact changed")
  (← IO.getStdout).putStrLn encoded
