import Lean
import TlsMpc.TlsWebSocketFrame
import TlsMpc.TlsWebSocketIdle
open TlsMpc TlsMpc.TlsWebSocketFrame
structure FrameImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat := 224
  input_widths : Array Nat := Array.replicate 28 8
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  initial_state : List Nat
  state_bytes : Nat := 26
  input_description : String := "shared frame state26,computed activity mask0/255,byte; output status,private data/control/start/frameDone/messageDone/controlDone masks and controlKind,shared state26; only status may be opened"
  deriving Lean.ToJson,Lean.FromJson,BEq
def main (args : List String) : IO Unit := do
  let (idle,text) ← match args with
    | [text] => pure (false,text)
    | ["idle",text] => pure (true,text)
    | _ => throw (IO.userError "[idle] frame/message capacity")
  let some capacity := text.toNat? | throw (IO.userError "invalid capacity")
  unless capacity≤65535 do throw (IO.userError "frame profile exceeds16-bit limit")
  let out := if idle then TlsWebSocketIdle.run ByteAuth.symbolic capacity (ByteCircuit.inputBytes 0 28)
    else runByte ByteAuth.symbolic capacity (ByteCircuit.inputBytes 0 28)
  let circuit := AigExport.compile (ByteCircuit.joinExpr out)
  let outputs := Array.ofFn (fun i : Fin (8*out.length) =>
    AigExport.exportRef (circuit.vec.get (8*out.length-1-i.val) (by omega)))
  let initialState := (stateBytes (start ByteAuth.concrete capacity)).map BitVec.toNat
  unless initialState.length==26 && out.length==34 do throw (IO.userError "frame codec shape mismatch")
  let value : FrameImage := {
    name := (if idle then "tls-websocket-frame-idle-v2-" else "tls-websocket-frame-v2-")++text,nodes := AigExport.exportNodes circuit.aig,
    outputs,initial_state := initialState}
  let encoded := (Lean.toJson value).compress
  let decoded ← match Lean.Json.parse encoded >>= Lean.fromJson? (α := FrameImage) with
    | .ok x => pure x | .error _ => throw (IO.userError "frame artifact roundtrip failure")
  unless decoded==value do throw (IO.userError "frame artifact changed")
  (← IO.getStdout).putStrLn encoded
