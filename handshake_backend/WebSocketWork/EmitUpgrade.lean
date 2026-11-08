import Lean
import TlsMpc.TlsWebSocketUpgrade
open TlsMpc TlsMpc.TlsWebSocketUpgrade
structure UpgradeImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "tls-websocket-upgrade-byte"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  initial_state : List Nat
  state_bytes : Nat
  input_description : String
  deriving Lean.ToJson,Lean.FromJson,BEq
def main (_args : List String) : IO Unit := do
  let raw := ByteCircuit.inputBytes 0 (stateSize+30)
  let out := runByte ByteAuth.symbolic raw
  let circuit := AigExport.compile (ByteCircuit.joinExpr out)
  let outputs := Array.ofFn (fun i : Fin (8*out.length) =>
    AigExport.exportRef (circuit.vec.get (8*out.length-1-i.val) (by omega)))
  let initialState := (stateBytes (start ByteAuth.concrete)).map BitVec.toNat
  unless initialState.length==stateSize && out.length==stateSize+3 do
    throw (IO.userError "upgrade codec shape mismatch")
  let value : UpgradeImage := {
    input_bits := 8*(stateSize+30),
    input_widths := Array.replicate (stateSize+30) 8,nodes := AigExport.exportNodes circuit.aig,
    outputs,initial_state := initialState,state_bytes := stateSize,
    input_description := "shared state,expected public accept28,computed activity mask0/255,byte; output authenticated status/completion,coalesced-WS activity mask,shared state; no private body/length opening"}
  let encoded := (Lean.toJson value).compress
  let decoded ← match Lean.Json.parse encoded >>= Lean.fromJson? (α := UpgradeImage) with
    | .ok x => pure x | .error _ => throw (IO.userError "upgrade artifact roundtrip failure")
  unless decoded==value do throw (IO.userError "upgrade artifact changed")
  (← IO.getStdout).putStrLn encoded
