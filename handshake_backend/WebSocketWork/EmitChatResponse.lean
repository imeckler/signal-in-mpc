import Lean
import TlsMpc.TlsChatResponse
open TlsMpc TlsMpc.Signal TlsMpc.TlsChatResponse
structure ChatImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  initial_state : List Nat
  state_bytes : Nat
  expected_offset : Nat
  input_description : String := "shared state,private data/start/end activity masks,byte; output public-eligible valid/finished/success,private body/reset/header masks,shared state; expected uint64 ID/status/length/body/headers never opened"
  deriving Lean.ToJson,Lean.FromJson,BEq
def main (args : List String) : IO Unit := do
  let [text] := args | throw (IO.userError "public message capacity")
  let some capacity := text.toNat? | throw (IO.userError "invalid message capacity")
  unless capacity≤65535 do throw (IO.userError "message capacity exceeds bounded profile")
  let out := runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity
    (ByteCircuit.inputBytes 0 (stateSize+4))
  let circuit := AigExport.compile (ByteCircuit.joinExpr out)
  let outputs := Array.ofFn (fun i : Fin (8*out.length) =>
    AigExport.exportRef (circuit.vec.get (8*out.length-1-i.val) (by omega)))
  let initialState := (stateBytes Word64.concrete (initial Word64.concrete ByteAuth.concrete capacity 0)).map BitVec.toNat
  unless initialState.length==stateSize && out.length==stateSize+6 && expectedOffset+8≤stateSize do
    throw (IO.userError "chat response codec shape mismatch")
  let value : ChatImage := {
    name := "tls-chat-response-"++text,input_bits := 8*(stateSize+4),input_widths := Array.replicate (stateSize+4) 8,
    nodes := AigExport.exportNodes circuit.aig,outputs,initial_state := initialState,state_bytes := stateSize,expected_offset := expectedOffset}
  let encoded := (Lean.toJson value).compress
  let decoded ← match Lean.Json.parse encoded >>= Lean.fromJson? (α := ChatImage) with
    | .ok x => pure x | .error _ => throw (IO.userError "chat artifact roundtrip failure")
  unless decoded==value do throw (IO.userError "chat artifact changed")
  (← IO.getStdout).putStrLn encoded
