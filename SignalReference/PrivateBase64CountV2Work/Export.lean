import Lean
import TlsMpc.Signal.PrivateBase64CountV2
open TlsMpc
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
structure CountImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def main (args : List String) : IO Unit := do
  let [version,text,state] := args | throw (IO.userError "expected legacy|balanced GROUPS fixed|state")
  let some groups := text.toNat? | throw (IO.userError "expected groups")
  unless groups≤22000 do throw (IO.userError "public capacity bound exceeded")
  unless version="legacy" || version="balanced" do throw (IO.userError "unknown version")
  unless state="fixed" || state="state" do throw (IO.userError "unknown initial-state mode")
  let inputCount := if state="state" then 4 else 2
  let a := ByteAuth.symbolic
  let raw := ByteCircuit.inputBytes 0 inputCount
  let bits := Signal.PrivateBuffer.decodeLength a (raw.take 2)
  let total := if state="state" then Signal.PrivateBuffer.decodeLength a (raw.drop 2) else Signal.PrivateBuffer.publicLength a 0
  let result := if version="legacy" then Signal.PrivateBase64.count a bits (List.range groups) total
    else Signal.PrivateBase64CountV2.count a bits (List.range groups) total
  let bytes := Signal.PrivateBuffer.encodeLength a result
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let image : CountImage := {
    name := s!"base64-count-{version}-{groups}-{state}"
    input_bits := 8*inputCount
    input_widths := Array.replicate inputCount 8
    nodes := AigExport.exportNodes circuit.aig
    outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef
      (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
  (← IO.getStdout).putStrLn (Lean.toJson image).compress
