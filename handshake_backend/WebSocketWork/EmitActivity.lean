import Lean
import TlsMpc.TlsWebSocketActivity
open TlsMpc
structure ActivityImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat := 24
  input_widths : Array Nat := #[8,8,8]
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "computed chunk validity255/0,private BE16 length; authenticate output bounds/source status before private byte processing; remaining outputs0/255 activity masks stay shared"
  deriving Lean.ToJson,Lean.FromJson,BEq
def main (args : List String) : IO Unit := do
  let [text] := args | throw (IO.userError "public capacity")
  let some capacity := text.toNat? | throw (IO.userError "invalid capacity")
  unless capacity≤16385 do throw (IO.userError "receive capacity exceeds TLS bound")
  let out := TlsWebSocketActivity.run ByteAuth.symbolic capacity (.var 0) (.var 1) (.var 2)
  let circuit := AigExport.compile (ByteCircuit.joinExpr out)
  let outputs := Array.ofFn (fun i : Fin (8*out.length) =>
    AigExport.exportRef (circuit.vec.get (8*out.length-1-i.val) (by omega)))
  unless out.length==capacity+1 do throw (IO.userError "activity artifact shape mismatch")
  let value : ActivityImage := {name := "tls-websocket-activity-"++text,nodes := AigExport.exportNodes circuit.aig,outputs}
  let encoded := (Lean.toJson value).compress
  let decoded ← match Lean.Json.parse encoded >>= Lean.fromJson? (α := ActivityImage) with
    | .ok x => pure x | .error _ => throw (IO.userError "activity artifact roundtrip failure")
  unless decoded==value do throw (IO.userError "activity artifact changed")
  (← IO.getStdout).putStrLn encoded
