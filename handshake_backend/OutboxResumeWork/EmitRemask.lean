import Lean
import TlsMpc.TlsWebSocketRemask
open TlsMpc
structure RemaskImage where
 format : String := "tls-mpc-aig-v1"
 name : String
 input_bits : Nat
 input_widths : Array Nat
 nodes : Array (List Nat)
 outputs : Array (Nat × Nat)
 input_description : String
 deriving Lean.ToJson,Lean.FromJson,BEq
def main (args : List String) : IO Unit := do
 let [text] := args | throw (IO.userError "CAPACITY")
 let some cap := text.toNat? | throw (IO.userError "invalid public capacity")
 unless 134≤cap && cap≤16384 do throw (IO.userError "unsupported capacity")
 let bytes := TlsWebSocketRemask.run ByteAuth.symbolic cap (ByteCircuit.inputBytes 0 (cap+8))
 let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
 let image : RemaskImage := {
  name := "tls-websocket-remask-"++text,input_bits := 8*(cap+8),input_widths := Array.replicate (cap+8) 8,
  nodes := AigExport.exportNodes circuit.aig,
  outputs := Array.ofFn (fun i : Fin (8*bytes.length) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))),
  input_description := "computed account resumability1, typed outbox valid1/BE16len2/data capacity, fresh private VM mask4; supports validated FIN binary masked16bit frames only; output typed validity/BE16len/data, canonical zero padding"}
 let encoded := (Lean.toJson image).compress
 let decoded ← match Lean.Json.parse encoded >>= Lean.fromJson? (α := RemaskImage) with
  | .ok value => pure value | .error _ => throw (IO.userError "roundtrip failed")
 unless decoded==image do throw (IO.userError "image changed")
 (← IO.getStdout).putStrLn encoded
