import Lean
import TlsMpc.TlsPrivateRequestId
open TlsMpc TlsMpc.Signal
structure RequestIdImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat := 64
  input_widths : Array Nat := Array.replicate 8 8
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson,Lean.FromJson,BEq
def main (args : List String) : IO Unit := do
  let [mode] := args | throw (IO.userError "seed|next")
  unless mode=="seed" || mode=="next" do throw (IO.userError "invalid requestID mode")
  let raw := ByteCircuit.inputBytes 0 8
  let out := if mode=="seed" then TlsPrivateRequestId.seedBytes ByteAuth.symbolic raw
    else TlsPrivateRequestId.runNext Word64.symbolic ByteAuth.symbolic raw
  unless out.length==(if mode=="seed" then 8 else 9) do throw (IO.userError "requestID output shape")
  let circuit := AigExport.compile (ByteCircuit.joinExpr out)
  let image : RequestIdImage := {
    name := "tls-private-request-id-"++mode,
    nodes := AigExport.exportNodes circuit.aig,
    outputs := Array.ofFn (fun i : Fin (8*out.length) => AigExport.exportRef (circuit.vec.get (8*out.length-1-i.val) (by omega)))}
  let encoded := (Lean.toJson image).compress
  let decoded ← match Lean.Json.parse encoded >>= Lean.fromJson? (α := RequestIdImage) with
    | .ok value => pure value | .error _ => throw (IO.userError "requestID image decode")
  unless decoded==image do throw (IO.userError "requestID image mismatch")
  (← IO.getStdout).putStrLn encoded
