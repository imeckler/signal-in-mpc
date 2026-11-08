import Lean
import TlsMpc.TlsChatResponseMux
open TlsMpc TlsMpc.Signal
structure MuxImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  initial_state : List Nat
  state_size : Nat := 982
  slot_offset : Nat := 933
  queue_offset : Nat := 977
  deriving Lean.ToJson,Lean.FromJson,BEq
def main (args : List String) : IO Unit := do
  let [mode] := args | throw (IO.userError "byte|admit")
  unless mode=="byte" || mode=="admit" do throw (IO.userError "invalid mux mode")
  let size := if mode=="byte" then 986 else 992
  let raw := ByteCircuit.inputBytes 0 size
  let out := if mode=="byte" then TlsChatResponseMux.runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic 4096 raw
    else TlsChatResponseMux.runAdmit Word64.symbolic ByteAuth.symbolic raw
  unless out.length==(if mode=="byte" then 985 else 982) do throw (IO.userError "mux output shape")
  let circuit := AigExport.compile (ByteCircuit.joinExpr out)
  let image : MuxImage := {
    name := if mode=="byte" then "tls-chat-mux-byte-4096-4" else "tls-chat-mux-admit-4",
    input_bits := 8*size,input_widths := Array.replicate size 8,
    nodes := AigExport.exportNodes circuit.aig,
    outputs := Array.ofFn (fun i : Fin (8*out.length) => AigExport.exportRef (circuit.vec.get (8*out.length-1-i.val) (by omega))),
    initial_state := (TlsChatResponseMux.stateBytes Word64.concrete (TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete 4096)).map BitVec.toNat}
  let encoded := (Lean.toJson image).compress
  let decoded ← match Lean.Json.parse encoded >>= Lean.fromJson? (α := MuxImage) with
    | .ok value => pure value | .error _ => throw (IO.userError "mux image decode")
  unless decoded==image do throw (IO.userError "mux image mismatch")
  (← IO.getStdout).putStrLn encoded
