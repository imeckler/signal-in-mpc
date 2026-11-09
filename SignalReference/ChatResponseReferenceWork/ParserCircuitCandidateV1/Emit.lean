import Lean
import ChatResponseReferenceWork.ParserCircuitCandidateV1.Stack32Codec
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
open ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
structure CandidateImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def main (args : List String) : IO Unit := do
  let [mode] := args | throw (IO.userError "baseline|mapped-full|candidate")
  unless mode=="baseline" || mode=="mapped-full" || mode=="candidate" do throw (IO.userError "invalid profile mode")
  let size := if mode=="baseline" then 986 else compactInputSize
  let raw := ByteCircuit.inputBytes 0 size
  let out := if mode=="baseline" then
      TlsChatResponseMux.runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic 4096 raw
    else if mode=="mapped-full" then
      TlsChatResponseMux.runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic 4096 (expandInput ByteAuth.symbolic raw)
    else runByte VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic 4096 raw
  unless out.length==(if mode=="candidate" then compactOutputSize else 985) do throw (IO.userError "candidate shape mismatch")
  let circuit := AigExport.compile (ByteCircuit.joinExpr out)
  let image : CandidateImage := {
    name := "chat-stack32-"++mode,input_bits := 8*size,input_widths := Array.replicate size 8,
    nodes := AigExport.exportNodes circuit.aig,
    outputs := Array.ofFn (fun i : Fin (8*out.length) =>
      AigExport.exportRef (circuit.vec.get (8*out.length-1-i.val) (by omega)))}
  (← IO.getStdout).putStrLn (Lean.toJson image).compress
