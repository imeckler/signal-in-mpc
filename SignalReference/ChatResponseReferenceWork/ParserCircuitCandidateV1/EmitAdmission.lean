import Lean
import ChatResponseReferenceWork.ParserCircuitCandidateV1.AdmissionProgram
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
  let [mode] := args | throw (IO.userError "baseline-admit|candidate-admit")
  unless mode=="baseline-admit" || mode=="candidate-admit" do throw (IO.userError "invalid profile mode")
  let size := if mode=="baseline-admit" then 992 else 592
  let raw := ByteCircuit.inputBytes 0 size
  let out := if mode=="baseline-admit" then TlsChatResponseMux.runAdmit Word64.symbolic ByteAuth.symbolic raw
    else AdmissionExport.run Word64.symbolic ByteAuth.symbolic raw
  unless out.length==(if mode=="baseline-admit" then 982 else 582) do throw (IO.userError "admission shape mismatch")
  let circuit := AigExport.compile (ByteCircuit.joinExpr out)
  let image : CandidateImage := {
    name := "chat-stack32-"++mode,input_bits := 8*size,input_widths := Array.replicate size 8,
    nodes := AigExport.exportNodes circuit.aig,
    outputs := Array.ofFn (fun i : Fin (8*out.length) =>
      AigExport.exportRef (circuit.vec.get (8*out.length-1-i.val) (by omega)))}
  (← IO.getStdout).putStrLn (Lean.toJson image).compress
