import Lean
import TlsMpc.Signal.SpqrChain

/-! Unverified JSON transport only; the operation and compiler are Lean. -/
open TlsMpc Std.Tactic.BVDecide

structure SpqrChainImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-spqr-chain"
  input_bits : Nat := 288
  input_widths : Array Nat := Array.replicate 36 8
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "secret SPQR next-chain-key32,counterBE4; output secret status1,next-chain-key32,next-counterBE4,message-key32; exhaustion preserves old state and zeros message key; epoch selection, KEM/chunks and atomic persistence remain separate"
  deriving Lean.ToJson, Lean.FromJson, BEq

def main (args : List String) : IO Unit := do
  unless args == ["signal-spqr-chain"] do throw (IO.userError "expected signal-spqr-chain")
  let bytes := Signal.SpqrChain.stepCore Sha256.symbolic ByteAuth.symbolic
    (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 4)
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  let image : SpqrChainImage := { nodes := AigExport.exportNodes circuit.aig, outputs }
  let serialized := (Lean.toJson image).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := SpqrChainImage) with
  | .error message => throw (IO.userError s!"export round-trip failed: {message}")
  | .ok decoded => unless decoded == image do throw (IO.userError "export round-trip changed the artifact")
  (← IO.getStdout).putStrLn serialized
