import Lean
import TlsMpc.Signal.PrivateShardedAccountV1
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
structure ShardImage where
 format : String := "tls-mpc-aig-v1"
 name : String := "signal-private-shard-validation-v1"
 input_bits : Nat
 input_widths : Array Nat
 kind : String
 nodes : Array (List Nat)
 outputs : Array (Nat × Nat)
 deriving Lean.ToJson
def main (args : List String) : IO Unit := do
 let kind := args.headD "global"
 if kind != "global" && kind != "conversation" then throw (IO.userError "shard validation kind")
 let count := if kind=="global" then 8306 else 20917
 let raw := ByteCircuit.inputBytes 0 count
 let output := [if kind=="global" then PrivateShardedAccountV1.globalValid ByteAuth.symbolic raw else
  PrivateShardedAccountV1.conversationValid Sha256.symbolic Word64.symbolic ByteAuth.symbolic (raw.take 8306) (raw.drop 8306)]
 let circuit := AigExport.compile (ByteCircuit.joinExpr output)
 let image : ShardImage := {
  input_bits := 8*count
  input_widths := Array.replicate count 8
  kind := kind
  nodes := AigExport.exportNodes circuit.aig
  outputs := Array.ofFn (fun (i : Fin (8*output.length)) => AigExport.exportRef
    (circuit.vec.get (8*output.length-1-i.val) (by omega))) }

 (← IO.getStdout).putStrLn (Lean.toJson image).compress
