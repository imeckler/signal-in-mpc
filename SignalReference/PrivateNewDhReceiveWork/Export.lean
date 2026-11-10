import Lean
import TlsMpc.Signal.PrivateNewDhReceiveProofs
open TlsMpc Std.Tactic.BVDecide
structure BufferImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def emit (name : String) (count : Nat) (bytes : List (BVExpr 8)) : IO Unit := do
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let image : BufferImage := {
    name := name
    input_bits := 8*count
    input_widths := Array.replicate count 8
    nodes := AigExport.exportNodes circuit.aig
    outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef
      (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
  (← IO.getStdout).putStrLn (Lean.toJson image).compress

def main : IO Unit := do
  let raw := ByteCircuit.inputBytes 0 976
  let a := ByteAuth.symbolic
  let field := fun start count => (raw.drop start).take count
  let old : Signal.RatchetStep.State (BVExpr 8) := ⟨field 0 32,field 32 32,field 64 32,field 96 32,field 128 4,field 132 4⟩
  let receivers : List (Signal.ReceiverStore.Entry (BVExpr 8) 0) := (List.range 5).map (fun i =>
    let base := 136+69*i
    ⟨Signal.OpenResult.get a raw base,Signal.PrivateNewDhReceive.listBytes a (field (base+1) 32),
      Signal.PrivateNewDhReceive.listBytes a (field (base+33) 32),Signal.PrivateNewDhReceive.listBytes a (field (base+65) 4),
      fun j => Fin.elim0 j⟩)
  emit "signal-private-new-dh-receive-256-5" 976
    (Signal.PrivateNewDhReceive.receive Signal.VarintDecode.Spqr.symbolic Signal.Word64.symbolic
      AesInverse.symbolic Sha256.symbolic a old receivers (field 481 44) (field 525 32) (field 557 32)
      (field 589 32) (field 621 32) (field 653 32) (field 685 32) (field 717 259))
