import Lean
import TlsMpc.Signal.SpqrEpoch

/-! Unverified transport for proved SPQR epoch key-material operations. -/
open TlsMpc Std.Tactic.BVDecide

structure SpqrEpochImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String
  deriving Lean.ToJson, Lean.FromJson, BEq

def epochImage (name : String) (inputs : Nat) (bytes : List (BVExpr 8)) (description : String) : SpqrEpochImage :=
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { name, input_bits := 8 * inputs, input_widths := Array.replicate inputs 8,
    nodes := AigExport.exportNodes circuit.aig, outputs, input_description := description }

def main (args : List String) : IO Unit := do
  let image ← match args with
    | ["signal-spqr-epoch-new"] => pure (epochImage "signal-spqr-epoch-new" 33
        (Signal.SpqrEpoch.newCore Sha256.symbolic ByteAuth.symbolic (.var 0) (ByteCircuit.inputBytes 1 32))
        "secret direction0=A2B/1=B2A,initialKey32; output status,root32,epochBE8,sendKey32,sendCounterBE4,recvKey32,recvCounterBE4; valid initial epoch and counters zero; invalid direction zeros113bytes; no KEM/state persistence")
    | ["signal-spqr-epoch-add"] => pure (epochImage "signal-spqr-epoch-add" 81
        (Signal.SpqrEpoch.addCore Signal.SpqrEpoch.symbolic Signal.Varint64.symbolic Sha256.symbolic ByteAuth.symbolic
          (.var 0) (ByteCircuit.inputBytes 1 32) (ByteCircuit.inputBytes 33 8)
          (ByteCircuit.inputBytes 41 8) (ByteCircuit.inputBytes 49 32))
        "secret direction0=A2B/1=B2A,root32,currentEpochBE8,proposedEpochBE8,epochSecret32; output status,root32,epochBE8,sendKey32,sendCounterBE4,recvKey32,recvCounterBE4; accepts consecutive nonoverflowing epoch; rejection preserves root/currentEpoch and zeros candidate chains; no links insertion/KEM/atomic commit")
    | _ => throw (IO.userError "expected signal-spqr-epoch-new or signal-spqr-epoch-add")
  let serialized := (Lean.toJson image).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := SpqrEpochImage) with
  | .error message => throw (IO.userError s!"JSON round-trip failed: {message}")
  | .ok decoded => unless decoded == image do throw (IO.userError "JSON round-trip changed artifact")
  (← IO.getStdout).putStrLn serialized
