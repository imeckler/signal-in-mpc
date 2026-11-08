import Lean
import TlsMpc.Signal.PrivateSend

/-! Isolated unverified JSON transport while the root Main integration is
pending. Protocol expressions and numeric compiler are the proved root modules.
Like Main, this transports the numeric DAG and round-trips the JSON before use. -/

open TlsMpc Std.Tactic.BVDecide

structure SignalSendImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String
  deriving Lean.ToJson, Lean.FromJson, BEq

def signalSendImage (name : String) (inputBytes : Nat) (description : String)
    (bytes : List (BVExpr 8)) : SignalSendImage :=
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { name, input_bits := 8 * inputBytes, input_widths := Array.replicate inputBytes 8,
    nodes := AigExport.exportNodes circuit.aig, outputs, input_description := description }

def signalSendEmit (image : SignalSendImage) : IO Unit := do
  let serialized := (Lean.toJson image).compress
  match Lean.Json.parse serialized >>= Lean.fromJson? (α := SignalSendImage) with
  | .error message => throw (IO.userError s!"export round-trip failed: {message}")
  | .ok decoded => unless decoded == image do throw (IO.userError "export round-trip changed the artifact")
  (← IO.getStdout).putStrLn serialized

def signalSendNumber (text : String) : IO Nat :=
  match text.toNat? with
  | some n => pure n
  | none => throw (IO.userError "expected a nonnegative decimal integer")

def main (args : List String) : IO Unit := do
  match args with
  | [size,pqSize,addresses] =>
    let size ← signalSendNumber size
    let pqSize ← signalSendNumber pqSize
    let hasAddresses := addresses == "present"
    unless size≤1024 ∧ pqSize≤1024 do throw (IO.userError "bounded private send")
    let addressSize := if hasAddresses then 36 else 0
    let b := Signal.PrivateSend.message Aes.symbolic Sha256.symbolic ByteAuth.symbolic hasAddresses (.var 0)
      (ByteCircuit.inputBytes 1 4) (ByteCircuit.inputBytes 5 4) (ByteCircuit.inputBytes 9 32)
      (ByteCircuit.inputBytes 41 32) (ByteCircuit.inputBytes 73 16) (ByteCircuit.inputBytes 89 32)
      (ByteCircuit.inputBytes 121 32) (ByteCircuit.inputBytes 153 32)
      (ByteCircuit.inputBytes 185 size) (ByteCircuit.inputBytes (185+size) pqSize)
      (ByteCircuit.inputBytes (185+size+pqSize) addressSize)
    signalSendEmit (signalSendImage "private-length-signal-send" (185+size+pqSize+addressSize)
      "Same input layout as SendExport, without public varint widths. Output validity8||BE16 private length||bounded Signal wire."
      (Signal.PrivateBuffer.output ByteAuth.symbolic b))
  | _ => throw (IO.userError "expected PLAINTEXT_SIZE PQ_SIZE none|present")
