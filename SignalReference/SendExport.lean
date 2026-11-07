import Lean
import TlsMpc.Signal.Send

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
  | [mode, size, pqSize, cw, pw, addresses] =>
      let size ← signalSendNumber size
      let pqSize ← signalSendNumber pqSize
      let cw ← signalSendNumber cw
      let pw ← signalSendNumber pw
      let hasAddresses ← match addresses with
        | "none" => pure false
        | "present" => pure true
        | _ => throw (IO.userError "addresses must be none or present")
      let shape : Signal.Serialization.Shape := ⟨cw, pw, hasAddresses⟩
      unless shape.valid do throw (IO.userError "counter widths must be between 1 and 5")
      if size > 1024 || pqSize > 1024 then throw (IO.userError "Signal export inputs are limited to 1024 bytes per payload")
      let addressSize := if hasAddresses then 36 else 0
      let version : BVExpr 8 := .var 0
      let co := ByteCircuit.inputBytes 1 4
      let previous := ByteCircuit.inputBytes 5 4
      let ratchet := ByteCircuit.inputBytes 9 32
      if mode == "signal-serialize" then
        signalSendEmit (signalSendImage mode (41 + size + pqSize + addressSize)
          "secret version, uint32 BE counter/previous, raw ratchet32, ciphertext, PQ, typed addresses0/36; output secret status then serialized content; public lengths/presence/varint widths; reject zeros all bytes"
          (Signal.Serialization.encodeCore Sha256.symbolic ByteAuth.symbolic shape version co previous ratchet
            (ByteCircuit.inputBytes 41 size) (ByteCircuit.inputBytes (41 + size) pqSize)
            (ByteCircuit.inputBytes (41 + size + pqSize) addressSize)))
      else if mode == "signal-send" then
        signalSendEmit (signalSendImage mode (185 + size + pqSize + addressSize)
          "secret version, uint32 BE counter/previous, ratchet32, AES key32, IV16, MAC key32, sender/receiver identity32 each, plaintext, PQ, addresses0/36; output secret status then complete Signal wire; public profile; session transition remains separate"
          (Signal.Send.sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape version co previous ratchet
            (ByteCircuit.inputBytes 41 32) (ByteCircuit.inputBytes 73 16) (ByteCircuit.inputBytes 89 32)
            (ByteCircuit.inputBytes 121 32) (ByteCircuit.inputBytes 153 32)
            (ByteCircuit.inputBytes 185 size) (ByteCircuit.inputBytes (185 + size) pqSize)
            (ByteCircuit.inputBytes (185 + size + pqSize) addressSize)))
      else throw (IO.userError "unknown Signal send export mode")
  | _ => throw (IO.userError "expected signal-serialize|signal-send SIZE PQ_SIZE COUNTER_WIDTH PREVIOUS_WIDTH none|present")
