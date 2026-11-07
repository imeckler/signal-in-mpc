import Lean
import TlsMpc.Signal.ChainSend

/-! Isolated unverified JSON transport for the proved bounded chain-send
operation. This contains no host-side key derivation or message assembly. -/

open TlsMpc Std.Tactic.BVDecide

structure ChainSendImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String
  deriving Lean.ToJson, Lean.FromJson, BEq

def chainSendImage (inputBytes : Nat) (bytes : List (BVExpr 8)) : ChainSendImage :=
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { name := "signal-chain-send", input_bits := 8 * inputBytes,
    input_widths := Array.replicate inputBytes 8,
    nodes := AigExport.exportNodes circuit.aig, outputs,
    input_description := "secret version1,counterBE4,previousBE4,ratchet32,chainKey32,SPQR-key-present0/1 byte,SPQR-key32,senderIdentity32,receiverIdentity32,plaintext,PQ,addresses0/36; output secret status1,nextChainKey32,nextCounterBE4,complete Signal wire; rejection preserves old chain state and zeros wire; SPQR transition and atomic storage commit remain external" }

def chainSendNumber (text : String) : IO Nat :=
  match text.toNat? with
  | some n => pure n
  | none => throw (IO.userError "expected a nonnegative decimal integer")

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-chain-send", size, pqSize, cw, pw, addresses] =>
      let size ← chainSendNumber size
      let pqSize ← chainSendNumber pqSize
      let cw ← chainSendNumber cw
      let pw ← chainSendNumber pw
      let hasAddresses ← match addresses with
        | "none" => pure false
        | "present" => pure true
        | _ => throw (IO.userError "addresses must be none or present")
      let shape : Signal.Serialization.Shape := ⟨cw, pw, hasAddresses⟩
      unless shape.valid do throw (IO.userError "counter widths must be between1 and5")
      if size > 1024 || pqSize > 1024 then throw (IO.userError "Signal export inputs are limited to1024 bytes per payload")
      let addressSize := if hasAddresses then 36 else 0
      let bytes := Signal.ChainSend.sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape
        (.var 0) (.var 73) (ByteCircuit.inputBytes 1 4) (ByteCircuit.inputBytes 5 4)
        (ByteCircuit.inputBytes 9 32) (ByteCircuit.inputBytes 41 32) (ByteCircuit.inputBytes 74 32)
        (ByteCircuit.inputBytes 106 32) (ByteCircuit.inputBytes 138 32)
        (ByteCircuit.inputBytes 170 size) (ByteCircuit.inputBytes (170 + size) pqSize)
        (ByteCircuit.inputBytes (170 + size + pqSize) addressSize)
      let image := chainSendImage (170 + size + pqSize + addressSize) bytes
      let serialized := (Lean.toJson image).compress
      match Lean.Json.parse serialized >>= Lean.fromJson? (α := ChainSendImage) with
      | .error message => throw (IO.userError s!"export round-trip failed: {message}")
      | .ok decoded => unless decoded == image do throw (IO.userError "export round-trip changed the artifact")
      (← IO.getStdout).putStrLn serialized
  | _ => throw (IO.userError "expected signal-chain-send SIZE PQ_SIZE COUNTER_WIDTH PREVIOUS_WIDTH none|present")
