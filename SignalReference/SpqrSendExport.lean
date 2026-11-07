import Lean
import TlsMpc.Signal.SpqrSend

/-! Unverified JSON transport only; all derivation and message assembly is in
the proved Lean circuit. The active SPQR epoch/payload selection is external. -/
open TlsMpc Std.Tactic.BVDecide

structure SpqrSendImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String
  deriving Lean.ToJson, Lean.FromJson, BEq

def spqrSendImage (inputBytes : Nat) (bytes : List (BVExpr 8)) : SpqrSendImage :=
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { name := "signal-spqr-send", input_bits := 8 * inputBytes,
    input_widths := Array.replicate inputBytes 8,
    nodes := AigExport.exportNodes circuit.aig, outputs,
    input_description := "all secret: version1,SignalCounterBE4,previousBE4,ratchet32,SignalChain32,SPQRChain32,SPQRCounterBE4,epochBE8,kind1,optional chunkIndexBE2+chunk32,sender32,receiver32,plaintext,addresses0/36; output status1,nextSignalChain32,nextSignalCounterBE4,nextSPQRChain32,nextSPQRCounterBE4,Signal wire; reject preserves BOTH old chain states and zeros wire; requires an already selected active epoch and payload; full SPQR state transitions and atomic commit remain external" }

def spqrSendNumber (text : String) : IO Nat :=
  match text.toNat? with
  | some n => pure n
  | none => throw (IO.userError "expected a nonnegative decimal integer")

def spqrSendPresence (text : String) : IO Bool :=
  match text with
  | "none" => pure false
  | "present" => pure true
  | _ => throw (IO.userError "presence must be none or present")

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-spqr-send", size, cw, pw, ew, iw, kw, chunk, addresses] =>
      let size ← spqrSendNumber size
      let cw ← spqrSendNumber cw
      let pw ← spqrSendNumber pw
      let ew ← spqrSendNumber ew
      let iw ← spqrSendNumber iw
      let kw ← spqrSendNumber kw
      let hasChunk ← spqrSendPresence chunk
      let hasAddresses ← spqrSendPresence addresses
      let shape : Signal.Serialization.Shape := ⟨cw, pw, hasAddresses⟩
      let pqShape : Signal.SpqrMessage.Shape := ⟨ew, iw, kw, hasChunk⟩
      unless shape.valid ∧ pqShape.valid do throw (IO.userError "invalid public varint-width profile")
      if size > 1024 then throw (IO.userError "Signal plaintext is limited to 1024 bytes")
      let chunkSize := if hasChunk then 34 else 0
      let addressSize := if hasAddresses then 36 else 0
      let input : Signal.SpqrSend.Input (BVExpr 8) := {
        version := .var 0, counter := ByteCircuit.inputBytes 1 4,
        previous := ByteCircuit.inputBytes 5 4, ratchet := ByteCircuit.inputBytes 9 32,
        chainKey := ByteCircuit.inputBytes 41 32, pqChainKey := ByteCircuit.inputBytes 73 32,
        pqCounter := ByteCircuit.inputBytes 105 4, epoch := ByteCircuit.inputBytes 109 8,
        kind := .var 117,
        chunkIndex := ByteCircuit.inputBytes 118 (if hasChunk then 2 else 0),
        chunkData := ByteCircuit.inputBytes 120 (if hasChunk then 32 else 0),
        sender := ByteCircuit.inputBytes (118 + chunkSize) 32,
        receiver := ByteCircuit.inputBytes (150 + chunkSize) 32,
        plaintext := ByteCircuit.inputBytes (182 + chunkSize) size,
        addresses := ByteCircuit.inputBytes (182 + chunkSize + size) addressSize }
      let bytes := Signal.SpqrSend.sealCore Aes.symbolic Signal.Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape pqShape input
      let image := spqrSendImage (182 + chunkSize + size + addressSize) bytes
      let serialized := (Lean.toJson image).compress
      match Lean.Json.parse serialized >>= Lean.fromJson? (α := SpqrSendImage) with
      | .error message => throw (IO.userError s!"export round-trip failed: {message}")
      | .ok decoded => unless decoded == image do throw (IO.userError "export round-trip changed the artifact")
      (← IO.getStdout).putStrLn serialized
  | _ => throw (IO.userError "expected signal-spqr-send SIZE COUNTER_WIDTH PREVIOUS_WIDTH EPOCH_WIDTH INDEX_WIDTH CHUNK_INDEX_WIDTH none|present none|present")
