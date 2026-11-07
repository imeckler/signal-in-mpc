import Lean
import TlsMpc.Signal.SpqrMessage

/-! Unverified JSON wrapper; all serialization and checks are compiled Lean. -/
open TlsMpc Std.Tactic.BVDecide

structure SpqrMessageImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-spqr-message"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "secret epochBE8,indexBE4,kind1,optional chunkIndexBE2+chunkData32; output secret acceptance1 and SPQR V1 wire; rejection zeroes wire; public encoded widths and chunk presence"
  deriving Lean.ToJson, Lean.FromJson, BEq

def spqrNumber (value : String) : IO Nat :=
  match value.toNat? with
  | some n => pure n
  | none => throw (IO.userError "expected a nonnegative decimal integer")

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-spqr-message", epochWidth, indexWidth, chunkWidth, chunk] =>
      let epochWidth ← spqrNumber epochWidth
      let indexWidth ← spqrNumber indexWidth
      let chunkWidth ← spqrNumber chunkWidth
      let hasChunk ← match chunk with
        | "none" => pure false
        | "present" => pure true
        | _ => throw (IO.userError "chunk must be none or present")
      let shape : Signal.SpqrMessage.Shape := ⟨epochWidth, indexWidth, chunkWidth, hasChunk⟩
      unless shape.valid do throw (IO.userError "widths must be epoch1..10,index1..5,chunk1..3 if present or0 otherwise")
      let inputBytes := if hasChunk then 47 else 13
      let bytes := Signal.SpqrMessage.encodeCore Signal.Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape
        (Signal.Varint64.pack Signal.Varint64.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 8))
        (Signal.Varint.pack Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 8 4)) (.var 12)
        (ByteCircuit.inputBytes 13 (if hasChunk then 2 else 0))
        (ByteCircuit.inputBytes 15 (if hasChunk then 32 else 0))
      let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
      let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
        AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
      let image : SpqrMessageImage := {
        input_bits := 8 * inputBytes, input_widths := Array.replicate inputBytes 8,
        nodes := AigExport.exportNodes circuit.aig, outputs }
      let serialized := (Lean.toJson image).compress
      match Lean.Json.parse serialized >>= Lean.fromJson? (α := SpqrMessageImage) with
      | .error message => throw (IO.userError s!"export round-trip failed: {message}")
      | .ok decoded => unless decoded == image do throw (IO.userError "export round-trip changed the artifact")
      (← IO.getStdout).putStrLn serialized
  | _ => throw (IO.userError "expected signal-spqr-message EPOCH_WIDTH INDEX_WIDTH CHUNK_WIDTH none|present")
