import Lean
import TlsMpc.Signal.SpqrDecodeAt

/-! Unverified JSON transport for the proved secret SPQR decoder circuits. -/
open TlsMpc Std.Tactic.BVDecide

structure SpqrDecodeImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String
  deriving Lean.ToJson, Lean.FromJson, BEq

def spqrDecodeImage (name : String) (inputBytes : Nat) (bytes : List (BVExpr 8)) (description : String) : SpqrDecodeImage :=
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { name, input_bits := 8 * inputBytes, input_widths := Array.replicate inputBytes 8,
    nodes := AigExport.exportNodes circuit.aig, outputs, input_description := description }

def main (args : List String) : IO Unit := do
  match args with
  | [mode, size] =>
      let size ← match size.toNat? with
        | some n => pure n
        | none => throw (IO.userError "expected nonnegative input size")
      if size > 256 then throw (IO.userError "SPQR decoder export accepts public capacities0..256")
      let image ← match mode with
        | "signal-spqr-decode" => pure (spqrDecodeImage mode size
            (Signal.VarintDecode.Spqr.decodeCore Signal.VarintDecode.Spqr.symbolic ByteAuth.symbolic
              (ByteCircuit.inputBytes 0 size))
            "shared byte input; output secret status255/0,count0..10,valueBE8; failure zeros all10 bytes; exact SPQR noncanonical/tenth-byte truncation semantics; reads at most10 bytes")
        | "signal-spqr-decode-at" => pure (spqrDecodeImage mode (8 + size)
            (Signal.SpqrDecodeAt.decodeCore Signal.VarintDecode.Spqr.symbolic ByteAuth.symbolic
              (ByteCircuit.inputBytes 8 size) (ByteCircuit.inputBytes 0 8))
            "secret offsetBE8 then shared byte input; output secret status255/0,newOffsetBE8,valueBE8; failure preserves original offset and zeros value; no offset-dependent host branch/index; exact SPQR decoder semantics")
        | _ => throw (IO.userError "expected signal-spqr-decode or signal-spqr-decode-at")
      let serialized := (Lean.toJson image).compress
      match Lean.Json.parse serialized >>= Lean.fromJson? (α := SpqrDecodeImage) with
      | .error message => throw (IO.userError s!"JSON round-trip failed: {message}")
      | .ok decoded => unless decoded == image do throw (IO.userError "JSON round-trip changed artifact")
      (← IO.getStdout).putStrLn serialized
  | _ => throw (IO.userError "expected signal-spqr-decode SIZE or signal-spqr-decode-at SIZE")
