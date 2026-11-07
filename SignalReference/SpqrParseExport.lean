import Lean
import TlsMpc.Signal.SpqrParseSpec

/-! Unverified JSON transport for the shared SPQR V1 parser. -/
open TlsMpc Std.Tactic.BVDecide

structure SpqrParseImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String
  deriving Lean.ToJson, Lean.FromJson, BEq

def spqrParseImage (inputBytes : Nat) : SpqrParseImage :=
  let bytes := Signal.SpqrParse.parseCore Signal.VarintDecode.Spqr.symbolic ByteAuth.symbolic
    (ByteCircuit.inputBytes 0 inputBytes)
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
    AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega)))
  { name := "signal-spqr-parse", input_bits := 8 * inputBytes,
    input_widths := Array.replicate inputBytes 8,
    nodes := AigExport.exportNodes circuit.aig, outputs,
    input_description := "shared SPQR V1 wire; public buffer length only; secret49-byte output=status255/0,epochBE8,indexBE4,kind1,hasChunk0/1,chunkIndexBE2,chunkData32; rejection zeros all49bytes; accepts noncanonical varints and trailing bytes; no state/KEM transition or V0 negotiation" }

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-spqr-parse", size] =>
      let size ← match size.toNat? with
        | some n => pure n
        | none => throw (IO.userError "expected nonnegative wire length")
      if size > 256 then throw (IO.userError "SPQR parser supports public lengths0..256")
      let image := spqrParseImage size
      let serialized := (Lean.toJson image).compress
      match Lean.Json.parse serialized >>= Lean.fromJson? (α := SpqrParseImage) with
      | .error message => throw (IO.userError s!"JSON round-trip failed: {message}")
      | .ok decoded => unless decoded == image do throw (IO.userError "JSON round-trip changed artifact")
      (← IO.getStdout).putStrLn serialized
  | _ => throw (IO.userError "expected signal-spqr-parse SIZE")
