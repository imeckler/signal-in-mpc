import Lean
import TlsMpc.Signal.ProtoParseProofs

/-! Unverified transport for public fixture and circuit exports. -/
open TlsMpc Std.Tactic.BVDecide

structure ProtoParseImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-protobuf-parse"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "shared original SignalMessage bytes; public wire length only; secret90-byte status/ratchet/counters/body-relative spans; allzero rejection; no authentication"
  deriving Lean.ToJson, Lean.FromJson, BEq

def protoParseImage (size : Nat) : ProtoParseImage :=
  let bytes := Signal.ProtoParse.parseCore Signal.VarintDecode.Spqr.symbolic Signal.Word64.symbolic ByteAuth.symbolic
    (ByteCircuit.inputBytes 0 size)
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  { input_bits := size * 8, input_widths := Array.replicate size 8,
    nodes := AigExport.exportNodes circuit.aig,
    outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) =>
      AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-protobuf-parse", size] =>
    let size ← match size.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected nonnegative size")
    if size > 512 then throw (IO.userError "public wire size exceeds512")
    let image := protoParseImage size
    let serialized := (Lean.toJson image).compress
    match Lean.Json.parse serialized >>= Lean.fromJson? (α := ProtoParseImage) with
      | .error message => throw (IO.userError message)
      | .ok decoded => unless decoded == image do throw (IO.userError "JSON roundtrip changed artifact")
    (← IO.getStdout).putStrLn serialized
  | ["evaluate"] =>
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      let wire ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
        | .ok ns => pure (ns.map (BitVec.ofNat 8))
        | .error e => throw (IO.userError e)
      let result := Signal.ProtoParse.parseChecked Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete ByteAuth.concrete wire
      stdout.putStrLn ((Lean.toJson (result.map (List.map BitVec.toNat))).compress)
  | _ => throw (IO.userError "expected signal-protobuf-parse SIZE | evaluate")
