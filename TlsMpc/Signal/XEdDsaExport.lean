import Lean
import TlsMpc.Signal.XEdDsa
import TlsMpc.Signal.XEdDsaField
import TlsMpc.Signal.XEdDsaBinding
open TlsMpc Std.Tactic.BVDecide

namespace TlsMpc.Signal.XEdDsaExport

structure XEdDsaBooleanImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "All inputs/outputs shared. This stage alone is not signature authentication."
  deriving Lean.ToJson, Lean.FromJson, BEq

def xFieldNode : FieldDag.Node → Lean.Json
  | .input i => Lean.Json.mkObj [("op",Lean.toJson "input"),("index",Lean.toJson i)]
  | .const n => Lean.Json.mkObj [("op",Lean.toJson "const"),("value",Lean.toJson (toString n))]
  | .bin op a b => Lean.Json.mkObj [("op",Lean.toJson (match op with | .add => "add" | .sub => "sub" | .mul => "mul")),
      ("left",Lean.toJson a),("right",Lean.toJson b)]
structure XEdDsaFieldImage where
  format : String := "tls-mpc-field-dag-v1"
  name : String
  modulus : String := toString FieldDag.modulus
  input_count : Nat
  bit_inputs : Array Nat
  nodes : Array Lean.Json
  outputs : Array Nat
  input_description : String := "All inputs/outputs shared. Recover: u -> valid1/0,xCandidate,y. Double: A.x,A.y,256 reduced-h bits LSB first,253 s bits LSB first -> Rcheck.x,y. Signed: root.x,y,flip bit,256 h bits,253 s bits -> Rcheck.x,y. Canonical conversion, signed A binding, SHA512/hash reduction and prekey policy remain required."
  deriving Lean.ToJson, Lean.FromJson, BEq

def xEmit [Lean.ToJson A] [Lean.FromJson A] [BEq A] (value : A) : IO Unit := do
  let text := (Lean.toJson value).compress
  match Lean.Json.parse text >>= Lean.fromJson? (α := A) with
  | .error e => throw (IO.userError e)
  | .ok decoded => unless decoded == value do throw (IO.userError "JSON roundtrip")
  (← IO.getStdout).putStrLn text

def xChallengeOperation (a : ByteAuth.Ops B) (s : Signal.XEdDsaSha512.Ops B W)
    (r : Signal.XEdDsaScalar.Ops B R) (mode : String) (raw : List B) : List B :=
  if mode == "hash" then Signal.XEdDsaSha512.hash s raw
  else if mode == "reduce" then Signal.XEdDsaScalar.reduce r raw
  else if mode == "binding" then Signal.XEdDsaBinding.bind a (raw.take 64) ((raw.drop 64).take 32) (raw.drop 96)
  else if mode == "finish" then Signal.XEdDsaBinding.finish a (raw.take 64) ((raw.drop 64).take 32)
    ((raw.drop 96).take 32) (raw.drop 128)
  else if mode == "prepare" then Signal.XEdDsaBinding.prepare a s r (raw.take 64) ((raw.drop 64).take 32)
    ((raw.drop 96).take 32) (raw.drop 128)
  else Signal.XEdDsaChallenge.run a s r (raw.take 64) ((raw.drop 64).take 32)
    ((raw.drop 96).take 32) (raw.drop 128)

def run (args : List String) : IO Unit := do
  match args with
  | ["field",mode,index] =>
      unless mode == "recover" || mode == "double" || mode == "signed" do throw (IO.userError "mode")
      let index ← match index.toNat? with | some n => pure n | none => throw (IO.userError "index")
      let recovery := mode == "recover"
      unless index < (if recovery then 3 else 2) do throw (IO.userError "output index")
      match FieldDag.compile (if mode == "signed" then Signal.XEdDsaField.signedOutput index else Signal.XEdDsaField.output recovery index) with
      | none => throw (IO.userError "field translation validation failed")
      | some art => xEmit ({
          name := s!"signal-xeddsa-{mode}-{index}"
          input_count := (if recovery then 1 else if mode == "signed" then 512 else 511)
          bit_inputs := (if recovery then #[] else ((List.range (if mode == "signed" then 510 else 509)).map (·+2)).toArray)
          nodes := art.nodes.toArray.map xFieldNode,outputs := #[art.output] } : XEdDsaFieldImage)
  | ["decode",length] =>
      let n ← match length.toNat? with | some n => pure n | none => throw (IO.userError "length")
      unless n ≤ 128 do throw (IO.userError "length cap128")
      let bytes := Signal.XEdDsa.decode ByteAuth.symbolic (ByteCircuit.inputBytes 0 n)
      let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
      xEmit ({
        name := s!"signal-xeddsa-decode-{n}",input_bits := n*8,input_widths := Array.replicate n 8,
        nodes := AigExport.exportNodes circuit.aig,
        outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) } : XEdDsaBooleanImage)
  | ["match"] =>
      let bytes := [Signal.XEdDsa.matchR ByteAuth.symbolic (ByteCircuit.inputBytes 0 64)
        (ByteCircuit.inputBytes 64 32) (ByteCircuit.inputBytes 96 32)]
      let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
      xEmit ({
        name := "signal-xeddsa-match",input_bits := 128*8,input_widths := Array.replicate 128 8,
        nodes := AigExport.exportNodes circuit.aig,
        outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) } : XEdDsaBooleanImage)
  | [command,mode,size] =>
      unless command == "boolean" || command == "evaluate" do throw (IO.userError "command")
      unless mode == "hash" || mode == "reduce" || mode == "challenge" || mode == "prepare" || mode == "binding" || mode == "finish" do throw (IO.userError "mode")
      let n ← match size.toNat? with | some n => pure n | none => throw (IO.userError "length")
      unless n ≤ 2048 && (mode != "reduce" || n == 64) && (mode != "binding" || n == 128) && (mode != "finish" || n == 160) do throw (IO.userError "length cap2048/reduce64")
      let total := if mode == "challenge" || mode == "prepare" then n+128 else n
      if command == "evaluate" then
        let stdin ← IO.getStdin
        let stdout ← IO.getStdout
        repeat
          let line ← stdin.getLine
          if line.isEmpty then break
          let ns ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
            | .ok ns => pure ns | .error e => throw (IO.userError e)
          unless ns.length == total do throw (IO.userError "input length")
          let out := xChallengeOperation ByteAuth.concrete Signal.XEdDsaSha512.concrete
            Signal.XEdDsaScalar.concrete mode (ns.map (BitVec.ofNat 8))
          stdout.putStrLn ((Lean.toJson (out.map BitVec.toNat)).compress)
      else
        let bytes := xChallengeOperation ByteAuth.symbolic Signal.XEdDsaSha512.symbolic
          Signal.XEdDsaScalar.symbolic mode (ByteCircuit.inputBytes 0 total)
        let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
        xEmit ({
          name := s!"signal-xeddsa-{mode}-{n}",input_bits := total*8,input_widths := Array.replicate total 8,
          nodes := AigExport.exportNodes circuit.aig,
          outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) } : XEdDsaBooleanImage)
  | _ => throw (IO.userError "expected field recover|double INDEX, decode LENGTH, match")

/-- Dispatch the shared XEdDSA stage exporter. --/
def tryRun (args : List String) : IO Bool := do
  match args with
  | "signal-xeddsa" :: rest => run rest; pure true
  | _ => pure false

end TlsMpc.Signal.XEdDsaExport
