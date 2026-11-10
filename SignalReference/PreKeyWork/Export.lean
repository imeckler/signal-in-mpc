import Lean
import TlsMpc.Signal.PreKeyWire
import TlsMpc.Signal.PreKeyValidation
open TlsMpc Std.Tactic.BVDecide
structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "Shared typed key/constructor/validation-prefix stages. Trust result is an explicit external policy boundary; signature statuses are internal outputs of frozen XEdDSA. No production PQXDH wiring."
  deriving Lean.ToJson,Lean.FromJson,BEq

def operation (a : ByteAuth.Ops B) (features : Signal.PreKeyWire.Features) (mode : String) (raw : List B) : List B :=
  if mode == "ec" then Signal.PreKeyWire.ec a raw
  else if mode == "kem" then Signal.PreKeyWire.kem a features raw
  else if mode == "device" then Signal.PreKeyWire.device a raw
  else if mode == "optional" then Signal.PreKeyWire.run a features 3 raw
  else if mode == "construct" then Signal.PreKeyBundle.construct a (raw.take 11) (raw.drop 11)
  else if mode == "finish" then Signal.PreKeyValidation.finish a (raw.take 20)
    (Signal.OpenResult.get a raw 20) (Signal.OpenResult.get a raw 21) (Signal.OpenResult.get a raw 22)
  else Signal.PreKeyValidation.typedFinish a (raw.take 5) ((raw.drop 5).take 20)
    (Signal.OpenResult.get a raw 25) (Signal.OpenResult.get a raw 26) (Signal.OpenResult.get a raw 27)

def main (args : List String) : IO Unit := do
  match args with
  | [command,mode,size,features] =>
    unless command == "export" || command == "evaluate" do throw (IO.userError "command")
    unless ["ec","kem","device","optional","construct","finish","typed-finish"].contains mode do throw (IO.userError "mode")
    let n ← match size.toNat? with | some n => pure n | none => throw (IO.userError "length")
    unless n ≤ 1600 do throw (IO.userError "length cap1600")
    unless (mode != "optional" || n == 2) && (mode != "device" || n == 4) && (mode != "construct" || n == 28) &&
      (mode != "finish" || n == 23) && (mode != "typed-finish" || n == 28) do throw (IO.userError "shape")
    unless features == "base" || features == "all" do throw (IO.userError "features")
    let config : Signal.PreKeyWire.Features := ⟨features == "all",features == "all"⟩
    if command == "evaluate" then
      let stdin ← IO.getStdin
      let stdout ← IO.getStdout
      repeat
        let line ← stdin.getLine
        if line.isEmpty then break
        let ns ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
          | .ok ns => pure ns | .error e => throw (IO.userError e)
        unless ns.length == n do throw (IO.userError "input length")
        stdout.putStrLn ((Lean.toJson ((operation ByteAuth.concrete config mode (ns.map (BitVec.ofNat 8))).map BitVec.toNat)).compress)
    else
      let bytes := operation ByteAuth.symbolic config mode (ByteCircuit.inputBytes 0 n)
      let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
      let image : Image := {
        name := s!"signal-prekey-{mode}-{n}-{features}"
        input_bits := n*8,input_widths := Array.replicate n 8
        nodes := AigExport.exportNodes circuit.aig
        outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
      let text := (Lean.toJson image).compress
      match Lean.Json.parse text >>= Lean.fromJson? (α := Image) with
      | .error e => throw (IO.userError e)
      | .ok decoded => unless decoded == image do throw (IO.userError "JSON roundtrip")
      (← IO.getStdout).putStrLn text
  | _ => throw (IO.userError "export|evaluate ec|kem|device|construct|finish|typed-finish SIZE base|all")
