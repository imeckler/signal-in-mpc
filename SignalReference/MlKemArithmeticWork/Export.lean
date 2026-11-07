import Lean
import TlsMpc.Signal.MlKemArithmetic
open TlsMpc Std.Tactic.BVDecide
structure MlKemArithmeticImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "shared coefficients/entropy/seedNonce; arithmetic requires canonical inputs0..3328, outputs add/sub/mul LE16; CBD/noise outputs256 canonical LE16 coefficients; no full KEM or actual libcrux arithmetic refinement"
  deriving Lean.ToJson, Lean.FromJson, BEq

def operation (r : Signal.MlKemArithmetic.Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (k : Signal.Keccak.Ops B K)
    (mode : String) (eta : Nat) (raw : List B) : List B :=
  if mode == "arithmetic" then
    let x := s.pack (s.byteConst 0) (s.byteConst 0) (Signal.OpenResult.get a raw 1) (Signal.OpenResult.get a raw 0)
    let y := s.pack (s.byteConst 0) (s.byteConst 0) (Signal.OpenResult.get a raw 3) (Signal.OpenResult.get a raw 2)
    Signal.MlKemArithmetic.arithmeticBytes r s x y
  else if mode == "cbd" then Signal.MlKemArithmetic.cbdBytes r s a eta 256 raw
  else Signal.MlKemArithmetic.noise r s a k eta raw

def main (args : List String) : IO Unit := do
  match args with
  | [command,mode,eta] =>
    let eta ← match eta.toNat? with | some n => pure n | none => throw (IO.userError "eta")
    unless eta == 2 || eta == 3 do throw (IO.userError "eta2or3")
    unless mode == "arithmetic" || mode == "cbd" || mode == "noise" do throw (IO.userError "mode")
    let inputBytes := if mode == "arithmetic" then 4 else if mode == "cbd" then 64*eta else 33
    if command == "signal-mlkem" then
      let bytes := operation Signal.MlKemArithmetic.symbolic Sha256.symbolic ByteAuth.symbolic Signal.Keccak.symbolic mode eta (ByteCircuit.inputBytes 0 inputBytes)
      let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
      let image : MlKemArithmeticImage := {
        name := s!"signal-mlkem-{mode}-{eta}"
        input_bits := inputBytes*8
        input_widths := Array.replicate inputBytes 8
        nodes := AigExport.exportNodes circuit.aig
        outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
      let text := (Lean.toJson image).compress
      match Lean.Json.parse text >>= Lean.fromJson? (α := MlKemArithmeticImage) with
        | .error e => throw (IO.userError e)
        | .ok decoded => unless decoded == image do throw (IO.userError "JSON roundtrip")
      (← IO.getStdout).putStrLn text
    else if command == "evaluate" then
      let stdin ← IO.getStdin
      let stdout ← IO.getStdout
      repeat
        let line ← stdin.getLine
        if line.isEmpty then break
        let raw ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
          | .ok ns => pure (ns.map (BitVec.ofNat 8))
          | .error e => throw (IO.userError e)
        unless raw.length == inputBytes do throw (IO.userError "input length")
        stdout.putStrLn ((Lean.toJson ((operation Signal.MlKemArithmetic.concrete Sha256.concrete ByteAuth.concrete Signal.Keccak.concrete mode eta raw).map BitVec.toNat)).compress)
    else throw (IO.userError "command")
  | _ => throw (IO.userError "expected signal-mlkem|evaluate arithmetic|cbd|noise ETA")
