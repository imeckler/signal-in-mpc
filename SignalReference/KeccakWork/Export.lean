import Lean
import TlsMpc.Signal.Keccak
open TlsMpc Std.Tactic.BVDecide
structure KeccakImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "shared bytes; public input/output lengths; secret SHA3/SHAKE digest; complete Lean sponge/compiler proof, actual libcrux refinement separate"
  deriving Lean.ToJson, Lean.FromJson, BEq

def config (mode : String) (output : Nat) : IO (Nat × Nat × Nat) :=
  match mode with
  | "sha3-256" => if output == 32 then pure (136,6,32) else throw (IO.userError "sha3-256 output32")
  | "sha3-512" => if output == 64 then pure (72,6,64) else throw (IO.userError "sha3-512 output64")
  | "shake128" => pure (168,31,output)
  | "shake256" => pure (136,31,output)
  | _ => throw (IO.userError "mode")
def main (args : List String) : IO Unit := do
  match args with
  | ["signal-keccak",mode,size,count] =>
    let size ← match size.toNat? with | some n => pure n | none => throw (IO.userError "input size")
    let count ← match count.toNat? with | some n => pure n | none => throw (IO.userError "output size")
    if size > 4096 || count > 4096 then throw (IO.userError "size limit4096")
    let (rate,delimiter,output) ← config mode count
    let bytes := Signal.Keccak.hash Signal.Keccak.symbolic rate delimiter output (ByteCircuit.inputBytes 0 size)
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : KeccakImage := {
      name := s!"signal-keccak-{mode}-{size}-{count}"
      input_bits := size*8
      input_widths := Array.replicate size 8
      nodes := AigExport.exportNodes circuit.aig
      outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
    let text := (Lean.toJson image).compress
    match Lean.Json.parse text >>= Lean.fromJson? (α := KeccakImage) with
      | .error e => throw (IO.userError e)
      | .ok decoded => unless decoded == image do throw (IO.userError "JSON roundtrip")
    (← IO.getStdout).putStrLn text
  | ["evaluate",mode,count] =>
    let count ← match count.toNat? with | some n => pure n | none => throw (IO.userError "output size")
    let (rate,delimiter,output) ← config mode count
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      let raw ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
        | .ok ns => pure (ns.map (BitVec.ofNat 8))
        | .error e => throw (IO.userError e)
      stdout.putStrLn ((Lean.toJson ((Signal.Keccak.hash Signal.Keccak.concrete rate delimiter output raw).map BitVec.toNat)).compress)
  | _ => throw (IO.userError "expected signal-keccak MODE INPUT OUTPUT or evaluate MODE OUTPUT")
