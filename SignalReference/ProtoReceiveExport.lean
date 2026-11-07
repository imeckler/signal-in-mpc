import Lean
import TlsMpc.Signal.ProtoReceive
open TlsMpc Std.Tactic.BVDecide
structure ProtoReceiveImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-protobuf-receive"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "secret cipherKey32,IV16,macKey32,sender32,receiver32,expectedAddresses36,originalWire; public wire size only; secret status255/0,lengthBE8,padded plaintext; general secret protobuf layout; no key selection or session commit"
  deriving Lean.ToJson, Lean.FromJson, BEq

def receiveCore (d : Signal.VarintDecode.Spqr.Ops B V) (o : Signal.Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (raw : List B) : List B :=
  Signal.ProtoReceive.openCore d o aes s a (raw.take 32) ((raw.drop 32).take 16) ((raw.drop 48).take 32)
    ((raw.drop 80).take 32) ((raw.drop 112).take 32) (raw.drop 180) ((raw.drop 144).take 36)

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-protobuf-receive", size] =>
    let size ← match size.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected size")
    if size > 512 then throw (IO.userError "public wire size exceeds512")
    let inputBytes := 180 + size
    let bytes := receiveCore Signal.VarintDecode.Spqr.symbolic Signal.Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 inputBytes)
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : ProtoReceiveImage := {
      input_bits := inputBytes * 8
      input_widths := Array.replicate inputBytes 8
      nodes := AigExport.exportNodes circuit.aig,
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }
    let text := (Lean.toJson image).compress
    match Lean.Json.parse text >>= Lean.fromJson? (α := ProtoReceiveImage) with
      | .error e => throw (IO.userError e)
      | .ok decoded => unless decoded == image do throw (IO.userError "JSON roundtrip failed")
    (← IO.getStdout).putStrLn text
  | ["evaluate"] =>
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      let raw ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
        | .ok ns => pure (ns.map (BitVec.ofNat 8))
        | .error e => throw (IO.userError e)
      let result := receiveCore Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete raw
      stdout.putStrLn ((Lean.toJson (result.map BitVec.toNat)).compress)
  | _ => throw (IO.userError "expected signal-protobuf-receive SIZE | evaluate")
