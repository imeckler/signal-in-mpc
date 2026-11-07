import Lean
import TlsMpc.Signal.ChainReceive
open TlsMpc Std.Tactic.BVDecide
structure ChainReceiveImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-chain-receive"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "secret PQpresence0/1,ratchet32,counterBE4,chain32,PQkey32,sender32,receiver32,expectedAddresses36,wire; output status,nextChain32,nextCounter4,lengthBE8,plaintext; reject preserves chain/counter and zeros length/plaintext; in-order selected-chain only"
  deriving Lean.ToJson, Lean.FromJson, BEq

def receiveCore (d : Signal.VarintDecode.Spqr.Ops B V) (o : Signal.Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (raw : List B) : List B :=
  Signal.ChainReceive.openCore d o aes s a (Signal.OpenResult.get a raw 0)
    ((raw.drop 1).take 32) ((raw.drop 33).take 4) ((raw.drop 37).take 32) ((raw.drop 69).take 32)
    ((raw.drop 101).take 32) ((raw.drop 133).take 32) (raw.drop 201) ((raw.drop 165).take 36)

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-chain-receive", size] =>
    let size ← match size.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected size")
    if size > 512 then throw (IO.userError "public wire size exceeds512")
    let inputBytes := 201 + size
    let bytes := receiveCore Signal.VarintDecode.Spqr.symbolic Signal.Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 inputBytes)
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : ChainReceiveImage := {
      input_bits := inputBytes * 8
      input_widths := Array.replicate inputBytes 8
      nodes := AigExport.exportNodes circuit.aig,
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }
    let text := (Lean.toJson image).compress
    match Lean.Json.parse text >>= Lean.fromJson? (α := ChainReceiveImage) with
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
  | _ => throw (IO.userError "expected signal-chain-receive SIZE | evaluate")
