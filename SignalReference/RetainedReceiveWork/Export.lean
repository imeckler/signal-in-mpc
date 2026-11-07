import Lean
import TlsMpc.Signal.RetainedReceive
open TlsMpc Std.Tactic.BVDecide
structure RetainedReceiveImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-retained-receive"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "shared PQpresence1,PQkey32,sender32,receiver32,addresses36,retainedEntries,wire; entries=valid1,ratchet32,chain32,counter4,skipped69N; output status1,nextEntries,length8,plaintext; first matching retained chain selected secretly, authenticated bounded advancement/consume; sender/root unchanged"
  deriving Lean.ToJson, Lean.FromJson, BEq

def getBytes (a : ByteAuth.Ops B) (raw : List B) (start : Nat) : Signal.SkippedKeys.Bytes B n :=
  fun i => raw[start+i.val]?.getD (a.const 0)
def getEntry (a : ByteAuth.Ops B) (raw : List B) (start n : Nat) : Signal.ReceiverStore.Entry B n :=
  ⟨raw[start]?.getD (a.const 0),getBytes a raw (start+1),getBytes a raw (start+33),getBytes a raw (start+65),
    fun i => ⟨raw[start+69+69*i.val]?.getD (a.const 0),getBytes a raw (start+70+69*i.val),
      getBytes a raw (start+102+69*i.val),getBytes a raw (start+106+69*i.val)⟩⟩
def receiveCore (d : Signal.VarintDecode.Spqr.Ops B V) (o : Signal.Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (jump chains count : Nat) (raw : List B) : List B :=
  let old := (List.range chains).map (fun i => getEntry a raw (133+i*(69+69*count)) count)
  Signal.RetainedReceive.openCore d o aes s a jump (Signal.OpenResult.get a raw 0) old
    ((raw.drop 1).take 32) ((raw.drop 33).take 32) ((raw.drop 65).take 32)
    (raw.drop (133+chains*(69+69*count))) ((raw.drop 97).take 36)

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-retained-receive", jump, chains, count, size] =>
    let chains ← match chains.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected chains")
    if chains > 5 then throw (IO.userError "max5 receiver chains")
    let jump ← match jump.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected maxJump")
    if jump > 16 then throw (IO.userError "maximum export maxJump16")
    let count ← match count.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected capacity")
    if count > 64 then throw (IO.userError "capacity exceeds64")
    let size ← match size.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected size")
    if size > 512 then throw (IO.userError "public wire size exceeds512")
    let inputBytes := 133 + chains * (69 + 69 * count) + size
    let bytes := receiveCore Signal.VarintDecode.Spqr.symbolic Signal.Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic jump chains count (ByteCircuit.inputBytes 0 inputBytes)
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : RetainedReceiveImage := {
      input_bits := inputBytes * 8
      input_widths := Array.replicate inputBytes 8
      nodes := AigExport.exportNodes circuit.aig,
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }
    let text := (Lean.toJson image).compress
    match Lean.Json.parse text >>= Lean.fromJson? (α := RetainedReceiveImage) with
      | .error e => throw (IO.userError e)
      | .ok decoded => unless decoded == image do throw (IO.userError "JSON roundtrip failed")
    (← IO.getStdout).putStrLn text
  | ["evaluate", jump, chains, count] =>
    let chains ← match chains.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected chains")
    if chains > 5 then throw (IO.userError "max5 receiver chains")
    let jump ← match jump.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected maxJump")
    if jump > 16 then throw (IO.userError "maximum export maxJump16")
    let count ← match count.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected capacity")
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      let raw ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
        | .ok ns => pure (ns.map (BitVec.ofNat 8))
        | .error e => throw (IO.userError e)
      let result := receiveCore Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete jump chains count raw
      stdout.putStrLn ((Lean.toJson (result.map BitVec.toNat)).compress)
  | _ => throw (IO.userError "expected signal-retained-receive SIZE | evaluate")
