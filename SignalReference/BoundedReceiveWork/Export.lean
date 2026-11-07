import Lean
import TlsMpc.Signal.BoundedReceive
open TlsMpc Std.Tactic.BVDecide
structure BoundedReceiveImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-bounded-receive"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "secret PQpresence1,ratchet32,chain32,currentCounter4,PQkey32,sender32,receiver32,expectedAddresses36,slots69N,wire; output status,nextChain32,nextCounter4,nextStore,lengthBE8,plaintext; bounded advance or skipped-key consumption, authenticated transaction; no new DH/SPQR transitions"
  deriving Lean.ToJson, Lean.FromJson, BEq

def receiveCore (d : Signal.VarintDecode.Spqr.Ops B V) (o : Signal.Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (jump count : Nat) (raw : List B) : List B :=
  let slots := (List.range count).map (fun i => ({
      valid := Signal.OpenResult.get a raw (201 + 69 * i)
      key := Signal.SkippedReceive.bytesAt a raw (202 + 69 * i)
      counter := Signal.SkippedReceive.bytesAt a raw (234 + 69 * i)
      seed := Signal.SkippedReceive.bytesAt a raw (238 + 69 * i) } : Signal.SkippedKeys.Slot B))
  Signal.BoundedReceive.openCore d o aes s a jump (Signal.OpenResult.get a raw 0)
    (Signal.SkippedReceive.bytesAt a raw 1) (Signal.SkippedReceive.bytesAt a raw 33)
    (Signal.SkippedReceive.bytesAt a raw 65) slots ((raw.drop 69).take 32)
    ((raw.drop 101).take 32) ((raw.drop 133).take 32) (raw.drop (201 + 69 * count)) ((raw.drop 165).take 36)

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-bounded-receive", jump, count, size] =>
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
    let inputBytes := 201 + 69 * count + size
    let bytes := receiveCore Signal.VarintDecode.Spqr.symbolic Signal.Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic jump count (ByteCircuit.inputBytes 0 inputBytes)
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : BoundedReceiveImage := {
      input_bits := inputBytes * 8
      input_widths := Array.replicate inputBytes 8
      nodes := AigExport.exportNodes circuit.aig,
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }
    let text := (Lean.toJson image).compress
    match Lean.Json.parse text >>= Lean.fromJson? (α := BoundedReceiveImage) with
      | .error e => throw (IO.userError e)
      | .ok decoded => unless decoded == image do throw (IO.userError "JSON roundtrip failed")
    (← IO.getStdout).putStrLn text
  | ["evaluate", jump, count] =>
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
      let result := receiveCore Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete jump count raw
      stdout.putStrLn ((Lean.toJson (result.map BitVec.toNat)).compress)
  | _ => throw (IO.userError "expected signal-bounded-receive SIZE | evaluate")
