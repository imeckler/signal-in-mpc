import Lean
import TlsMpc.Signal.SkippedReceive
open TlsMpc Std.Tactic.BVDecide
structure SkippedReceiveImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-skipped-receive"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "secret PQpresent1,PQkey32,sender32,receiver32,expectedAddresses36,slots69N,wire; public capacity/wire size; output status,nextStore,lengthBE8,plaintext; first matching skipped seed consumed only on authenticated receive; rejection preserves store"
  deriving Lean.ToJson, Lean.FromJson, BEq

def receiveCore (d : Signal.VarintDecode.Spqr.Ops B V) (o : Signal.Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (count : Nat) (raw : List B) : List B :=
  let slots := (List.range count).map (fun i =>
    ({
      valid := Signal.OpenResult.get a raw (133 + 69*i)
      key := Signal.SkippedReceive.bytesAt a raw (134 + 69*i)
      counter := Signal.SkippedReceive.bytesAt a raw (166 + 69*i)
      seed := Signal.SkippedReceive.bytesAt a raw (170 + 69*i) } : Signal.SkippedKeys.Slot B))
  Signal.SkippedReceive.openCore d o aes s a (Signal.OpenResult.get a raw 0)
    ((raw.drop 1).take 32) ((raw.drop 33).take 32) ((raw.drop 65).take 32)
    (raw.drop (133 + 69*count)) ((raw.drop 97).take 36) slots

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-skipped-receive", count, size] =>
    let count ← match count.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected capacity")
    if count > 64 then throw (IO.userError "capacity exceeds64")
    let size ← match size.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected size")
    if size > 512 then throw (IO.userError "public wire size exceeds512")
    let inputBytes := 133 + 69 * count + size
    let bytes := receiveCore Signal.VarintDecode.Spqr.symbolic Signal.Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic count (ByteCircuit.inputBytes 0 inputBytes)
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : SkippedReceiveImage := {
      input_bits := inputBytes * 8
      input_widths := Array.replicate inputBytes 8
      nodes := AigExport.exportNodes circuit.aig,
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }
    let text := (Lean.toJson image).compress
    match Lean.Json.parse text >>= Lean.fromJson? (α := SkippedReceiveImage) with
      | .error e => throw (IO.userError e)
      | .ok decoded => unless decoded == image do throw (IO.userError "JSON roundtrip failed")
    (← IO.getStdout).putStrLn text
  | ["evaluate", count] =>
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
      let result := receiveCore Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete count raw
      stdout.putStrLn ((Lean.toJson (result.map BitVec.toNat)).compress)
  | _ => throw (IO.userError "expected signal-skipped-receive SIZE | evaluate")
