import Lean
import TlsMpc.Signal.ReceiverStore
open TlsMpc Std.Tactic.BVDecide Signal.ReceiverStore
structure ReceiverStoreImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "shared auth1,ratchet32,nextEntry,oldEntries; entry=valid1,ratchet32,chain32,counter4,skipped69N; oldest first with empty prefix; lookup first match, authenticated replace or append-and-trim"
  deriving Lean.ToJson, Lean.FromJson, BEq

def getBytes (a : ByteAuth.Ops B) (raw : List B) (start : Nat) : Signal.SkippedKeys.Bytes B n :=
  fun i => raw[start+i.val]?.getD (a.const 0)
def getEntry (a : ByteAuth.Ops B) (raw : List B) (start n : Nat) : Entry B n :=
  ⟨raw[start]?.getD (a.const 0),getBytes a raw (start+1),getBytes a raw (start+33),getBytes a raw (start+65),
    fun i => ⟨raw[start+69+69*i.val]?.getD (a.const 0),getBytes a raw (start+70+69*i.val),
      getBytes a raw (start+102+69*i.val),getBytes a raw (start+106+69*i.val)⟩⟩
def storeCore (a : ByteAuth.Ops B) (op : Operation) (capacity skips : Nat) (raw : List B) : List B :=
  run a op (raw[0]?.getD (a.const 0)) (getBytes a raw 1) (getEntry a raw 33 skips)
    ((List.range capacity).map (fun i => getEntry a raw (33+(i+1)*(69+69*skips)) skips))
def main (args : List String) : IO Unit := do
  match args with
  | [mode,operation,capacity,skips] =>
    let capacity ← match capacity.toNat? with | some n => pure n | none => throw (IO.userError "capacity")
    let skips ← match skips.toNat? with | some n => pure n | none => throw (IO.userError "skips")
    if capacity > 5 || skips > 64 then throw (IO.userError "maximum5chains/64skips")
    let op ← match operation with
      | "lookup" => pure Operation.lookup | "replace" => pure Operation.replace | "insert" => pure Operation.insert
      | _ => throw (IO.userError "operation")
    let inputBytes := 33+(capacity+1)*(69+69*skips)
    if mode == "signal-receiver-store" then
      let bytes := storeCore ByteAuth.symbolic op capacity skips (ByteCircuit.inputBytes 0 inputBytes)
      let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
      let image : ReceiverStoreImage := {
        name := s!"signal-receiver-store-{operation}-{capacity}-{skips}"
        input_bits := inputBytes*8
        input_widths := Array.replicate inputBytes 8
        nodes := AigExport.exportNodes circuit.aig
        outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
      let text := (Lean.toJson image).compress
      match Lean.Json.parse text >>= Lean.fromJson? (α := ReceiverStoreImage) with
        | .error e => throw (IO.userError e)
        | .ok decoded => unless decoded == image do throw (IO.userError "JSON roundtrip failed")
      (← IO.getStdout).putStrLn text
    else if mode == "evaluate" then
      let stdin ← IO.getStdin
      let stdout ← IO.getStdout
      repeat
        let line ← stdin.getLine
        if line.isEmpty then break
        let raw ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
          | .ok ns => pure (ns.map (BitVec.ofNat 8))
          | .error e => throw (IO.userError e)
        unless raw.length == inputBytes do throw (IO.userError "input length")
        stdout.putStrLn ((Lean.toJson ((storeCore ByteAuth.concrete op capacity skips raw).map BitVec.toNat)).compress)
    else throw (IO.userError "mode")
  | _ => throw (IO.userError "expected MODE OP CAPACITY SKIPS")
