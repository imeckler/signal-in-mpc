import Lean
import TlsMpc.Signal.SessionReceive
open TlsMpc Std.Tactic.BVDecide
structure SessionReceiveImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-session-receive"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "shared PQpresence1,oldSenderState136,freshPrivate32,freshPublic32,receiveAgreement32,sendAgreement32,remote32,PQkey32,sender32,receiver32,addresses36,retainedEntries,wire; output status1,nextSenderState136,nextEntries,length8,plaintext; secret retained/new-DH choice; bounded classical transaction, external SPQR key and private X25519 composition"
  deriving Lean.ToJson, Lean.FromJson, BEq

def getBytes (a : ByteAuth.Ops B) (raw : List B) (start : Nat) : Signal.SkippedKeys.Bytes B n :=
  fun i => raw[start+i.val]?.getD (a.const 0)
def getEntry (a : ByteAuth.Ops B) (raw : List B) (start n : Nat) : Signal.ReceiverStore.Entry B n :=
  ⟨raw[start]?.getD (a.const 0),getBytes a raw (start+1),getBytes a raw (start+33),getBytes a raw (start+65),
    fun i => ⟨raw[start+69+69*i.val]?.getD (a.const 0),getBytes a raw (start+70+69*i.val),
      getBytes a raw (start+102+69*i.val),getBytes a raw (start+106+69*i.val)⟩⟩
def receiveCore (d : Signal.VarintDecode.Spqr.Ops B V) (o : Signal.Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (jump chains count : Nat) (raw : List B) : List B :=
  let oldSender : Signal.RatchetStep.State B := ⟨(raw.drop 1).take 32,(raw.drop 33).take 32,
    (raw.drop 65).take 32,(raw.drop 97).take 32,(raw.drop 129).take 4,(raw.drop 133).take 4⟩
  let old := (List.range chains).map (fun i => getEntry a raw (429+i*(69+69*count)) count)
  Signal.SessionReceive.openCore d o aes s a jump (Signal.OpenResult.get a raw 0) oldSender old
    ((raw.drop 137).take 32) ((raw.drop 169).take 32) ((raw.drop 201).take 32) ((raw.drop 233).take 32)
    ((raw.drop 265).take 32) ((raw.drop 297).take 32) ((raw.drop 329).take 32) ((raw.drop 361).take 32)
    (raw.drop (429+chains*(69+69*count))) ((raw.drop 393).take 36)

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-session-receive", jump, chains, count, size] =>
    let chains ← match chains.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected chains")
    if chains == 0 || chains > 5 then throw (IO.userError "max5 receiver chains")
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
    let inputBytes := 429 + chains * (69 + 69 * count) + size
    let bytes := receiveCore Signal.VarintDecode.Spqr.symbolic Signal.Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic jump chains count (ByteCircuit.inputBytes 0 inputBytes)
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : SessionReceiveImage := {
      input_bits := inputBytes * 8
      input_widths := Array.replicate inputBytes 8
      nodes := AigExport.exportNodes circuit.aig,
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }
    let text := (Lean.toJson image).compress
    match Lean.Json.parse text >>= Lean.fromJson? (α := SessionReceiveImage) with
      | .error e => throw (IO.userError e)
      | .ok decoded => unless decoded == image do throw (IO.userError "JSON roundtrip failed")
    (← IO.getStdout).putStrLn text
  | ["evaluate", jump, chains, count] =>
    let chains ← match chains.toNat? with
      | some n => pure n
      | none => throw (IO.userError "expected chains")
    if chains == 0 || chains > 5 then throw (IO.userError "max5 receiver chains")
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
  | _ => throw (IO.userError "expected signal-session-receive SIZE | evaluate")
