import Lean
import TlsMpc.Signal.NewRatchetReceive
open TlsMpc Std.Tactic.BVDecide
structure NewRatchetReceiveImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-new-ratchet-receive"
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "secret PQpresence1,oldRoot32,oldPrivate32,oldPublic32,oldSenderChain32,index4,previous4,newPrivate32,newPublic32,receiveAgreement32,sendAgreement32,remote32,PQkey32,sender32,receiver32,addresses36,wire; output status1,nextSenderState136,remote32,receiverChain32,counter4,slots69N,length8,plaintext; selected new-DH first-message transaction; shared pair/agreement provenance external"
  deriving Lean.ToJson, Lean.FromJson, BEq

def receiveCore (d : Signal.VarintDecode.Spqr.Ops B V) (o : Signal.Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (jump count : Nat) (raw : List B) : List B :=
  let old : Signal.RatchetStep.State B := ⟨(raw.drop 1).take 32,(raw.drop 33).take 32,
    (raw.drop 65).take 32,(raw.drop 97).take 32,(raw.drop 129).take 4,(raw.drop 133).take 4⟩
  Signal.NewRatchetReceive.openCore d o aes s a jump count (Signal.OpenResult.get a raw 0) old
    ((raw.drop 137).take 32) ((raw.drop 169).take 32) ((raw.drop 201).take 32) ((raw.drop 233).take 32)
    ((raw.drop 265).take 32) ((raw.drop 297).take 32) ((raw.drop 329).take 32) ((raw.drop 361).take 32)
    (raw.drop 429) ((raw.drop 393).take 36)

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-new-ratchet-receive", jump, count, size] =>
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
    let inputBytes := 429 + size
    let bytes := receiveCore Signal.VarintDecode.Spqr.symbolic Signal.Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic jump count (ByteCircuit.inputBytes 0 inputBytes)
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : NewRatchetReceiveImage := {
      input_bits := inputBytes * 8
      input_widths := Array.replicate inputBytes 8
      nodes := AigExport.exportNodes circuit.aig,
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }
    let text := (Lean.toJson image).compress
    match Lean.Json.parse text >>= Lean.fromJson? (α := NewRatchetReceiveImage) with
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
  | _ => throw (IO.userError "expected signal-new-ratchet-receive SIZE | evaluate")
