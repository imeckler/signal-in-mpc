import Lean
import TlsMpc.Signal.RatchetStep
open TlsMpc Std.Tactic.BVDecide
structure RatchetStepImage where
  format : String := "tls-mpc-aig-v1"
  name : String := "signal-ratchet-step"
  input_bits : Nat := 265 * 8
  input_widths : Array Nat := Array.replicate 265 8
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String := "shared auth1,oldRoot32,oldPrivate32,oldPublic32,oldSenderChain32,index4,previous4,newPrivate32,newPublic32,receiveAgreement32,sendAgreement32; shared status1,nextState136,receiverChain32,counter4; authenticated two-half candidate; externally justified fresh pair and X25519 agreements"
  deriving Lean.ToJson, Lean.FromJson, BEq

def ratchetStepCore (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (raw : List B) : List B :=
  let old : Signal.RatchetStep.State B := ⟨(raw.drop 1).take 32,(raw.drop 33).take 32,
    (raw.drop 65).take 32,(raw.drop 97).take 32,(raw.drop 129).take 4,(raw.drop 133).take 4⟩
  Signal.RatchetStep.step s a (Signal.OpenResult.get a raw 0) old
    ((raw.drop 137).take 32) ((raw.drop 169).take 32) ((raw.drop 201).take 32) ((raw.drop 233).take 32)

def main (args : List String) : IO Unit := do
  match args with
  | ["signal-ratchet-step"] =>
    let bytes := ratchetStepCore Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 265)
    let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
    let image : RatchetStepImage := {
      nodes := AigExport.exportNodes circuit.aig
      outputs := Array.ofFn (fun (i : Fin (8 * bytes.length)) => AigExport.exportRef (circuit.vec.get (8 * bytes.length - 1 - i.val) (by omega))) }
    let text := (Lean.toJson image).compress
    match Lean.Json.parse text >>= Lean.fromJson? (α := RatchetStepImage) with
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
      unless raw.length == 265 do throw (IO.userError "expected265bytes")
      let result := ratchetStepCore Sha256.concrete ByteAuth.concrete raw
      stdout.putStrLn ((Lean.toJson (result.map BitVec.toNat)).compress)
  | _ => throw (IO.userError "expected signal-ratchet-step or evaluate")
