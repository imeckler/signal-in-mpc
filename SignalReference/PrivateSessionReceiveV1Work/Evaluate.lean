import Lean
import TlsMpc.Signal.PrivateSessionReceiveV1
open TlsMpc.Signal TlsMpc

def evaluate (raw : List (BitVec 8)) : List (BitVec 8) :=
  let a := ByteAuth.concrete
  let field := fun start count => (raw.drop start).take count
  let old : RatchetStep.State (BitVec 8) := ⟨field 0 32,field 32 32,field 64 32,field 96 32,field 128 4,field 132 4⟩
  let receivers : List (ReceiverStore.Entry (BitVec 8) 0) := (List.range 5).map (fun i =>
    let base := 136+69*i
    ⟨OpenResult.get a raw base,PrivateNewDhReceive.listBytes a (field (base+1) 32),
      PrivateNewDhReceive.listBytes a (field (base+33) 32),PrivateNewDhReceive.listBytes a (field (base+65) 4),
      fun j => Fin.elim0 j⟩)
  PrivateSessionReceiveV1.receiveSummary VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete a
    old receivers (field 481 44) (field 525 32) (field 557 32)
    (field 589 32) (field 621 32) (field 653 32) (field 685 32) (field 717 259)
    (PrivateNewDhReceiveSplit.parseSummary VarintDecode.Spqr.concrete Word64.concrete a (field 717 259))

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let raw ← match Lean.Json.parse line >>= Lean.fromJson? (α := List Nat) with
      | .ok values => pure (values.map (BitVec.ofNat 8))
      | .error e => throw (IO.userError e)
    if raw.length != 976 then throw (IO.userError "bounded receiving fixture expects976 bytes")
    stdout.putStrLn (Lean.toJson ((evaluate raw).map BitVec.toNat)).compress
