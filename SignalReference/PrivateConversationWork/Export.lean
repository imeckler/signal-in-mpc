import Lean
import TlsMpc.Signal.PrivateConversationBackend
open TlsMpc Std.Tactic.BVDecide
structure BufferImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  sha_profile : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def emit (profile : Sha256Backend.Profile) (name : String) (count : Nat) (bytes : List (BVExpr 8)) : IO Unit := do
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let image : BufferImage := {
    name := name
    sha_profile := profile.tag
    input_bits := 8*count
    input_widths := Array.replicate count 8
    nodes := AigExport.exportNodes circuit.aig
    outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef
      (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
  (← IO.getStdout).putStrLn (Lean.toJson image).compress

def main (args : List String) : IO Unit := do
  let (profile,dimensions) ← match args with
    | [cert,size,chunk,addresses] => pure (Sha256Backend.Profile.reference,[cert,size,chunk,addresses])
    | [cert,size,chunk,addresses,tag] =>
      let some profile := Sha256Backend.Profile.parse tag | throw (IO.userError "unsupported SHA profile")
      pure (profile,[cert,size,chunk,addresses])
    | _ => throw (IO.userError "expected CERT_BYTES PLAINTEXT_BYTES none|present none|present [reference|gate-efficient|latency]")
  match dimensions with
  | [certText,sizeText,chunkText,addressText] =>
    let some cert := certText.toNat? | throw (IO.userError "expected certificate size")
    let some size := sizeText.toNat? | throw (IO.userError "expected plaintext size")
    let hasChunk := chunkText == "present"
    let withAddresses := addressText == "present"
    unless cert≤1024 ∧ size≤1024 do throw (IO.userError "bounded established service")
    let chunkSize := if hasChunk then 34 else 0
    let addressSize := if withAddresses then 36 else 0
    let base := 128+cert
    let field := fun offset count => ByteCircuit.inputBytes (base+offset) count
    let i : Signal.SpqrSend.Input (BVExpr 8) := {
      version := .var base,counter := field 1 4,previous := field 5 4,ratchet := field 9 32,
      chainKey := field 41 32,pqChainKey := field 73 32,pqCounter := field 105 4,epoch := field 109 8,
      kind := .var (base+117),chunkIndex := field 118 (if hasChunk then 2 else 0),
      chunkData := field 120 (if hasChunk then 32 else 0),sender := field (118+chunkSize) 32,
      receiver := field (150+chunkSize) 32,plaintext := field (182+chunkSize) size,
      addresses := field (182+chunkSize+size) addressSize }
    let spqrSize := 182+chunkSize+size+addressSize
    let p := Signal.PrivateConversationService.prepare Aes.symbolic Signal.Varint64.symbolic Signal.RelayEncoding.decimalSymbolic
      (Sha256Backend.select profile Sha256.symbolic) ByteAuth.symbolic hasChunk withAddresses
      (ByteCircuit.inputBytes 0 32) (ByteCircuit.inputBytes 32 32) (ByteCircuit.inputBytes 64 32)
      (ByteCircuit.inputBytes 96 32) (ByteCircuit.inputBytes 128 cert)
      (ByteCircuit.inputBytes (base+spqrSize) 57) i
    emit profile "signal-private-variable-conversation" (base+spqrSize+57) (Signal.PrivateConversationService.output ByteAuth.symbolic i (ByteCircuit.inputBytes (base+spqrSize) 57) p)
  | _ => throw (IO.userError "expected CERT_BYTES PLAINTEXT_BYTES none|present none|present")
