import Lean
import TlsMpc.Signal.PrivateConversationBackend
import TlsMpc.TlsKdf
open TlsMpc Std.Tactic.BVDecide
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
structure ProfileImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  sha_profile : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def main (args : List String) : IO Unit := do
  let [tag,operation] := args | throw (IO.userError "expected PROFILE block|hmac|hkdf|private-hmac")
  let some profile := Sha256Backend.Profile.parse tag | throw (IO.userError "unknown SHA profile")
  let count ← match operation with
    | "block" => pure 96
    | "hmac" | "hkdf" => pure 48
    | "private-hmac" => pure 51
    | _ => throw (IO.userError "unknown profile operation")
  let o := Sha256Backend.select profile Sha256.symbolic
  let a := ByteAuth.symbolic
  let raw := ByteCircuit.inputBytes 0 count
  let words := Sha256.packWords o raw
  let get := fun i => words[i]?.getD (o.wordConst 0)
  let state : Sha256.State (BVExpr 32) := ⟨get 0,get 1,get 2,get 3,get 4,get 5,get 6,get 7⟩
  let bytes ← match operation with
    | "block" => pure (Sha256.digest o (Sha256.compress o state (words.drop 8)))
    | "hmac" => pure (Sha256.hmac o (raw.take 32) (raw.drop 32))
    | "hkdf" => pure (TlsKdf.expandCore o (raw.take 32) (raw.drop 32) 32)
    | "private-hmac" => pure (Signal.PrivateBuffer.output a
        (Signal.PrivateHash.hmac o a (raw.take 32) 16 (Signal.PrivateBuffer.fromWire a 16 (raw.drop 32))))
    | _ => throw (IO.userError "unreachable operation")
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let image : ProfileImage := {
    name := s!"sha-profile-{tag}-{operation}"
    sha_profile := tag
    input_bits := 8*count
    input_widths := Array.replicate count 8
    nodes := AigExport.exportNodes circuit.aig
    outputs := Array.ofFn (fun (i : Fin (8*bytes.length)) => AigExport.exportRef
      (circuit.vec.get (8*bytes.length-1-i.val) (by omega))) }
  (← IO.getStdout).putStrLn (Lean.toJson image).compress
