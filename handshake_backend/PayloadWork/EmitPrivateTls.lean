import Lean
import TlsMpc.TlsPrivateSeal
open TlsMpc

namespace PrivateTlsExport
structure Image where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  input_description : String
  deriving Lean.ToJson,Lean.FromJson,BEq

def image (mode : String) (capacity : Nat) : Image :=
  let data := ByteCircuit.inputBytes 39 capacity
  let bytes := if mode=="tls-private-inner" then
      let built := TlsPrivateSeal.build ByteAuth.symbolic (.var 37) (.var 38) 0 data
      built.valid :: built.bytes
    else TlsPrivateSeal.sealCore Gcm.symbolic ByteAuth.symbolic
      (ByteCircuit.inputBytes 0 16) (ByteCircuit.inputBytes 16 12) (ByteCircuit.inputBytes 28 8)
      (.var 36) (.var 37) (.var 38) data
  let circuit := AigExport.compile (ByteCircuit.joinExpr bytes)
  let outputs := Array.ofFn (fun i : Fin (8*bytes.length) =>
    AigExport.exportRef (circuit.vec.get (8*bytes.length-1-i.val) (by omega)))
  {name := mode,input_bits := 8*(39+capacity),input_widths := Array.replicate (39+capacity) 8,
   nodes := AigExport.exportNodes circuit.aig,outputs,
   input_description := "key16,iv12,sequenceBE8,computed validity byte,private lengthBE2,fixed-capacity data; status must be authenticated before releasing ciphertext; capacity is a public profile independent of private length/identifiers"}
end PrivateTlsExport

def main (args : List String) : IO Unit := do
  let [mode,text] := args | throw (IO.userError "tls-seal-private-record|tls-private-inner CAPACITY")
  unless mode=="tls-seal-private-record" || mode=="tls-private-inner" do
    throw (IO.userError "unsupported private TLS export")
  let some capacity := text.toNat? | throw (IO.userError "invalid public capacity")
  unless capacity≤16384 do throw (IO.userError "private TLS capacity exceeds record limit")
  let value := PrivateTlsExport.image mode capacity
  let encoded := (Lean.toJson value).compress
  let decoded ← match Lean.Json.parse encoded >>= Lean.fromJson? (α := PrivateTlsExport.Image) with
    | .ok value => pure value | .error _ => throw (IO.userError "private TLS artifact roundtrip failed")
  unless decoded==value do throw (IO.userError "private TLS artifact changed")
  (← IO.getStdout).putStrLn encoded
