import Lean
import TlsMpc.Signal.PrivatePreKeyMessageV1
open TlsMpc
private def fromHex (s : String) : List (BitVec 8) :=
 let c:=s.toList.toArray
 let n (x : Char) := if x≥'0' && x≤'9' then x.toNat-'0'.toNat else x.toNat-'a'.toNat+10
 (List.range (c.size/2)).map (fun i=>BitVec.ofNat 8 (16*n c[2*i]!+n c[2*i+1]!))
def main (args : List String) : IO Unit := do
 let [registration,otp,signedId,kid,base,identity,ct,signal] := args | throw (IO.userError "prekey components")
 let buffer := Signal.PrivateBuffer.fromPublic ByteAuth.concrete 256 (fromHex signal)
 let run (status : BitVec 8) (ciphertext : List (BitVec 8)) :=
  Signal.PrivatePreKeyMessageV1.message Sha256.concrete ByteAuth.concrete status
   (fromHex registration) (fromHex otp) (fromHex signedId) (fromHex kid)
   (fromHex base) (fromHex identity) ciphertext buffer
 let result := Signal.PrivateBuffer.output ByteAuth.concrete (run 255 (fromHex ct))
 let failed := [run 0 (fromHex ct),run 1 (fromHex ct),run 255 ((fromHex ct).set 0 9)]
 unless result.length==1959 && result.head! ==255 && failed.all (fun x=>x.valid==0 && x.data.all (· ==0)) do
  throw (IO.userError "private PreKey envelope gate regression")
 IO.println (Lean.toJson (result.map BitVec.toNat)).compress
