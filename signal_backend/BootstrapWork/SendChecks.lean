import Lean
import TlsMpc.Signal.PrivateBootstrapSendV1
open TlsMpc TlsMpc.Signal.PrivateBootstrapSendV1
private def fromHex (s : String) : List (BitVec 8) :=
 let c:=s.toList.toArray
 let n (x : Char) := if x≥'0' && x≤'9' then x.toNat-'0'.toNat else x.toNat-'a'.toNat+10
 (List.range (c.size/2)).map (fun i=>BitVec.ofNat 8 (16*n c[2*i]!+n c[2*i+1]!))
private def js (raw : List (BitVec 8)) := Lean.toJson (raw.map BitVec.toNat)
def main (args : List String) : IO Unit := do
 let [k,g,context,p0,p1] := args | throw (IO.userError "public reference fields")
 let keys:=fromHex k;let generated:=fromHex g;let c:=fromHex context
 let one:=first Aes.concrete Sha256.concrete ByteAuth.concrete keys generated
  (c.take 32) (part c 32 32) (part c 1665 16) (part c 1681 36) (fromHex p0) (part c 96 1569) 255
 let two:=second Aes.concrete Sha256.concrete ByteAuth.concrete (one.take 6040) (fromHex p1) 255
 let rejected:=second Aes.concrete Sha256.concrete ByteAuth.concrete (two.take 6040) (fromHex p1) 255
 unless one.length==7999 && two.length==7999 && one.head! ==255 && two.head! ==255 &&
  rejected.head! ==0 && (rejected.drop 1).take 6039 == (two.drop 1).take 6039 &&
  (rejected.drop 6040).all (· ==0) do throw (IO.userError "initial sender selection regression")
 IO.println (Lean.Json.mkObj [("first_state",js ((one.drop 1).take 6039)),
  ("first_buffer",js (one.drop 6040)),("second_state",js ((two.drop 1).take 6039)),
  ("second_buffer",js (two.drop 6040)),("bounded_entry_reuse_rejected_preserved",Lean.toJson true)]).compress
