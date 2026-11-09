import Lean
import TlsMpc.Signal.PrivateInitialSpqrV1
open TlsMpc TlsMpc.Signal.PrivateInitialSpqrV1
private def fromHex (s : String) : List (BitVec 8) :=
 let chars := s.toList.toArray
 let n (c : Char) := if c≥'0' && c≤'9' then c.toNat-'0'.toNat else c.toNat-'a'.toNat+10
 (List.range (chars.size/2)).map (fun i => BitVec.ofNat 8 (16*n chars[2*i]!+n chars[2*i+1]!))
private def js (xs : List (BitVec 8)) := Lean.toJson (xs.map BitVec.toNat)
def main (args : List String) : IO Unit := do
 let [auth,generated] := args | throw (IO.userError "auth32 generated3585")
 let g := fromHex generated
 let one := start Sha256.concrete ByteAuth.concrete (fromHex auth) g
 let two := second Sha256.concrete ByteAuth.concrete (one.take 3842)
 let rejected := second Sha256.concrete ByteAuth.concrete (two.take 3842)
 unless one.length==3911 && two.length==3911 && one.head! ==255 && two.head! ==255 &&
   rejected.head! ==0 && (rejected.drop 1).take 3841 == (two.drop 1).take 3841 &&
   (rejected.drop 3842).all (· ==0) do throw (IO.userError "initial SPQR retained state regression")
 let failures := [start Sha256.concrete ByteAuth.concrete (fromHex auth) (g.set 0 0),
  start Sha256.concrete ByteAuth.concrete (fromHex auth) (g.set 0 1),
  start Sha256.concrete ByteAuth.concrete (fromHex auth) (g.set 2401 ((g[2401]?.getD 0) ^^^ 1))]
 unless failures.all (fun out => out.head! == 0 && (out.drop 1).all (· ==0)) do
  throw (IO.userError "initial SPQR KEM gate regression")
 IO.println (Lean.Json.mkObj [("first_state",js (serialize ByteAuth.concrete (State.parse ByteAuth.concrete (one.drop 1)))),
  ("first_message",js ((one.drop 3842).take 37)),("first_key",js (one.drop 3879)),
  ("second_state",js (serialize ByteAuth.concrete (State.parse ByteAuth.concrete (two.drop 1)))),
  ("second_message",js ((two.drop 3842).take 37)),("second_key",js (two.drop 3879)),
  ("rejected_reuse_preserves_state",Lean.toJson true)]).compress
