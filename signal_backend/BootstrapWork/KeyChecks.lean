import Lean
import TlsMpc.Signal.PrivateBootstrapKeysV1
open TlsMpc TlsMpc.Signal.PrivateBootstrapKeysV1

def bytes (n offset : Nat) : List (BitVec 8) := (List.range n).map (fun i => BitVec.ofNat 8 (i+offset))
def main : IO Unit := do
 let identity := bytes 32 101
 let signed := bytes 32 33
 let dh := bytes 96 1 ++ identity ++ bytes 160 51
 let kem := [255,8] ++ bytes 1568 7 ++ bytes 32 17
 let run (flag : BitVec 8) (ik d k : List (BitVec 8)) :=
   prepareKeys Sha256.concrete ByteAuth.concrete flag ik signed d k
 let good := run 255 identity dh kem
 IO.println (Lean.toJson (good.map BitVec.toNat)).compress
 let badDh := part dh 0 192 ++ List.replicate 32 0 ++ dh.drop 224
 let cases := [run 0 identity dh kem,run 1 identity dh kem,run 255 (bytes 32 102) dh kem,
   run 255 identity badDh kem,run 255 identity dh (0::kem.drop 1),
   run 255 identity dh (255::9::kem.drop 2),run 255 identity (dh.drop 1) kem]
 unless good.length==546 && good.head! == 255 && cases.all (fun x => x.head! == 0 && (x.drop 1).all (· == 0)) do
   throw (IO.userError "bootstrap key selection regression")
 IO.println "bootstrap key selection passed7 rejection profiles"
