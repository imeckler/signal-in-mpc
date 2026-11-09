import AesCtrBlockWork.FixsliceCircuitV1Work.Cipher16
import Lean
namespace FixslicePublicFixture
open Lean TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open LibSignalReference.Candidate.FixsliceCircuitV1
set_option linter.unusedVariables false

def readBytes (j : Json) (fieldName : String) : Except String (List (BitVec 8)) := do
 let xs←(←j.getObjVal? fieldName).getArr?
 xs.toList.mapM (fun value=>do
  let n←value.getNat?
  if n<256 then .ok (BitVec.ofNat 8 n) else .error "public byte width")
def run (j : Json) : Except String Json := do
 let key←readBytes j "key";let plaintext←readBytes j "plaintext"
 if key.length != 32 || plaintext.isEmpty || plaintext.length % 16 != 0 || plaintext.length > 128 then
  return Json.mkObj [("accepted",toJson false),("error",toJson "shape")]
 let keys:=groupAt 0 (scheduleValue (fun i=>key[i]?.getD 0))
 let blocks:=plaintext.length/16
 let output:=(List.range blocks).flatMap (fun block=>
  let plain:=fun byte=>plaintext[16*block+byte]?.getD 0
  let packed:=network (fun lane byte=>if lane=0 then plain byte else 0)
  let state:=encrypt (concrete16 ⟨0,by decide⟩)
   (fun r=>mapWords (project ⟨0,by decide⟩) (keys r)) (mapWords (project ⟨0,by decide⟩) packed)
  (List.range 16).map (decode16 state))
 return Json.mkObj [("accepted",toJson true),("ciphertext",toJson (output.map BitVec.toNat))]
end FixslicePublicFixture

def main : IO Unit := do
 let input←IO.getStdin;let output←IO.getStdout
 repeat
  let line←input.getLine
  if line.isEmpty then break
  let result:=do let j←Lean.Json.parse line;FixslicePublicFixture.run j
  match result with
  | .ok value=>output.putStrLn value.compress
  | .error error=>throw (IO.userError error)
