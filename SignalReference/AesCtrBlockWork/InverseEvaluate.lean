import AesCtrBlockWork.FactoredInverse
import Lean
set_option linter.unusedVariables false
open Lean Aeneas Aeneas.Std
open LibSignalReference.Candidate.AesCtrInverse
open TlsMpc.Signal.AesLayout

def main : IO Unit := do
 let input←IO.getStdin;let output←IO.getStdout
 repeat
  let line←input.getLine
  if line.isEmpty then break
  let result : Except String Json := do
   let j←Json.parse line
   let values←(←j.getObjVal? "state").getArr?
   let xs←values.toList.mapM fun value=>do
    let n←value.getNat?
    if n<2^64 then .ok (BitVec.ofNat 64 n) else .error "word width"
   if h:xs.length=8 then
    let word : Nat→BitVec 64:=fun i=>xs[i]?.getD 0
    let words : Words (BitVec 64):=⟨word 0,word 1,word 2,word 3,word 4,word 5,word 6,word 7⟩
    return Json.mkObj [("accepted",toJson true),("blocks",toJson ((inverseResult words).val.map fun block=>block.val.map UScalar.val))]
   else return Json.mkObj [("accepted",toJson false)]
  match result with
  | .ok value=>output.putStrLn value.compress
  | .error error=>throw (IO.userError error)
