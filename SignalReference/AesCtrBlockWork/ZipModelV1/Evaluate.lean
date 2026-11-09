import AesCtrBlockWork.ZipModelV1.ActualRoundKey
import Lean
open Lean Aeneas Aeneas.Std
open RustCryptoAesZipDiagnostic
namespace ZipFixture

def readWords (j : Json) (fieldName : String) : Except String (List U64) := do
 let values←(←j.getObjVal? fieldName).getArr?
 values.toList.mapM fun value => do
  let n←value.getNat?
  if n<2^64 then .ok ⟨BitVec.ofNat 64 n⟩ else .error "word width"
def slice (xs : List U64) : Except String (Slice U64) :=
 if h:xs.length≤16 then .ok ⟨xs,by scalar_tac⟩ else .error "fixture capacity"
def nat (j : Json) (fieldName : String) : Except String Nat := do (←j.getObjVal? fieldName).getNat?
def wordsJson (xs : List U64) : Json := toJson (xs.map UScalar.val)
def choiceJson : Option (U64×U64) → Json
 | none => .null
 | some (a,b) => toJson [a.val,b.val]
def leftInst : RustCryptoAesZipDiagnostic.core.iter.traits.iterator.Iterator MutIter U64 :=
 ⟨Aeneas.Std.core.slice.iter.IteratorIterMut.next⟩
def next := RustCryptoAesZipDiagnostic.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next leftInst
 (Aeneas.Std.core.iter.traits.iterator.IteratorSliceIter U64)
def drive : Nat → Zip64 → (Zip64→Zip64) → Result (Zip64 × List (Option (U64×U64)) × List Nat)
 | 0,z,back => .ok (back z,[],[])
 | n+1,z,back => do
   let (choice,z',nextBack)←next z
   let returned:=choice.map (fun (a,b)=>(a ^^^ b,b))
   let (last,choices,hints)←drive n z' (fun owner=>back (nextBack owner returned))
   .ok (last,choice::choices,(z'.len-z'.index)::hints)
def run (j : Json) : Except String Json := do
 let mode←(←j.getObjVal? "mode").getStr?
 let state←readWords j "state";let keys←readWords j "keys"
 let a←slice state;let b←slice keys
 if mode="zip" then
  let ai←nat j "left_start";let bi←nat j "right_start";let steps←nat j "steps"
  if ai>state.length||bi>keys.length||steps>24 then throw "fixture bounds"
  let z:=fromIterators ⟨a,ai⟩ ⟨b,bi⟩
  match drive steps z id with
  | .ok (last,choices,hints) =>
    return Json.mkObj [("state",wordsJson last.fst.slice.val),("keys",wordsJson last.snd.slice.val),
      ("yielded",toJson (choices.map choiceJson)),("remaining",toJson hints)]
  | _ => throw "model failed"
 else if mode="add" then
  if h:state.length=8 then
   let input:Array U64 (8#usize):=⟨state,by simpa using h⟩
   match RustCryptoAesZipDiagnostic.soft.fixslice.add_round_key input b with
   | .ok output =>return Json.mkObj [("accepted",toJson true),("state",wordsJson output.val),("preserved",toJson (output.val==state))]
   | .fail .assertionFailure =>return Json.mkObj [("accepted",toJson false),("state",wordsJson state),("preserved",toJson true)]
   | _ =>throw "unexpected model error"
  else throw "state shape"
 else throw "mode"
end ZipFixture

def main : IO Unit := do
 let input←IO.getStdin;let output←IO.getStdout
 repeat
  let line←input.getLine
  if line.isEmpty then break
  let result:=do let j←Json.parse line;ZipFixture.run j
  match result with
  | .ok value=>output.putStrLn value.compress
  | .error error=>throw (IO.userError error)
