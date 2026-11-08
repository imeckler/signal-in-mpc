import Lean
import TlsMpc.Signal.PrivateRecordUpdateV1
open TlsMpc TlsMpc.Signal
open PrivateRecordEncodingV1
partial def node (j : Lean.Json) : Except String (Node (BitVec 8)) := do
 let kind ← j.getObjValAs? Nat "kind"
 let tag ← j.getObjValAs? Nat "tag"
 let present ← j.getObjValAs? Nat "present"
 let p := BitVec.ofNat 8 present
 if kind=2 then
  let children ← j.getObjValAs? (List Lean.Json) "children"
  return .message tag p (← children.mapM node)
 else
  let data ← j.getObjValAs? (List Nat) "data"
  let values := data.map (BitVec.ofNat 8)
  let emit ← j.getObjValAs? Bool "emit"
  if kind=0 then
   let size ← j.getObjValAs? Nat "length"
   let a := ByteAuth.concrete
   return .bytes tag p emit (PrivateBuffer.fromPrivate a values.length
     [a.const (size/256),a.const size] values)
  else return .scalar tag p emit values

def main : IO Unit := do
 let stdin ← IO.getStdin;let stdout ← IO.getStdout
 repeat
  let line ← stdin.getLine
  if line.isEmpty then break
  let parsed := do
   let j ← Lean.Json.parse line
   let ns ← j.getObjValAs? (List Lean.Json) "nodes"
   let nodes ← ns.mapM node
   let result ← j.getObjValAs? (List Nat) "result"
   let capacity ← j.getObjValAs? Nat "capacity"
   return (nodes,result.map (BitVec.ofNat 8),capacity)
  let (nodes,result,capacity) ← match parsed with
   | .ok value => pure value
   | .error err => throw (IO.userError err)
  let updated := PrivateRecordUpdateV1.applyReceive ByteAuth.concrete nodes result
  let encoded := encode Sha256.concrete Varint64.concrete ByteAuth.concrete capacity 16 updated
  stdout.putStrLn (Lean.toJson ((PrivateBuffer.output ByteAuth.concrete encoded).map BitVec.toNat)).compress
