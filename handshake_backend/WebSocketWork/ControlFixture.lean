import Lean
import TlsMpc.TlsWebSocketControl
open TlsMpc TlsMpc.TlsWebSocketControl
private def hex (bytes : List (BitVec 8)) : String :=
  String.ofList (bytes.flatMap fun b => ["0123456789abcdef".toList[b.toNat/16]!,"0123456789abcdef".toList[b.toNat%16]!])
def main (args : List String) : IO Unit := do
  let [tapePath,encodePath] := args | throw (IO.userError "tape vectors / encode vectors")
  let tape ← IO.FS.Handle.mk tapePath .write
  let encoded ← IO.FS.Handle.mk encodePath .write
  let write (s : State (BitVec 8)) (data done opcode byte : BitVec 8) : IO (State (BitVec 8)) := do
    let next := step ByteAuth.concrete s data done opcode byte
    unless stateBytes (readState ByteAuth.concrete (stateBytes next))==stateBytes next do
      throw (IO.userError "control state codec failed")
    tape.putStrLn (hex (stateBytes s++[data,done,opcode,byte])++" "++hex (stateBytes next))
    return next
  for size in [0,1,2,15,125] do
    let mut state := initial ByteAuth.concrete
    for i in List.range (max 1 size) do
      state ← write state (if size==0 then 0 else 255) (if i+1==max 1 size then 255 else 0) 9 (BitVec.ofNat 8 (i*73+17))
    unless state.valid==255 && state.queued==1 && state.kinds[0]?.getD 0==10 &&
        state.lengths[0]?.getD 0==BitVec.ofNat 8 size && state.count==0 && state.data==List.replicate 125 0 do
      throw (IO.userError "control collection/length failed")
    let expected := (List.range 125).map (fun i => if i<size then BitVec.ofNat 8 (i*73+17) else 0)
    unless state.payloads.take 125==expected do throw (IO.userError "control payload changed")
    for opcode in [8,10] do
      if opcode==8 && size != 0 && size != 2 then continue
      let payload : List (BitVec 8) := if opcode==8 && size==2 then [3,232]++List.replicate 123 0 else expected
      let raw := [255,0,BitVec.ofNat 8 size,BitVec.ofNat 8 opcode,167,33,153,58]++payload
      encoded.putStrLn (hex raw++" "++hex (encode ByteAuth.concrete raw))
  let mut burst := initial ByteAuth.concrete
  for _ in List.range 4 do burst ← write burst 0 255 9 0
  unless burst.valid==255 && burst.queued==4 do throw (IO.userError "control burst queue failed")
  burst ← write burst 0 255 9 0
  unless burst.valid==0 do throw (IO.userError "control overflow silently dropped")
  let pong ← write (initial ByteAuth.concrete) 255 255 10 123
  unless pong.valid==255 && pong.queued==0 && pong.count==0 do throw (IO.userError "pong generated a reply")
  for badMask in [1,254] do
    let bad ← write (initial ByteAuth.concrete) badMask 0 9 0
    unless bad.valid==0 do throw (IO.userError "noncanonical control mask accepted")
  for preamble in [[0,0,2,10],[254,0,2,10],[255,1,0,10],[255,0,126,10],[255,0,127,10],[255,0,2,9]] do
    let raw := preamble++[167,33,153,58]++List.replicate 125 0
    let result := encode ByteAuth.concrete raw
    unless result==List.replicate 134 0 do throw (IO.userError "invalid control became normal payload")
    encoded.putStrLn (hex raw++" "++hex result)
  IO.println "private control fixtures passed: collection/empty/125/burst/pong/overflow/masks; fresh-mask native wrapper separate"
