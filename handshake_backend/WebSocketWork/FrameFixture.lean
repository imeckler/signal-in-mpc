import Lean
import TlsMpc.TlsWebSocketFrame
open TlsMpc TlsMpc.TlsWebSocketFrame
private def unhex (s : String) : IO (List (BitVec 8)) := do
  if s=="-" then return []
  let chars := s.toList.toArray
  unless chars.size%2==0 do throw (IO.userError "odd fixture hex")
  (List.range (chars.size/2)).mapM fun i => do
    let digit (c : Char) := if c>='0' && c<='9' then c.toNat-'0'.toNat else c.toNat-'a'.toNat+10
    return BitVec.ofNat 8 (16*digit chars[2*i]!+digit chars[2*i+1]!)
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "fixture file")
  let text ← IO.FS.readFile path
  let mut passed := 0
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let [encoded,validText,framesText,messagesText,controlsText,dataText,controlText] := line.splitOn " " |
      throw (IO.userError "invalid frame fixture line")
    let raw ← unhex encoded
    let mut acc : State (BitVec 8) × List (BitVec 8) × List (BitVec 8) × Nat × Nat × Nat :=
      (start ByteAuth.concrete 4096,[],[],0,0,0)
    for byte in raw do
      let result := step ByteAuth.concrete 4096 acc.1 byte
      unless stateBytes (readState ByteAuth.concrete (stateBytes result.state)) == stateBytes result.state do
        throw (IO.userError "frame state codec failed")
      acc := (result.state,
        if result.data==255 then acc.2.1++[byte] else acc.2.1,
        if result.controlData==255 then acc.2.2.1++[byte] else acc.2.2.1,
        acc.2.2.2.1+(if result.frameDone==255 then 1 else 0),
        acc.2.2.2.2.1+(if result.messageDone==255 then 1 else 0),
        acc.2.2.2.2.2+(if result.controlDone==255 then 1 else 0))
    let state := acc.1
    let data := acc.2.1
    let control := acc.2.2.1
    let frames := acc.2.2.2.1
    let messages := acc.2.2.2.2.1
    let controls := acc.2.2.2.2.2
    let expectedData ← unhex dataText
    let expectedControl ← unhex controlText
    unless state.valid.toNat==validText.toNat! &&
        (state.valid==0 || (frames==framesText.toNat! && messages==messagesText.toNat! &&
          controls==controlsText.toNat! && data==expectedData && control==expectedControl)) do
      throw (IO.userError s!"frame case {passed} failed: valid {state.valid.toNat},frames {frames},messages {messages},controls {controls}")
    passed := passed+1
  IO.println s!"private WebSocket frame fixtures passed {passed}"
