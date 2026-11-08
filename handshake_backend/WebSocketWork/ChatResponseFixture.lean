import Lean
import TlsMpc.TlsChatResponse
open TlsMpc TlsMpc.TlsChatResponse
private def unhex (s : String) : IO (List (BitVec 8)) := do
  if s=="-" then return []
  let chars := s.toList.toArray
  unless chars.size%2==0 do throw (IO.userError "odd fixture hex")
  (List.range (chars.size/2)).mapM fun i => do
    let digit (c : Char) := if c>='0' && c<='9' then c.toNat-'0'.toNat else c.toNat-'a'.toNat+10
    return BitVec.ofNat 8 (16*digit chars[2*i]!+digit chars[2*i+1]!)
private def hex (bytes : List (BitVec 8)) : String :=
  String.ofList (bytes.flatMap fun b => ["0123456789abcdef".toList[b.toNat/16]!,"0123456789abcdef".toList[b.toNat%16]!])
def main (args : List String) : IO Unit := do
  let (path,vectors) ← match args with
    | [path] => pure (path,none)
    | [path,vectorPath] => do
      let stream ← IO.FS.Handle.mk vectorPath .write
      pure (path,some stream)
    | _ => throw (IO.userError "fixture file [step vectors]")
  let base := initial Signal.Word64.concrete ByteAuth.concrete 4096 1234
  let idle := process Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete ByteAuth.concrete 4096 base 0 0 0 173
  let begun := process Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete ByteAuth.concrete 4096 base 0 255 0 0
  let repeated := process Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete ByteAuth.concrete 4096 begun.state 0 255 0 0
  let invalid := process Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete ByteAuth.concrete 4096 base 254 0 0 0
  let early := process Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete ByteAuth.concrete 4096 base 0 0 255 0
  unless stateBytes Signal.Word64.concrete idle.state==stateBytes Signal.Word64.concrete base &&
      begun.state.valid==255 && repeated.state.valid==0 && invalid.state.valid==0 && early.state.valid==0 do
    throw (IO.userError "response private activity/start/end contract failed")
  let text ← IO.FS.readFile path
  let mut passed := 0
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let [encoded,idText,acceptedText,successText,bodyPresentText,bodyText,messagePresentText,messageText,headersText] := line.splitOn " " |
      throw (IO.userError "invalid response fixture line")
    let raw ← unhex encoded
    let first := initial Signal.Word64.concrete ByteAuth.concrete 4096 (BitVec.ofNat 64 idText.toNat!)
    let begun := process Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete ByteAuth.concrete 4096 first 0 255 0 0
    let mut acc : State (BitVec 8) (BitVec 64) × List (BitVec 8) × List (BitVec 8) × Nat :=
      (begun.state,[],[],0)
    for (byte,index) in raw.zipIdx do
      let old := acc.1
      let idle := process Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete ByteAuth.concrete 4096 old 0 0 0 173
      unless stateBytes Signal.Word64.concrete idle.state == stateBytes Signal.Word64.concrete old &&
          idle.bodyData==0 && idle.bodyReset==0 && idle.headerData==0 do
        throw (IO.userError "inactive private slot changed parser state")
      let ending : BitVec 8 := if index+1==raw.length then 255 else 0
      let result := process Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete ByteAuth.concrete 4096 old 255 0 ending byte
      unless stateBytes Signal.Word64.concrete (readState Signal.Word64.concrete ByteAuth.concrete (stateBytes Signal.Word64.concrete result.state)) ==
          stateBytes Signal.Word64.concrete result.state do
        throw (IO.userError "response state codec failed")
      if passed%17==0 && (index%3==0 || index+1==raw.length || result.bodyReset==255) then
        if let some stream := vectors then
          let input := stateBytes Signal.Word64.concrete old ++ [255,0,ending,byte]
          let output := [result.state.valid,result.state.finished,result.state.successful,result.bodyData,result.bodyReset,result.headerData] ++
            stateBytes Signal.Word64.concrete result.state
          stream.putStrLn (hex input++" "++hex output)
      let terminal := byte.toNat<128
      let lengthDone := TlsWebSocketUpgrade.get ByteAuth.concrete old.modes 2==255 && terminal
      let bodyReset := result.bodyReset==255
      let messageReset := lengthDone && TlsWebSocketUpgrade.get ByteAuth.concrete old.kinds 2==255
      let messageData := TlsWebSocketUpgrade.get ByteAuth.concrete old.modes 3==255 &&
        TlsWebSocketUpgrade.get ByteAuth.concrete old.kinds 2==255
      let body := if bodyReset then [] else acc.2.1
      let message := if messageReset then [] else acc.2.2.1
      acc := (result.state,if result.bodyData==255 then body++[byte] else body,
        if messageData then message++[byte] else message,
        acc.2.2.2+(if lengthDone && TlsWebSocketUpgrade.get ByteAuth.concrete old.kinds 3==255 then 1 else 0))
    let final := if raw.isEmpty then
        (process Signal.VarintDecode.Spqr.concrete Signal.Word64.concrete ByteAuth.concrete 4096 acc.1 0 0 255 0).state
      else acc.1
    let body ← unhex bodyText
    let message ← unhex messageText
    unless final.valid.toNat==acceptedText.toNat! &&
        (final.valid==0 || (final.successful.toNat==successText.toNat! &&
          final.bodyPresent.toNat==bodyPresentText.toNat! && final.bodyLength.toNat==body.length &&
          acc.2.1==body && final.messagePresent.toNat==messagePresentText.toNat! &&
          acc.2.2.1==message && acc.2.2.2==headersText.toNat!)) do
      throw (IO.userError s!"response case {passed} failed:valid {final.valid.toNat},success {final.successful.toNat}")
    passed := passed+1
  IO.println s!"private chat response fixtures passed {passed}"
