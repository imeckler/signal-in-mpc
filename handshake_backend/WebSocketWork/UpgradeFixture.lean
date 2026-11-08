import Lean
import TlsMpc.TlsWebSocketUpgrade
open TlsMpc TlsMpc.TlsWebSocketUpgrade
private def unhex (s : String) : IO (List (BitVec 8)) := do
  let chars := s.toList.toArray
  unless chars.size%2==0 do throw (IO.userError "odd fixture hex")
  (List.range (chars.size/2)).mapM fun i => do
    let digit (c : Char) := if c>='0' && c<='9' then c.toNat-'0'.toNat else c.toNat-'a'.toNat+10
    return BitVec.ofNat 8 (16*digit chars[2*i]!+digit chars[2*i+1]!)

private def runChunks (raw : List (BitVec 8)) (sizes : List Nat) : IO (Nat × Nat × List Nat) := do
  let expected := ("s3pPLMBiTxaQ9kYGzzhZRbK+xOo=".toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat))
  let mut state := start ByteAuth.concrete
  let mut remaining := raw
  let mut forwarded : List Nat := []
  for size in sizes do
    let chunk := remaining.take size
    remaining := remaining.drop size
    let padded := chunk ++ List.replicate (size+3-chunk.length) 173
    let result := feed ByteAuth.concrete expected state 255
      (BitVec.ofNat 8 (chunk.length/256)) (BitVec.ofNat 8 chunk.length) padded
    state := result.1
    unless stateBytes (readState ByteAuth.concrete (stateBytes state)) == stateBytes state do
      throw (IO.userError "upgrade state codec failed")
    forwarded := forwarded ++ ((List.zip padded result.2).filter (fun p => p.2==255)).map (fun p => p.1.toNat)
  unless remaining.isEmpty do throw (IO.userError "fixture chunks incomplete")
  return (state.valid.toNat,(get ByteAuth.concrete state.phases 6).toNat,forwarded)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "fixture file")
  let text ← IO.FS.readFile path
  let mut passed := 0
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let [encoded,sizesText,validText,doneText,restText] := line.splitOn " " |
      throw (IO.userError "invalid fixture line")
    let raw ← unhex encoded
    let sizes ← (sizesText.splitOn ",").mapM fun s =>
      match s.toNat? with | some n => pure n | none => throw (IO.userError "invalid size")
    let result ← runChunks raw sizes
    let rest ← if restText=="-" then pure [] else unhex restText
    unless result.1==validText.toNat! && result.2.1==doneText.toNat! &&
        (result.1==0 || result.2.2==rest.map BitVec.toNat) do
      throw (IO.userError s!"upgrade case {passed} failed: status {result.1}/{result.2.1}")
    passed := passed+1
  IO.println s!"upgrade stream fixtures passed {passed}"
