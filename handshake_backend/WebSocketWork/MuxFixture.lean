import Lean
import TlsMpc.TlsChatResponseMux
open TlsMpc TlsMpc.Signal TlsMpc.TlsChatResponseMux
private abbrev S := State (BitVec 8) (BitVec 64)
private def mask (b : Bool) : BitVec 8 := if b then 255 else 0
private def base : S := initial Word64.concrete ByteAuth.concrete 4096
private def add (s : S) (slot id : Nat) (valid : BitVec 8 := 255) : S :=
  admit Word64.concrete ByteAuth.concrete s (BitVec.ofNat 8 slot) (BitVec.ofNat 64 id) valid
private partial def vi (n : Nat) : List Nat :=
  if n<128 then [n] else (n%128+128)::vi (n/128)
private def wire (id : Nat) (status : Nat := 200) : List Nat :=
  let body := [8]++vi id++[16]++vi status++[34,2,123,125]
  [8,2,26]++vi body.length++body
private def byte (s : S) (x : Nat) (active beginning ending : Bool) : S :=
  (process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete 4096 s
    (mask active) (mask beginning) (mask ending) (BitVec.ofNat 8 x)).state
private def stream (s : S) (raw : List Nat) : S :=
  raw.zipIdx.foldl (fun state pair => byte state pair.1 true (pair.2==0) (pair.2+1==raw.length)) s
private def check (condition : Bool) (name : String) : IO Unit :=
  unless condition do throw (IO.userError ("mux fixture: "++name))
private def hex (raw : List (BitVec 8)) : String :=
  String.ofList (raw.flatMap fun value => ["0123456789abcdef".toList[value.toNat/16]!,"0123456789abcdef".toList[value.toNat%16]!])
private def vectorSteps (bytePath admitPath : String) : IO Unit := do
  let bytes ← IO.FS.Handle.mk bytePath .write
  let admissions ← IO.FS.Handle.mk admitPath .write
  let mut state := base
  let id := 2^63+127
  for i in List.range 4 do
    let raw := stateBytes Word64.concrete state ++ [BitVec.ofNat 8 i] ++ Word64.bytes Word64.concrete (BitVec.ofNat 64 (id+i)) ++ [255]
    let out := runAdmit Word64.concrete ByteAuth.concrete raw
    admissions.putStrLn (hex raw++" "++hex out)
    state := readState Word64.concrete ByteAuth.concrete out
  let mut completed := 0
  for selected in [3,1,0,2,3] do
    unless stateBytes Word64.concrete (readState Word64.concrete ByteAuth.concrete (stateBytes Word64.concrete state))==stateBytes Word64.concrete state do
      throw (IO.userError "mux codec roundtrip before message")
    let raw := stateBytes Word64.concrete state ++ [0,255,0,0]
    let out := runByte VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete 4096 raw
    bytes.putStrLn (hex raw++" "++hex out)
    state := readState Word64.concrete ByteAuth.concrete (out.take stateSize)
    let payload := wire (id+selected)
    for pair in payload.zipIdx do
      let raw := stateBytes Word64.concrete state ++ [255,0,mask (pair.2+1==payload.length),BitVec.ofNat 8 pair.1]
      let out := runByte VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete 4096 raw
      bytes.putStrLn (hex raw++" "++hex out)
      state := readState Word64.concrete ByteAuth.concrete (out.take stateSize)
      unless stateBytes Word64.concrete (readState Word64.concrete ByteAuth.concrete (stateBytes Word64.concrete state))==stateBytes Word64.concrete state do
        throw (IO.userError "mux codec roundtrip after byte")
    if completed<4 then
      let expected := ([4,2,1,3] : List (BitVec 8)).take (completed+1) ++ List.replicate (3-completed) 0
      unless state.valid==255 && state.queued==BitVec.ofNat 8 (completed+1) && state.rows==expected do
        throw (IO.userError "mux serialized completion semantics")
    else unless state.valid==0 do throw (IO.userError "mux serialized replay accepted")
    completed := completed+1
def main (args : List String) : IO Unit := do
  let id0 := 2^63+127
  let id1 := 2^63+128
  let start := add (add base 0 id0) 1 id1
  check (start.valid==255) "admission"
  let first := stream start (wire id1)
  check (first.valid==255 && first.queued==1 && first.rows==[2,0,0,0]) "out of order first"
  check ((first.slots[1]?).map (fun slot => (slot.consumed,slot.id))==some (255,0)) "completed ID erased"
  check (first.parser.id==0 && first.parser.expected==0 && first.parser.seen==0) "private parser reset"
  let second := stream first (wire id0)
  check (second.valid==255 && second.queued==2 && second.rows==[2,1,0,0]) "coalesced second"
  let repeated := stream first (wire id1)
  check (repeated.valid==0 && repeated.queued==1) "same chunk replay"
  check ((stream start (wire (id1+1))).valid==0) "unknown ID"
  check ((add start 2 id0).valid==0) "duplicate pending ID"
  check ((add start 0 (id1+1)).valid==0) "occupied slot"
  check ((add start 4 (id1+1)).valid==0) "slot bound"
  check ((add start 2 (id1+1) 127).valid==0) "noncanonical computed validity"
  for status in [100,199,300,401,500,999,1000] do
    check ((stream start (wire id0 status)).valid==0) "non2xx abort policy"
  let raw := wire id1
  let before := (raw.take 5).zipIdx.foldl (fun state pair => byte state pair.1 true (pair.2==0) false) (add base 0 id0)
  let late := add before 1 id1
  let after := (raw.drop 5).zipIdx.foldl (fun state pair => byte state pair.1 true false (pair.2+6==raw.length)) late
  check (after.valid==0) "request admitted after response start"
  let idle := byte start 173 false false false
  check (idle.valid==255 && idle.parser.seen==0 && idle.queued==0) "inactive byte"
  let malformed := (process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete 4096 start 0 0 127 0).state
  check (malformed.valid==0) "malformed end mask"
  check ((byte base 0 false true false).valid==0) "message start without pending slot"
  check ((byte second 0 false true false).valid==0) "coalesced orphan prefix after all completions"
  let all := (List.range 4).foldl (fun state i => add state i (id0+i)) base
  let all := [3,1,0,2].foldl (fun state i => stream state (wire (id0+i))) all
  check (all.valid==255 && all.queued==4 && all.rows==[4,2,1,3]) "four reordered completions"
  check ((stream all (wire id0)).valid==0) "consumed slot replay after full queue"
  match args with
  | [] => pure ()
  | [bytePath,admitPath] => vectorSteps bytePath admitPath
  | _ => throw (IO.userError "[bytevectors admitvectors]")
  IO.println "mux public fixtures passed: private unique correlation, reordering/coalescing/replay, late admission, bounds, ID/parser erasure, non2xx"
