import TlsMpc.TlsChatResponseMux
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The parser's100 group-tag words occupy mux byte73..872. Native accepted
protobuf tags fit29bits; this candidate retains four BE bytes per entry. The
reachable-state/carry proof is required before any streaming runtime promotion. -/
def compactStateSize : Nat := 582
def compactInputSize : Nat := 586
def compactOutputSize : Nat := 585

def retainedIndex (index : Nat) : Nat :=
  if index < 73 then index
  else if index < 473 then 73+8*((index-73)/4)+4+(index-73)%4
  else index+400

def compactOutput (a : ByteAuth.Ops B) (full : List B) : List B :=
  (List.range compactOutputSize).map (fun i => TlsWebSocketUpgrade.get a full (retainedIndex i))

/-- Reconstruct the original mux input ABI, preserving all control/data bytes
and inserting only the omitted high32 stack-tag bits as public zeros. -/
def expandInput (a : ByteAuth.Ops B) (compact : List B) : List B :=
  (List.range 986).map (fun i =>
    if i < 73 then TlsWebSocketUpgrade.get a compact i
    else if i < 873 then
      if (i-73)%8 < 4 then a.const 0
      else TlsWebSocketUpgrade.get a compact (73+4*((i-73)/8)+((i-73)%8-4))
    else TlsWebSocketUpgrade.get a compact (i-400))

@[irreducible] def runByte (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (capacity : Nat) (raw : List B) : List B :=
  compactOutput a (TlsChatResponseMux.runByte d o a capacity (expandInput a raw))

/-- Exact one-step observable equality, for every compact input including
malformed masks/bytes. This does not yet assert full-message reachable closure
under re-encoding the next stack after an error or successful group update. -/
theorem one_step_projection (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (capacity : Nat) (raw : List B) :
    runByte d o a capacity raw = compactOutput a (TlsChatResponseMux.runByte d o a capacity (expandInput a raw)) := by
  unfold runByte
  rfl

theorem output_length (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (capacity : Nat) (raw : List B) : (runByte d o a capacity raw).length = compactOutputSize := by
  simp only [runByte,compactOutput,List.length_map,List.length_range]

theorem expand_length (a : ByteAuth.Ops B) (raw : List B) : (expandInput a raw).length = 986 := by
  simp only [expandInput,List.length_map,List.length_range]

#print axioms one_step_projection
#print axioms output_length
#print axioms expand_length
end ChatResponseReference.ParserCircuitCandidateV1
