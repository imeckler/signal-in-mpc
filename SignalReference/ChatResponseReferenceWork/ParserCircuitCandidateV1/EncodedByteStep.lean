import ChatResponseReferenceWork.ParserCircuitCandidateV1.CompactInput
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

def compactEvent (event : TlsChatResponseMux.Event (BitVec 8) (BitVec 64)) : List (BitVec 8) :=
  compactOutput ByteAuth.concrete (TlsChatResponseMux.stateBytes Word64.concrete event.state ++
    [event.bodyData,event.bodyReset,event.headerData])

theorem mux_runByte_encoded (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (active beginning ending byte : BitVec 8) :
    TlsChatResponseMux.runByte VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity
      (TlsChatResponseMux.stateBytes Word64.concrete state ++ [active,beginning,ending,byte]) =
    let event := TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state active beginning ending byte
    TlsChatResponseMux.stateBytes Word64.concrete event.state ++ [event.bodyData,event.bodyReset,event.headerData] := by
  have length := mux_bytes_length state shape
  have takeState : (TlsChatResponseMux.stateBytes Word64.concrete state).take 982 =
      TlsChatResponseMux.stateBytes Word64.concrete state := by
    simpa only [length] using (List.take_length (l := TlsChatResponseMux.stateBytes Word64.concrete state))
  simp only [TlsChatResponseMux.runByte,TlsChatResponseMux.stateSize,List.take_append,length,
    Nat.sub_self,List.take_zero,List.append_nil,takeState,read_encoded_mux state shape,
    get_appended]
  rfl

theorem compact_trim_output (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (flags : List (BitVec 8)) :
    compactOutput ByteAuth.concrete (TlsChatResponseMux.stateBytes Word64.concrete (trimMuxState state) ++ flags) =
    compactOutput ByteAuth.concrete (TlsChatResponseMux.stateBytes Word64.concrete state ++ flags) := by
  unfold compactOutput
  apply List.map_congr_left
  intro index member
  have bound : index < 585 := List.mem_range.mp member
  rw [serialized_mux_trim_get state shape flags]
  unfold projectedByte
  rw [(retained_inverse ⟨index,bound⟩).1]

theorem compact_trim_event (event : TlsChatResponseMux.Event (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape event.state) : compactEvent (trimMuxEvent event) = compactEvent event :=
  compact_trim_output event.state shape _

theorem encoded_byte_step (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (shape : MuxCodecShape state) (safe : SafeStack state.parser) (active beginning ending byte : BitVec 8) :
    runByte VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity
      (encodeCompactInput state active beginning ending byte) =
    compactEvent (TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state active beginning ending byte) := by
  unfold runByte
  rw [expand_encoded_input state shape,mux_runByte_encoded capacity _ (mux_trim_codec_shape state shape)]
  change compactEvent (TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
    capacity (trimMuxState state) active beginning ending byte) = _
  rw [←compact_trim_event _ (mux_process_codec_shape capacity _ _ _ _ _ (mux_trim_codec_shape state shape))]
  rw [trim_mux_process capacity state _ _ _ _ safe]
  exact compact_trim_event _ (mux_process_codec_shape capacity state _ _ _ _ shape)

#print axioms mux_runByte_encoded
#print axioms compact_trim_output
#print axioms encoded_byte_step
end ChatResponseReference.ParserCircuitCandidateV1
