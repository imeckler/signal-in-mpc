import ChatResponseReferenceWork.StreamingUnknownV1.LengthTransition
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
private theorem and_zero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
private theorem and_hot (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
private theorem either_zero (x : BitVec 8) : TlsWebSocketUpgrade.either ByteAuth.concrete x 0 = x := by
  unfold TlsWebSocketUpgrade.either
  have notZero : ByteAuth.concrete.not 0 = 255 := rfl
  have rightHot (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
  rw [notZero,rightHot]
  exact BitVec.not_not
private theorem either_hot (x : BitVec 8) : TlsWebSocketUpgrade.either ByteAuth.concrete x 255 = 255 := by
  unfold TlsWebSocketUpgrade.either
  have notHot : ByteAuth.concrete.not 255 = 0 := rfl
  rw [notHot,and_zero]
  rfl

theorem unknown_length_response_data (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 2) (kinds : state.kinds = [0,0,0,0])
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    responseData (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state =
      responseData state := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  simp only [responseData,TlsChatResponse.step]
  rw [modes,kinds,ended]
  have p0 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 2) 0 = 0 := rfl
  have p1 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 2) 1 = 0 := rfl
  have p2 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 2) 2 = 255 := rfl
  have k1 : TlsWebSocketUpgrade.get ByteAuth.concrete [0,0,0,0] 1 = 0 := rfl
  have k2 : TlsWebSocketUpgrade.get ByteAuth.concrete [0,0,0,0] 2 = 0 := rfl
  simp only [p0,p1,p2,k1,k2,zero_and,and_hot,and_zero,Word64.select_reject,either_zero]

/-- Consuming the actual native length header never changes known response
fields for an unknown tag; this remains true independently of validity/fit. -/
theorem native_unknown_length_header_data (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0)
    (kinds : state.kinds = [0,0,0,0])
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ header,
      contents before = header ++ contents after ∧
      responseData (feed state header) = responseData state := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native actual
  have invariant := core_prefix_invariant state leading 2 0 (by decide) (by omega) modes positions continues
  have currentKinds : (feed state leading).kinds = [0,0,0,0] :=
    (prefix_kinds state leading continues (by rw [kinds]; rfl)).trans kinds
  let header := leading ++ [byte]
  refine ⟨header,?_,?_⟩
  · calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = header ++ contents after := by simp only [header,List.append_assoc,List.singleton_append]
  · have data := (unknown_length_response_data (feed state leading) byte invariant.1 currentKinds terminal).trans (nonterminal_prefix_data state leading continues)
    simpa only [header,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using data

#print axioms native_unknown_length_header_data
#print axioms unknown_length_response_data
end ChatResponseReference.StreamingUnknownV1
