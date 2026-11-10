import ChatResponseReferenceWork.StreamingV1.BodyEvents
import ChatResponseReferenceWork.StreamingV1.VarintSpan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Key/scalar bytes cannot emit body/reset/header events, even on malformed
bytes and already rejected states; no scalar-known or validity assumption. -/
theorem key_scalar_events_zero (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (role : Nat) (bounded : role ≤ 1) (modes : state.modes = lane role) :
    let event := TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte
    event.bodyData = 0 ∧ event.bodyReset = 0 ∧ event.headerData = 0 := by
  have off2 : TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2 = 0 := by
    rw [modes]; have cases : role = 0 ∨ role = 1 := by omega
    rcases cases with h|h <;> subst role <;> rfl
  have off3 : TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 3 = 0 := by
    rw [modes]; have cases : role = 0 ∨ role = 1 := by omega
    rcases cases with h|h <;> subst role <;> rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  refine ⟨?_,?_,?_⟩
  · change ByteAuth.concrete.and _ (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 3) _) = 0
    rw [off3]; simp only [zeroAnd,andZero]
  · change ByteAuth.concrete.and _ (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _) _) = 0
    rw [off2]; simp only [zeroAnd,andZero]
  · change ByteAuth.concrete.and _ (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 3) _) = 0
    rw [off3]; simp only [zeroAnd,andZero]

/-- Actual group field masks suppress every event in any lane or error state. -/
theorem zero_kinds_events_zero (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (kinds : state.kinds = [0,0,0,0]) :
    let event := TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte
    event.bodyData = 0 ∧ event.bodyReset = 0 ∧ event.headerData = 0 := by
  have off1 : TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 1 = 0 := by rw [kinds]; rfl
  have off3 : TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 3 = 0 := by rw [kinds]; rfl
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  refine ⟨?_,?_,?_⟩
  · change ByteAuth.concrete.and _ (ByteAuth.concrete.and _ (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 1)) = 0
    rw [off1]; simp only [andZero]
  · change ByteAuth.concrete.and _ (ByteAuth.concrete.and _ (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 1)) = 0
    rw [off1]; simp only [andZero]
  · change ByteAuth.concrete.and _ (ByteAuth.concrete.and _ (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 3)) = 0
    rw [off3]; simp only [andZero]

theorem continuing_key_scalar_trace_zero (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (role : Nat) (bounded : role ≤ 1) (modes : state.modes = lane role)
    (continues : ∀ byte ∈ bytes, VarintDecode.Spqr.terminates byte = false) :
    bodyTrace state bytes = bytes.map (fun byte => (0,0,0,byte)) ∧ (feed state bytes).modes = lane role := by
  induction bytes generalizing state with
  | nil => exact ⟨rfl,modes⟩
  | cons byte rest ih =>
    have event := key_scalar_events_zero state byte role bounded modes
    have nextModes := core_modes_continue state role (by omega) byte modes (continues byte (by simp))
    have tail := ih _ nextModes (by intro x member; exact continues x (by simp [member]))
    constructor
    · change (_,_,_,byte)::bodyTrace _ rest = (0,0,0,byte)::rest.map _
      rw [event.1,event.2.1,event.2.2,tail.1]
    · exact tail.2

theorem body_trace_append_exact (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (first second : List (BitVec 8)) :
    bodyTrace state (first++second) = bodyTrace state first ++ bodyTrace (feed state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons byte rest ih =>
    simp only [bodyTrace,List.cons_append,feed,List.foldl_cons]
    rw [ih]
    rfl

/-- The consumed span of every successful actual native key/scalar varint has
exactly zero event masks, including its terminating byte. -/
theorem native_key_scalar_trace_zero (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (value : U64) (role : Nat) (bounded : role ≤ 1)
    (modes : state.modes = lane role)
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,after)) :
    ∃ consumed, contents before = consumed++contents after ∧
      bodyTrace state consumed = consumed.map (fun byte => (0,0,0,byte)) := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,native⟩ := native_success_span before after value actual
  obtain ⟨events,nextModes⟩ := continuing_key_scalar_trace_zero state leading role bounded modes continues
  refine ⟨leading++[byte],?_,?_⟩
  · rw [span,suffix,List.append_assoc]; rfl
  · rw [body_trace_append_exact,events,List.map_append]
    have last := key_scalar_events_zero (feed state leading) byte role bounded nextModes
    simp only [bodyTrace,List.map_cons,List.map_nil,List.append_nil,last.1,last.2.1,last.2.2]

#print axioms key_scalar_events_zero
#print axioms zero_kinds_events_zero
#print axioms continuing_key_scalar_trace_zero
#print axioms body_trace_append_exact
#print axioms native_key_scalar_trace_zero
end ChatResponseReference.StreamingUnknownV1
