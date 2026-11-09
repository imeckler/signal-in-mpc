import ChatResponseReferenceWork.StreamingUnknownV1.FixedResume
import ChatResponseReferenceWork.StreamingV1.BodyEvents
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Unknown opaque bytes emit no body/reset/header events, including rejected
records and arbitrary byte values; no validity/success premise is needed. -/
theorem unknown_opaque_events (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,0,0,0]) :
    let event := TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte
    event.bodyData = 0 ∧ event.bodyReset = 0 ∧ event.headerData = 0 := by
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  refine ⟨?_,opaque_reset_zero state byte modes,?_⟩
  · change ByteAuth.concrete.and _ (ByteAuth.concrete.and _ (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 1)) = 0
    rw [kinds]
    have off : TlsWebSocketUpgrade.get ByteAuth.concrete [0,0,0,0] 1 = 0 := rfl
    rw [off]
    simp only [andZero]
  · change ByteAuth.concrete.and _ (ByteAuth.concrete.and _ (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 3)) = 0
    rw [kinds]
    have off : TlsWebSocketUpgrade.get ByteAuth.concrete [0,0,0,0] 3 = 0 := rfl
    rw [off]
    simp only [andZero]

theorem unknown_opaque_trace_exact (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count : Nat) (bounded : count < 2^64) (fits : bytes.length ≤ count)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,0,0,0]) (skip : state.skip = BitVec.ofNat 64 count) :
    bodyTrace state bytes = bytes.map (fun byte => (0,0,0,byte)) := by
  induction bytes generalizing state count with
  | nil => rfl
  | cons byte rest ih =>
    let event := TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte
    have events := unknown_opaque_events state byte modes kinds
    change (event.bodyData,event.bodyReset,event.headerData,byte)::bodyTrace event.state rest =
      (0,0,0,byte)::rest.map (fun value => (0,0,0,value))
    rw [events.1,events.2.1,events.2.2]
    congr 1
    cases rest with
    | nil => rfl
    | cons following tail =>
      have first := opaque_prefix_inside state [byte] count bounded
        (by simp only [List.length_cons,List.length_nil] at fits ⊢; omega) modes skip
      have nextKinds : event.state.kinds = [0,0,0,0] :=
        (opaque_kinds_step state byte modes (by rw [kinds]; rfl)).trans kinds
      exact ih event.state (count-1) (by omega)
        (by simp only [List.length_cons] at fits ⊢; omega) first.1 nextKinds first.2

#print axioms unknown_opaque_events
#print axioms unknown_opaque_trace_exact
end ChatResponseReference.StreamingUnknownV1
