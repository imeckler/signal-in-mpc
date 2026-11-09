import ChatResponseReferenceWork.StreamingV1.StringUtfState
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- Exact all-input UTF machine relation over an actual bounded string payload.
Malformed bytes and already rejected records retain the same UTF state trace. -/
theorem string_utf_prefix (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count : Nat) (phase : Utf8.Phase)
    (bounded : count < 2^64) (fits : bytes.length ≤ count)
    (modes : state.modes = lane 3) (skip : state.skip = BitVec.ofNat 64 count)
    (kindsShape : state.kinds.length = 4)
    (stringKind : TlsWebSocketUpgrade.either ByteAuth.concrete
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 2)
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 3) = 255)
    (utf : state.utf = Utf8.encode phase) :
    (feed state bytes).utf = Utf8.encode (Utf8.run phase bytes) := by
  induction bytes generalizing state count phase with
  | nil => exact utf
  | cons byte rest ih =>
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    have encodedShape : state.utf.length = 8 := by rw [utf]; cases phase <;> rfl
    have first : next.utf = Utf8.encode (Utf8.next phase byte) := by
      rw [string_utf_step state byte modes stringKind encodedShape,utf,Utf8.step_encoding]
    cases rest with
    | nil => exact first
    | cons following tail =>
      have remains : 1 < count := by simp only [List.length_cons] at fits; omega
      have inside := opaque_prefix_inside state [byte] count bounded (by simp only [List.length_cons,List.length_nil]; omega) modes skip
      have nextKinds : next.kinds = state.kinds := opaque_kinds_step state byte modes kindsShape
      have nextKind : TlsWebSocketUpgrade.either ByteAuth.concrete
          (TlsWebSocketUpgrade.get ByteAuth.concrete next.kinds 2)
          (TlsWebSocketUpgrade.get ByteAuth.concrete next.kinds 3) = 255 := by rw [nextKinds]; exact stringKind
      exact ih next (count-1) (Utf8.next phase byte) (by omega)
        (by simp only [List.length_cons] at fits ⊢; omega) inside.1 inside.2
        (nextKinds ▸ kindsShape) nextKind first

/-- Final UTF completion agrees with the executable grammar for every payload,
including truncated/malformed UTF8. This is not a std raw-pointer body theorem. -/
theorem string_utf_complete (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count : Nat)
    (bounded : count < 2^64) (fits : bytes.length ≤ count)
    (modes : state.modes = lane 3) (skip : state.skip = BitVec.ofNat 64 count)
    (kindsShape : state.kinds.length = 4)
    (stringKind : TlsWebSocketUpgrade.either ByteAuth.concrete
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 2)
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 3) = 255)
    (utf : state.utf = Utf8.encode .ready) :
    TlsWebSocketUpgrade.get ByteAuth.concrete (feed state bytes).utf 0 =
      if Utf8.accepts bytes then 255 else 0 := by
  rw [string_utf_prefix state bytes count .ready bounded fits modes skip kindsShape stringKind utf,Utf8.encoding_complete]
  simp only [Utf8.accepts,decide_eq_true_eq]

#print axioms string_utf_prefix
#print axioms string_utf_complete
end ChatResponseReference.StreamingV1
