import ChatResponseReferenceWork.StreamingV1.MessagePayloadValidity
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- All-outcome validity equality for the actual Core message-String payload,
under exact post-header state/counters and executable UTF8 specification. -/
theorem message_payload_agreement (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (budget remaining : Nat)
    (budgetBound : budget ≤ 4096) (remainingBound : remaining ≤ 4096)
    (budgetEnough : bytes.length ≤ budget) (childEnough : bytes.length ≤ remaining)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,0,255,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (inner : state.inner = 255) (depth : state.depth = 0)
    (skip : state.skip = BitVec.ofNat 64 bytes.length)
    (budgetCounter : state.budget = BitVec.ofNat 64 budget) (childCounter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (utf : state.utf = Utf8.encode .ready) :
    (feed state bytes).valid = if Utf8.accepts bytes then 255 else 0 := by
  by_cases accepted : Utf8.accepts bytes = true
  · rw [accepted]
    have grammar : Utf8.run .ready bytes = .ready := of_decide_eq_true accepted
    exact message_payload_valid state bytes bytes.length budget remaining .ready budgetBound remainingBound budgetEnough rfl childEnough
      modes kinds valid seen finished inner depth skip budgetCounter childCounter utf grammar
  · have bad : Utf8.accepts bytes = false := Bool.eq_false_iff.mpr accepted
    rw [bad]
    have nonempty : bytes ≠ [] := by intro empty; rw [empty] at bad; cases bad
    exact string_payload_utf_reject state bytes nonempty (by omega) modes skip (by rw [kinds]; rfl)
      (by rw [kinds]; rfl) utf bad

#print axioms message_payload_agreement
end ChatResponseReference.StreamingV1
