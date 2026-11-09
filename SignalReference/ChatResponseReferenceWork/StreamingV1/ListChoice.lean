import ChatResponseReferenceWork.StreamingV1.KeyTransition
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

theorem choose_accept_exact (yes no : List (BitVec 8)) (length : yes.length = no.length) :
    TlsWebSocketUpgrade.choose ByteAuth.concrete 255 yes no = yes := by
  induction yes generalizing no with
  | nil => cases no <;> simp_all [TlsWebSocketUpgrade.choose]
  | cons y ys ih =>
    cases no with
    | nil => simp at length
    | cons n ns =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at length
      simp only [TlsWebSocketUpgrade.choose,List.zipWith_cons_cons,TlsInner.select_accept]
      exact congrArg (List.cons y) (ih ns length)

theorem choose_reject_exact (yes no : List (BitVec 8)) (length : yes.length = no.length) :
    TlsWebSocketUpgrade.choose ByteAuth.concrete 0 yes no = no := by
  induction yes generalizing no with
  | nil => cases no <;> simp_all [TlsWebSocketUpgrade.choose]
  | cons y ys ih =>
    cases no with
    | nil => simp at length
    | cons n ns =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at length
      simp only [TlsWebSocketUpgrade.choose,List.zipWith_cons_cons,TlsInner.select_reject]
      exact congrArg (List.cons n) (ih ns length)

theorem terminal_position_reset (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (role group : Nat) (roleBound : role < 3)
    (modes : state.modes = lane role) (positions : state.positions = oneHot group)
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.positions = oneHot 0 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by
    rw [terminal_exact byte,terminal]; rfl
  have active : TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3) = 255 := by
    rw [modes]; exact lane_active role roleBound
  change TlsWebSocketUpgrade.choose ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3))
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
    (TlsWebSocketUpgrade.initial ByteAuth.concrete 9)
    (TlsWebSocketUpgrade.choose ByteAuth.concrete
      (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3))
      (0::state.positions.take 9) state.positions) = oneHot 0
  rw [ended,active]
  change TlsWebSocketUpgrade.choose ByteAuth.concrete 255 (oneHot 0)
    (TlsWebSocketUpgrade.choose ByteAuth.concrete 255 (0::state.positions.take 9) state.positions) = oneHot 0
  apply choose_accept_exact
  simp only [TlsWebSocketUpgrade.choose,List.length_zipWith,List.length_cons,List.length_take,positions]
  simp [oneHot]

#print axioms choose_accept_exact
#print axioms choose_reject_exact
#print axioms terminal_position_reset
end ChatResponseReference.StreamingV1
