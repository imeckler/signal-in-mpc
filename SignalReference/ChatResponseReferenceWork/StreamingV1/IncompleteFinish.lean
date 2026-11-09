import ChatResponseReferenceWork.StreamingV1.VarintPrefix
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
set_option maxHeartbeats 1000000

/-- EOF in any scalar or length lane is rejected regardless of field values. -/
theorem finish_nonkey (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (mode : TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0 = 0) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete state).valid = 0 := by
  simp only [TlsChatResponse.finish,mode]
  change state.valid &&& (state.seen &&& ((~~~state.finished) &&& (0 &&& _))) = 0
  simp

/-- EOF between bytes of a key cannot be confused with a clean field boundary. -/
theorem finish_partial_position (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (position : TlsWebSocketUpgrade.get ByteAuth.concrete state.positions 0 = 0) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete state).valid = 0 := by
  simp only [TlsChatResponse.finish,position]
  change state.valid &&& (state.seen &&& ((~~~state.finished) &&& (_ &&& (0 &&& _)))) = 0
  simp

theorem prefix_eof_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading : List (BitVec 8)) (role : Nat) (roleBound : role < 3)
    (bound : leading.length ≤ 9) (modes : state.modes = lane role)
    (positions : state.positions = oneHot 0)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false)
    (incomplete : role ≠ 0 ∨ 0 < leading.length) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state leading)).valid = 0 := by
  have invariant := core_prefix_invariant state leading role 0 roleBound (by omega) modes positions continues
  rcases incomplete with nonkey | nonempty
  · apply finish_nonkey
    rw [invariant.1]
    have cases : role = 1 ∨ role = 2 := by omega
    rcases cases with h|h <;> subst role <;> rfl
  · apply finish_partial_position
    rw [invariant.2.1]
    simp only [Nat.zero_add]
    have cases : leading.length = 1 ∨ leading.length = 2 ∨ leading.length = 3 ∨ leading.length = 4 ∨
      leading.length = 5 ∨ leading.length = 6 ∨ leading.length = 7 ∨ leading.length = 8 ∨ leading.length = 9 := by omega
    rcases cases with h|h|h|h|h|h|h|h|h <;> rw [h] <;> rfl
#print axioms finish_nonkey
#print axioms finish_partial_position
#print axioms prefix_eof_reject
end ChatResponseReference.StreamingV1
