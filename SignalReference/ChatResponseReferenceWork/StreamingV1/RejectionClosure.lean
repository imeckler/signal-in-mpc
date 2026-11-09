import ChatResponseReferenceWork.StreamingV1.RejectedCore
import ChatResponseReferenceWork.StreamingV1.IncompleteFinish
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

theorem step_invalid_sticky (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (invalid : state.valid = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
  change ByteAuth.concrete.and state.valid _ = 0
  rw [invalid]
  exact BitVec.zero_and

theorem feed_invalid_sticky (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (invalid : state.valid = 0) :
    (feed state bytes).valid = 0 := by
  induction bytes generalizing state with
  | nil => exact invalid
  | cons byte rest ih =>
    exact ih _ (step_invalid_sticky state byte invalid)

theorem finish_invalid_sticky (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (invalid : state.valid = 0) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete state).valid = 0 := by
  change ByteAuth.concrete.and state.valid _ = 0
  rw [invalid]
  exact BitVec.zero_and

/-- Arbitrary remaining bytes cannot turn a malformed tenth byte into an
accepted message, even when they contain a later valid-looking envelope. -/
theorem bad_tenth_suffix_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading tail : List (BitVec 8)) (byte : BitVec 8) (role : Nat) (roleBound : role < 3)
    (length : leading.length = 9) (modes : state.modes = lane role)
    (positions : state.positions = oneHot 0)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false)
    (invalid : 2 ≤ byte.toNat) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete
      (feed state (leading ++ byte::tail))).valid = 0 := by
  apply finish_invalid_sticky
  simp only [feed,List.foldl_append,List.foldl_cons]
  change (feed ((TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state) tail).valid = 0
  exact feed_invalid_sticky _ tail
    (core_prefix_tenth_reject state leading byte role roleBound length modes positions continues invalid)

#print axioms step_invalid_sticky
#print axioms feed_invalid_sticky
#print axioms finish_invalid_sticky
#print axioms bad_tenth_suffix_reject
end ChatResponseReference.StreamingV1
