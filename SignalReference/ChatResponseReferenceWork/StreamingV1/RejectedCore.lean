import ChatResponseReferenceWork.StreamingV1.RejectedReader
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem core_tenth_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (role : Nat) (roleBound : role < 3)
    (modes : state.modes = lane role) (positions : state.positions = oneHot 9)
    (invalid : 2 ≤ byte.toNat) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
  have active : TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3) = 255 := by
    rw [modes]; exact lane_active role roleBound
  have overflow := final_overflow_exact byte
  rw [if_neg (by omega : ¬byte.toNat < 2)] at overflow
  change ByteAuth.concrete.and state.valid
    (ByteAuth.concrete.and state.seen (ByteAuth.concrete.and (ByteAuth.concrete.not state.finished)
      (ByteAuth.concrete.and (ByteAuth.concrete.not (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.budget 0))
        (ByteAuth.concrete.and
          (ByteAuth.concrete.not (ByteAuth.concrete.and
            (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3))
            (TlsWebSocketUpgrade.either ByteAuth.concrete
              (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.positions 9)
                (ByteAuth.concrete.not (TlsWebSocketUpgrade.eq ByteAuth.concrete
                  (ByteAuth.concrete.and byte (ByteAuth.concrete.const 254)) 0)))
              (ByteAuth.concrete.not (TlsWebSocketUpgrade.any ByteAuth.concrete state.positions))))) _)))) = 0
  rw [active,positions,overflow]
  have hot : TlsWebSocketUpgrade.get ByteAuth.concrete (oneHot 9) 9 = 255 := rfl
  have andHot : ByteAuth.concrete.and 255 255 = 255 := rfl
  have eitherHot (x : BitVec 8) : TlsWebSocketUpgrade.either ByteAuth.concrete 255 x = 255 := by
    change ~~~((~~~(255 : BitVec 8)) &&& (~~~x)) = 255
    simp
  have notHot : ByteAuth.concrete.not 255 = 0 := rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := by
    change (0 : BitVec 8) &&& x = 0
    exact BitVec.zero_and
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := by
    change x &&& (0 : BitVec 8) = 0
    exact BitVec.and_zero
  rw [hot,andHot,eitherHot,andHot,notHot,zeroAnd,andZero,andZero,andZero,andZero]

/-- The same ninth-prefix invariant that proves accepted values also establishes
Core rejection of every invalid tenth byte, whether terminal or continuing. -/
theorem core_prefix_tenth_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading : List (BitVec 8)) (byte : BitVec 8) (role : Nat) (roleBound : role < 3)
    (length : leading.length = 9) (modes : state.modes = lane role)
    (positions : state.positions = oneHot 0)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false)
    (invalid : 2 ≤ byte.toNat) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (feed state leading) byte).state.valid = 0 := by
  have invariant := core_prefix_invariant state leading role 0 roleBound (by omega) modes positions continues
  apply core_tenth_reject _ byte role roleBound invariant.1
  · simpa only [Nat.zero_add,length] using invariant.2.1
  · exact invalid

open Aeneas Aeneas.Std
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
/-- Exact actual rejection/suffix for the same invalid tenth byte. -/
theorem rejected_tenth_native (before : Slice U8) (leading tail : List (BitVec 8)) (byte : BitVec 8)
    (span : contents before = leading ++ byte::tail) (length : leading.length = 9)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false)
    (invalid : 2 ≤ byte.toNat) :
    ∃ error after,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after) ∧
      error = invalidError ∧
      after = if FastGuard before then before else drop before (min 10 before.length) := by
  apply native_prefix_rejection
  rw [span]
  exact rejected_tenth_row leading tail byte length continues invalid

#print axioms core_tenth_reject
#print axioms core_prefix_tenth_reject
#print axioms rejected_tenth_native
end ChatResponseReference.StreamingV1
