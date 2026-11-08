import ProtoParseWork.FullParserV3Work.PayloadPlan
import ProtoParseWork.FullParserV3Work.UnknownShadow
open TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

def attemptsPayloadMask (key : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) : BitVec 8 :=
  ByteAuth.concrete.and (keyFields Word64.concrete ByteAuth.concrete key).ok
    (ByteAuth.concrete.and (validKnownMask key state) (ByteAuth.concrete.and
      (Word64.concrete.ule state.depth 99)
      (Word64.bor ByteAuth.concrete (Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 0)
        (Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 2))))

theorem nonpayload_mask (key : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (h : validKnownMask key state = 0 ∨ 99 < state.depth.toNat ∨ (key.value &&& 7 ≠ 0 ∧ key.value &&& 7 ≠ 2)) :
    attemptsPayloadMask key state = 0 := by
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hz' (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  rcases h with hk | hd | ⟨h0,h2⟩
  · simp only [attemptsPayloadMask,hk,hz,hz']
  · have hb : Word64.concrete.ule state.depth 99 = 0 := by
      rw [Word64.ule_value]; exact if_neg (by change ¬state.depth.toNat ≤ 99; omega)
    simp only [attemptsPayloadMask,hb,hz,hz']
  · have h0' : Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 0 = 0 := by rw [word_eq_value]; exact if_neg h0
    have h2' : Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 2 = 0 := by rw [word_eq_value]; exact if_neg h2
    simp only [attemptsPayloadMask,h0',h2',Word64.bor,hz,hz',show ByteAuth.concrete.xor 0 0 = 0 from rfl]

theorem plan_wrong_wire (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : validKnownMask key state = 0) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  change ByteAuth.concrete.and key.ok (ByteAuth.concrete.and
    (Word64.concrete.ule key.value (Word64.concrete.const 4294967295)) (ByteAuth.concrete.and
      (ByteAuth.concrete.not (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 0))
      (ByteAuth.concrete.and (validKnownMask key state) _))) = 0
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hz' (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [hk,hz,hz']

/-- Wrong wire, recursion limit, fixed-width underflow and bad EndGroup all
reject before attempting any payload decoder. Their exact v2 cursor is the
successful key's end, rather than a speculative payload-table position. -/
theorem nonpayload_failure_stop (capacity position : Nat) (lastClear : BitVec 8)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : key.ok = 255)
    (hp : (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0)
    (ha : attemptsPayloadMask key state = 0) :
    (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload state).stop = key.stop := by
  change Word64.concrete.select (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok _
    (Word64.concrete.select (attemptsPayloadMask key state) _ (Word64.concrete.select key.ok key.stop _)) = key.stop
  rw [hp,ha,Word64.select_reject,hk,Word64.select_accept]
  exact Word64.select_reject _ _

#print axioms nonpayload_mask
#print axioms plan_wrong_wire
#print axioms nonpayload_failure_stop
end FullParserV3
