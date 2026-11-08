import ProtoParseWork.FullParserV3Work.FrozenRejection
open TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

theorem payload_attempt_mask (key : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hk : (keyFields Word64.concrete ByteAuth.concrete key).ok = 255)
    (hv : validKnownMask key state = 255) (hd : state.depth.toNat ≤ 99)
    (hkind : key.value &&& 7 = 0 ∨ key.value &&& 7 = 2) : attemptsPayloadMask key state = 255 := by
  have hb : Word64.concrete.ule state.depth 99 = 255 := by rw [Word64.ule_value]; exact if_pos hd
  unfold attemptsPayloadMask
  rw [hk,hv,hb]
  rcases hkind with h | h
  all_goals simp only [h]
  all_goals decide

theorem payload_decoded_failure_stop (capacity position : Nat) (lastClear : BitVec 8)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hp : (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0)
    (ha : attemptsPayloadMask key state = 255) (hd : payload.ok = 255) :
    (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload state).stop = payload.stop := by
  change Word64.concrete.select (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok _
    (Word64.concrete.select (attemptsPayloadMask key state) (Word64.concrete.select payload.ok payload.stop _) _) = payload.stop
  simp only [hp,ha,hd,Word64.select_reject,Word64.select_accept]

theorem plan_length_invalid (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hkind : key.value &&& 7 = 2)
    (hu : Word64.concrete.ule payload.value (Word64.concrete.sub (Word64.concrete.const capacity) payload.stop) = 0) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hz' (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [ProtoParse.plan,show Word64.concrete.band key.value (Word64.concrete.const 7) = key.value &&& 7 from rfl,hkind,
    show Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const 0) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const 1) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const 2) = 255 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const 3) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const 4) = 0 from by decide,
    show Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const 5) = 0 from by decide,hu,hz,hz',Word64.bor,show ByteAuth.concrete.xor 0 0 = 0 from rfl]

#print axioms payload_attempt_mask
#print axioms payload_decoded_failure_stop
#print axioms plan_length_invalid
end FullParserV3
