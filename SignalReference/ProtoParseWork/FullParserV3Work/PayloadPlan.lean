import ProtoParseWork.FullParserV3Work.PayloadGuard
import ProtoParseWork.FullParserV3Work.KeyValidationPlan
open TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

def validKnownMask (key : ProtoParse.Decoded (BitVec 8) (BitVec 64)) (state : ProtoParse.State (BitVec 8) (BitVec 64)) : BitVec 8 :=
  Word64.bor ByteAuth.concrete (ByteAuth.concrete.not (ByteAuth.concrete.and
    (Word64.eq Word64.concrete ByteAuth.concrete state.depth 0) (Word64.concrete.ule (key.value >>> 3) 6)))
    (Unpad.chooseByte ByteAuth.concrete
      (Word64.bor ByteAuth.concrete (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 2)
        (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 3))
      (Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 0)
      (Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 2))

private theorem bor_accept_left (x : BitVec 8) : Word64.bor ByteAuth.concrete 255 x = 255 := by
  change ((255 : BitVec 8) ^^^ x) ^^^ ((255 : BitVec 8) &&& x) = 255
  simp only [show (255 : BitVec 8) = BitVec.allOnes 8 from rfl,BitVec.allOnes_and,
    BitVec.xor_assoc,BitVec.xor_self,BitVec.xor_zero]

theorem valid_known_skip (key : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hs : state.depth ≠ 0 ∨ 6 < (key.value >>> 3).toNat) : validKnownMask key state = 255 := by
  have hk : ByteAuth.concrete.and (Word64.eq Word64.concrete ByteAuth.concrete state.depth 0)
      (Word64.concrete.ule (key.value >>> 3) 6) = 0 := by
    rcases hs with hd | ht
    · rw [word_eq_value,if_neg hd]
      exact BitVec.zero_and
    · rw [Word64.ule_value,if_neg (by change ¬(key.value >>> 3).toNat ≤ 6; omega)]
      exact BitVec.and_zero
  unfold validKnownMask
  rw [hk]
  exact bor_accept_left _

theorem valid_known_scalar (key : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hd : state.depth = 0)
    (ht : key.value >>> 3 = 2 ∨ key.value >>> 3 = 3) (hk : key.value &&& 7 = 0) : validKnownMask key state = 255 := by
  unfold validKnownMask
  rcases ht with ht | ht
  all_goals simp only [hd,ht,hk]
  all_goals decide

theorem valid_known_bytes (key : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hd : state.depth = 0)
    (ht : key.value >>> 3 = 1 ∨ key.value >>> 3 = 4 ∨ key.value >>> 3 = 5 ∨ key.value >>> 3 = 6)
    (hk : key.value &&& 7 = 2) : validKnownMask key state = 255 := by
  unfold validKnownMask
  rcases ht with ht | ht | ht | ht
  all_goals simp only [hd,ht,hk]
  all_goals decide

/-- Exact v2 error-time transition to the payload decoder's failure cursor. The
caller derives valid-key/known-wire decisions and failed basic mask from the
actual decoded header and the separately proved branch reference. -/
theorem payload_varint_failure_stop (capacity position : Nat) (lastClear : BitVec 8)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : (keyFields Word64.concrete ByteAuth.concrete key).ok = 255)
    (hknown : validKnownMask key state = 255) (hdepth : state.depth.toNat ≤ 99)
    (hkind : key.value &&& 7 = 0 ∨ key.value &&& 7 = 2) (hpayload : payload.ok = 0)
    (hbad : (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0) :
    (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload state).stop =
      Word64.concrete.select (Word64.bor ByteAuth.concrete
        (Word64.concrete.ule (key.stop + Word64.concrete.const 11) (Word64.concrete.const capacity)) lastClear) key.stop
        (Word64.concrete.select (Word64.concrete.ule (key.stop + Word64.concrete.const 10) (Word64.concrete.const capacity))
          (key.stop + Word64.concrete.const 10) (Word64.concrete.const capacity)) := by
  have hkey' : ByteAuth.concrete.and key.ok
      (ByteAuth.concrete.and (Word64.concrete.ule key.value (Word64.concrete.const 4294967295))
        (ByteAuth.concrete.and (ByteAuth.concrete.not (Word64.eq Word64.concrete ByteAuth.concrete
          (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).tag (Word64.concrete.const 0)))
          (Word64.concrete.ule (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).kind (Word64.concrete.const 5)))) = 255 := hkey
  have hknown' : Word64.bor ByteAuth.concrete (ByteAuth.concrete.not
      (ByteAuth.concrete.and (Word64.eq Word64.concrete ByteAuth.concrete state.depth (Word64.concrete.const 0))
        (Word64.concrete.ule (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).tag (Word64.concrete.const 6))))
      (Unpad.chooseByte ByteAuth.concrete (Word64.bor ByteAuth.concrete
        (Word64.eq Word64.concrete ByteAuth.concrete (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).tag (Word64.concrete.const 2))
        (Word64.eq Word64.concrete ByteAuth.concrete (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).tag (Word64.concrete.const 3)))
        (Word64.eq Word64.concrete ByteAuth.concrete (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).kind (Word64.concrete.const 0))
        (Word64.eq Word64.concrete ByteAuth.concrete (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).kind (Word64.concrete.const 2))) = 255 := hknown
  have hbelow : Word64.concrete.ule state.depth (Word64.concrete.const 99) = 255 := by
    rw [Word64.ule_value]; exact if_pos hdepth
  have hw : Word64.bor ByteAuth.concrete
      (Word64.eq Word64.concrete ByteAuth.concrete (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).kind (Word64.concrete.const 0))
      (Word64.eq Word64.concrete ByteAuth.concrete (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).kind (Word64.concrete.const 2)) = 255 := by
    change Word64.bor ByteAuth.concrete (Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 0)
      (Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 2) = 255
    rcases hkind with hk | hk
    all_goals simp only [hk]
    all_goals decide
  dsimp only [ProtoParse.planWithCursor]
  simp only [hbad,hkey',hknown',hbelow,hw,hpayload,Word64.select_reject]
  exact Word64.select_accept _ _

#print axioms valid_known_skip
#print axioms valid_known_scalar
#print axioms valid_known_bytes
#print axioms payload_varint_failure_stop
end FullParserV3
