import TlsMpc.Signal.PrivateProtoParseV1
namespace PrivateLengthV1.Plan
open TlsMpc TlsMpc.Signal

theorem plan_const (o : Word64.Ops B W) (a : ByteAuth.Ops B) (ending : Nat)
    (key payload : ProtoParse.Decoded B W) (state : ProtoParse.State B W) :
    PrivateProtoParseV1.plan o a (o.const ending) key payload state =
      ProtoParse.plan o a ending key payload state := rfl

theorem nat_ule (x y : Nat) (hx : x < 2^64) (hy : y < 2^64) :
    Word64.concrete.ule (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) =
      if x ≤ y then 255 else 0 := by
  simp [Word64.ule_value,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy]

/-- Failure-cursor guards use the secret actual end, including the native
contiguous fast-path boundary. There is no success-only restriction. -/
theorem cursor_const (ending position : Nat) (bound : ending ≤ 512) (inside : position < ending)
    (lastClear : BitVec 8) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) :
    PrivateProtoParseV1.planWithCursor Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 ending) position lastClear key payload state =
    ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete ending position lastClear key payload state := by
  have hn : ending < 2^64 := by omega
  have hp10 : position+10 < 2^64 := by omega
  have hp11 : position+11 < 2^64 := by omega
  have keyFast : Word64.bor ByteAuth.concrete
      (Word64.concrete.ule (BitVec.ofNat 64 (position+11)) (BitVec.ofNat 64 ending)) lastClear =
      if ending > position+10 then 255 else lastClear := by
    rw [nat_ule _ _ hp11 hn]
    split <;> rename_i comparison
    · have guard : ending > position+10 := by omega
      simp [guard,Word64.bor,ByteAuth.concrete,BitVec.xor_assoc]
    · have guard : ¬ending > position+10 := by omega
      simp [guard,Word64.bor,ByteAuth.concrete]
  have keyStop : Word64.concrete.select
      (Word64.concrete.ule (BitVec.ofNat 64 (position+10)) (BitVec.ofNat 64 ending))
      (BitVec.ofNat 64 (position+10)) (BitVec.ofNat 64 ending) =
      BitVec.ofNat 64 (position + min 10 (ending-position)) := by
    rw [nat_ule _ _ hp10 hn]
    split <;> rename_i comparison
    · rw [Word64.select_accept]
      congr 1; omega
    · rw [Word64.select_reject]
      congr 1; omega
  have hp : PrivateProtoParseV1.plan Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 ending) key payload state =
      ProtoParse.plan Word64.concrete ByteAuth.concrete ending key payload state :=
    plan_const _ _ _ _ _ _
  unfold PrivateProtoParseV1.planWithCursor ProtoParse.planWithCursor
  rw [hp]
  dsimp only
  change Word64.bor ByteAuth.concrete
      (Word64.concrete.ule (Word64.concrete.const (position+11)) (BitVec.ofNat 64 ending)) lastClear = _ at keyFast
  change Word64.concrete.select
      (Word64.concrete.ule (Word64.concrete.const (position+10)) (BitVec.ofNat 64 ending))
      (Word64.concrete.const (position+10)) (BitVec.ofNat 64 ending) = _ at keyStop
  rw [keyFast,keyStop]
  rfl


#print axioms plan_const
#print axioms cursor_const
end PrivateLengthV1.Plan
