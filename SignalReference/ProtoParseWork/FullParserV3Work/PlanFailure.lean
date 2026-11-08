import ProtoParseWork.FullParserV3Work.SuccessScan
open TlsMpc TlsMpc.Signal
namespace FullParserV3
set_option maxHeartbeats 2000000

theorem plan_varint_key_failure (capacity position : Nat) (lastClear : BitVec 8)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : key.ok = 0) :
    let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload state
    p.ok = 0 ∧ p.tag = 0 ∧
    p.stop = Word64.concrete.select (if capacity > position+10 then 255 else lastClear)
      (BitVec.ofNat 64 position) (BitVec.ofNat 64 (position + min 10 (capacity-position))) := by
  have hp : (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
    simp only [ProtoParse.plan,hk]
    exact BitVec.zero_and
  dsimp only [ProtoParse.planWithCursor]
  rw [hk,hp]
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [hz,Word64.select_reject]
  exact ⟨True.intro,rfl,rfl⟩

#print axioms plan_varint_key_failure
end FullParserV3
