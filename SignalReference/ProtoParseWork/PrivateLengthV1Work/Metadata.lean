import ProtoParseWork.PrivateLengthV1Work.Framing
namespace PrivateLengthV1.Metadata
open TlsMpc TlsMpc.Signal

theorem field_pad (state : ProtoParse.State (BitVec 8) (BitVec 64)) (count index : Nat) :
    ProtoParse.getField Word64.concrete ByteAuth.concrete (Stack.pad state count) index =
      ProtoParse.getField Word64.concrete ByteAuth.concrete state index := rfl

theorem complete_pad (ending count : Nat) (state : ProtoParse.State (BitVec 8) (BitVec 64)) :
    PrivateProtoParseV1.completeMask Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending) (Stack.pad state count) =
      ProtoParse.completeMask Word64.concrete ByteAuth.concrete ending state := rfl

theorem ratchet_take (wire : List (BitVec 8)) (length count : Nat)
    (within : length ≤ wire.length) (capacity : wire.length ≤ 512)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) :
    PrivateProtoParseV1.ratchetRead Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 (length-9))
      (ProtoParse.body wire) (Stack.pad state count) =
      ProtoParse.ratchetRead Word64.concrete ByteAuth.concrete (ProtoParse.body (wire.take length)) state := by
  rw [Framing.body_take wire length within]
  simp only [PrivateProtoParseV1.ratchetRead,field_pad,ProtoParse.ratchetRead]
  apply Read.read_take
  · rw [Framing.body_length]; omega
  · rw [Framing.body_length]; omega
  · decide

/-- Even unmasked metadata reads match the actual prefix for every parser
state, not only accepted ones. The stack extension is unobservable here. -/
theorem metadata_take (wire : List (BitVec 8)) (length count : Nat)
    (within : length ≤ wire.length) (capacity : wire.length ≤ 512)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) :
    PrivateProtoParseV1.metadata Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 (length-9))
      wire (Stack.pad state count) =
      ProtoParse.metadata Word64.concrete ByteAuth.concrete (wire.take length) state := by
  unfold PrivateProtoParseV1.metadata ProtoParse.metadata
  rw [ratchet_take wire length count within capacity state]
  simp only [field_pad]

#print axioms ratchet_take
#print axioms metadata_take
end PrivateLengthV1.Metadata
