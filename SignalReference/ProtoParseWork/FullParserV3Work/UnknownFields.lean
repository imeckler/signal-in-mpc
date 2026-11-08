import ProtoParseWork.FullParserV3Work.FieldProjection
open TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstTopField
open ParserErrorStateV2
set_option maxHeartbeats 1000000

private theorem unknown_not_slot (tag : BitVec 64) (i : Nat) (hi : i < 6) (ht : 6 < tag.toNat) :
    tag ≠ BitVec.ofNat 64 (i+1) := by
  intro he
  have hn := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i+1 < 2^64)] at hn
  omega

theorem initialize_unknown (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (tag : BitVec 64) (hl : fields.length ≤ 6) (ht : 6 < tag.toNat) :
    ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 tag fields = fields := by
  apply List.ext_getElem
  · exact initialize_length _ _ _
  · intro i h1 h2
    rw [initialize_get_general fields tag i h2,if_neg (unknown_not_slot tag i (by omega) ht)]

theorem write_unknown (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (tag : BitVec 64) (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (hl : fields.length ≤ 6) (ht : 6 < tag.toNat) :
    ProtoParse.writeFields Word64.concrete ByteAuth.concrete 255 tag payload fields = fields := by
  apply List.ext_getElem
  · exact write_fields_length _ _ _ _
  · intro i h1 h2
    rw [write_fields_get tag payload fields i h2,if_neg (unknown_not_slot tag i (by omega) ht)]

#print axioms initialize_unknown
#print axioms write_unknown
end FullParserV3
