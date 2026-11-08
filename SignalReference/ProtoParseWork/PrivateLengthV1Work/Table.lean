import ProtoParseWork.PrivateLengthV1Work.BoundedBytes
import ProtoParseWork.PrivateLengthV1Work.DecoderPadding
namespace PrivateLengthV1.Table
open TlsMpc TlsMpc.Signal

/-- The public-capacity table contains exactly the accepted parser's decoded
rows on the true prefix. Extra capacity rows are empty/rejected rows; they
cannot consume the MAC or capacity padding. -/
theorem table_eq (bytes : List (BitVec 8)) (ending : Nat)
    (inside : ending ≤ bytes.length) (capacity : bytes.length ≤ 512) :
    PrivateProtoParseV1.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 ending) bytes =
    (List.range bytes.length).map
      (ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (bytes.take ending)) := by
  unfold PrivateProtoParseV1.table
  simp only [ProtoParse.table,BoundedBytes.bounded_length]
  apply List.map_congr_left
  intro position _
  rw [BoundedBytes.bounded_eq bytes ending inside capacity]
  exact DecoderPadding.prefix_all _ _ _

#print axioms table_eq
end PrivateLengthV1.Table
