import ProtoParseWork.FullParserV3Work.ActualSkipScan
import ProtoParseWork.FullParserV3Work.KnownTotality
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 2000000

/-- Common strict-prefix observations determine the actual decoder's complete
successful return and suffix. This transports independently accepted extraction
closures, without assuming that their generated functions are identical. -/
theorem skip_success_from_prefix (bytes after : Slice U8) (value : U64) (count : Nat)
    (hc : count ≤ 10)
    (hp : ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) 0 =
      ⟨255,BitVec.ofNat 64 count,value.bv⟩)
    (hs : after = drop bytes count) :
    LoopSupportSkip.encoding.varint.decode_varint sliceBuf bytes = .ok (.Ok value,after) := by
  obtain ⟨result,remaining,hd,hpost,_⟩ := decode_full_reference bytes
  cases result with
  | Err error =>
    have he := congrArg ProtoParse.Decoded.ok hp
    rw [hpost.2] at he
    cases he
  | Ok value' =>
    obtain ⟨count',_,hc',hp',hs'⟩ := hpost
    have he := hp.symm.trans hp'
    have hv : value = value' := by
      apply UScalar.eq_of_val_eq
      have h := congrArg BitVec.toNat (congrArg ProtoParse.Decoded.value he)
      simpa only [UScalar.bv_toNat] using h
    have hn : count = count' := (small_word_eq count count' (by omega) (by omega)).mp (congrArg ProtoParse.Decoded.stop he)
    subst value'
    subst count'
    have ha : remaining = after := hs'.trans hs.symm
    simpa only [ha] using hd

theorem field_success_to_skip (bytes after : Slice U8) (value : U64)
    (hp : LibSignalReference.Candidate.ProstFieldBuf.PrefixPost bytes (.Ok value) after) :
    LoopSupportSkip.encoding.varint.decode_varint sliceBuf bytes = .ok (.Ok value,after) := by
  obtain ⟨count,_,hc,hr,hs⟩ := hp
  exact skip_success_from_prefix bytes after value count hc hr hs

theorem bytes_success_to_skip (bytes after : Slice U8) (value : U64)
    (hp : LibSignalReference.Candidate.ProstBytesBuf.PrefixPost bytes (.Ok value) after) :
    LoopSupportSkip.encoding.varint.decode_varint sliceBuf bytes = .ok (.Ok value,after) := by
  obtain ⟨count,_,hc,hr,hs⟩ := hp
  exact skip_success_from_prefix bytes after value count hc hr hs

#print axioms skip_success_from_prefix
#print axioms field_success_to_skip
#print axioms bytes_success_to_skip
end FullParserV3
