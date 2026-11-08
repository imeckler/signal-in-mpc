import ProtoParseWork.FullParserV3Work.DecoderTransport
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 2000000

/-- Error transport retains actual mutation as well as rejection. Independent
primitive extraction closures share the proved strict-prefix failure and exact
fast/slow cursor, not an assumed function-identification axiom. -/
theorem skip_error_from_prefix (bytes after : Slice U8)
    (hp : (ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) 0).ok = 0)
    (hs : after = if FastGuard bytes then bytes else drop bytes (min 10 bytes.length)) :
    LoopSupportSkip.encoding.varint.decode_varint sliceBuf bytes = .ok (.Err invalidError,after) := by
  obtain ⟨result,remaining,hd,hpost,he⟩ := decode_full_reference bytes
  cases result with
  | Ok value =>
    obtain ⟨count,_,_,hr,_⟩ := hpost
    rw [hr] at hp
    cases hp
  | Err error =>
    rw [hpost.1] at hd
    have ha : remaining = after := he.trans hs.symm
    simpa only [ha] using hd

theorem field_error_to_skip (bytes after : Slice U8) (error : ProstFieldCandidate.error.DecodeError)
    (hp : LibSignalReference.Candidate.ProstFieldBuf.PrefixPost bytes (.Err error) after)
    (he : LibSignalReference.Candidate.ProstFieldBuf.ErrorPost bytes (.Err error) after) :
    LoopSupportSkip.encoding.varint.decode_varint sliceBuf bytes = .ok (.Err invalidError,after) := by
  apply skip_error_from_prefix bytes after hp.2
  exact he

theorem bytes_error_to_skip (bytes after : Slice U8) (error : ProstBytesCandidate.error.DecodeError)
    (hp : LibSignalReference.Candidate.ProstBytesBuf.PrefixPost bytes (.Err error) after)
    (he : LibSignalReference.Candidate.ProstBytesBuf.ErrorPost bytes (.Err error) after) :
    LoopSupportSkip.encoding.varint.decode_varint sliceBuf bytes = .ok (.Err invalidError,after) := by
  apply skip_error_from_prefix bytes after hp.2
  exact he

#print axioms skip_error_from_prefix
#print axioms field_error_to_skip
#print axioms bytes_error_to_skip
end FullParserV3
