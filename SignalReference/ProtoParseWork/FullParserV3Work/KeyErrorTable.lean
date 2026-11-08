import ProtoParseWork.FullParserV3Work.KeyErrors
import ProtoParseWork.FullParserV3Work.DecoderTable
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstTopField

/-- Absolute-cursor rebasing never changes diagnostic classification. -/
theorem classify_rebase (ok : BitVec 8) (value oldStop newStop : BitVec 64)
    (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) :
    classify Word64.concrete ByteAuth.concrete ⟨ok,oldStop,value⟩ payload state =
    classify Word64.concrete ByteAuth.concrete ⟨ok,newStop,value⟩ payload state := rfl

/-- The actual key error at every public table row has exactly the private
constructor/parameter diagnostic computed by the whole-input parser. -/
theorem actual_key_error_at (bytes after : Slice U8) (position : Nat)
    (error : LoopSupportSkip.error.DecodeError)
    (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hp : position < bytes.length)
    (hd : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Err error,after)) :
    statusView (.Err (SignalMessageIntegration.skipError error)) = some (classify
      Word64.concrete ByteAuth.concrete
      ((ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (contents bytes))[position]'(by rw [table_length]; simpa only [contents,List.length_map] using hp))
      payload state) := by
  rw [table_get _ _ (by simpa only [contents,List.length_map] using hp),decode_prefix_drop,← contents_drop]
  exact actual_key_error (drop bytes position) after error payload state hd

#print axioms classify_rebase
#print axioms actual_key_error_at
end FullParserV3.Observed
