import ProtoParseWork.FullParserV3Work.KnownMessageScan
import ProtoParseWork.FullParserV3Work.PayloadPlan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 2000000
private theorem scalar_tag_words (tag : U32) (ht : ScalarTag tag) :
    BitVec.ofNat 64 tag.val = 2 ∨ BitVec.ofNat 64 tag.val = 3 := by
  rcases ht with rfl | rfl <;> decide
private theorem bytes_tag_words (tag : U32) (ht : BytesTag tag) :
    BitVec.ofNat 64 tag.val = 1 ∨ BitVec.ofNat 64 tag.val = 4 ∨ BitVec.ofNat 64 tag.val = 5 ∨ BitVec.ofNat 64 tag.val = 6 := by
  rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem actual_scalar_mask (bytes middle : Slice U8) (position : Nat) (tag : U32)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hp : position < bytes.length)
    (hd : state.depth = 0) (ht : ScalarTag tag)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (LibSignalReference.Candidate.ProstSkipBuf.drop bytes position) =
      .ok (.Ok (tag,.Varint),middle)) :
    validKnownMask ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩) state = 255 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,htag,hkind,_⟩ := actual_key_row bytes middle position tag .Varint hp hk
  apply valid_known_scalar _ state hd _ hkind
  rw [htag]
  exact scalar_tag_words tag ht

theorem actual_bytes_mask (bytes middle : Slice U8) (position : Nat) (tag : U32)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hp : position < bytes.length)
    (hd : state.depth = 0) (ht : BytesTag tag)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (LibSignalReference.Candidate.ProstSkipBuf.drop bytes position) =
      .ok (.Ok (tag,.LengthDelimited),middle)) :
    validKnownMask ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩) state = 255 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,htag,hkind,_⟩ := actual_key_row bytes middle position tag .LengthDelimited hp hk
  apply valid_known_bytes _ state hd _ hkind
  rw [htag]
  exact bytes_tag_words tag ht

#print axioms actual_scalar_mask
#print axioms actual_bytes_mask
end FullParserV3
