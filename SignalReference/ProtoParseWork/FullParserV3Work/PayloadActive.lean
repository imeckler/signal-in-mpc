import ProtoParseWork.FullParserV3Work.FrozenRejection
import ProtoParseWork.FullParserV3Work.PayloadRejectionStep
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 2000000

/-- Structural form of the proved payload-error observation, preserving every
component rather than reducing rejection to a boolean. -/
theorem payload_active (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (error : LoopSupportSkip.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.parser.ok = 255) (hn : state.parser.next = BitVec.ofNat 64 position)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Err error,after))
    (hkind : kind = .Varint ∨ kind = .LengthDelimited) (hdepth : state.parser.depth.toNat ≤ 99)
    (hknown : validKnownMask ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩) state.parser = 255) :
    ∀ positions : List Nat, ActiveRejection bytes after (skipError error) state
      (finish Word64.concrete ByteAuth.concrete (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position)))
      (if state.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete
        255 (BitVec.ofNat 64 tag.val) state.parser.fields else state.parser.fields) := by
  intro positions
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := actual_payload_rejection_step bytes middle after position tag kind error state
    hp hcap hs hn hk hd hkind hdepth hknown positions
  exact ⟨h1,h2,h3,h4,h5,h6,h7⟩

#print axioms payload_active
end FullParserV3.Observed
