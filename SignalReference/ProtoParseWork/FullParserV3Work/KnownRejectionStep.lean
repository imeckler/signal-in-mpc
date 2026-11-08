import ProtoParseWork.FullParserV3Work.KnownErrorCases
import ProtoParseWork.FullParserV3Work.KnownMask
import ProtoParseWork.FullParserV3Work.ScalarWrongRejection
import ProtoParseWork.FullParserV3Work.BytesWrongRejection
import ProtoParseWork.FullParserV3Work.PayloadActive
import ProtoParseWork.FullParserV3Work.LengthRejectionStep
import ProtoParseWork.FullParserV3Work.TopRejection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 3000000

theorem known_case_rejection (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (error : prost.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.parser.ok = 255) (hn : state.parser.next = BitVec.ofNat 64 position) (hz : state.parser.depth = 0)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (cases : KnownErrorCase error tag (signalWire kind) middle after) :
    ∀ positions : List Nat, ActiveRejection bytes after error state
      (finish Word64.concrete ByteAuth.concrete (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position)))
      (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 (BitVec.ofNat 64 tag.val) state.parser.fields) := by
  have hdepth : state.parser.depth.toNat ≤ 99 := by rw [hz]; decide
  cases cases with
  | scalarWrong ht hw ha he =>
    have hw' : kind ≠ .Varint := by intro h; apply hw; cases h; rfl
    rw [ha,he]
    exact actual_scalar_wrong_rejection bytes middle position tag kind state hp hcap hs hn hz ht hw' hk
  | bytesWrong ht hw ha he =>
    have hw' : kind ≠ .LengthDelimited := by intro h; apply hw; cases h; rfl
    rw [ha,he]
    exact actual_bytes_wrong_rejection bytes middle position tag kind state hp hcap hs hn hz ht hw' hk
  | scalarPayload ht hw he hd =>
    have hkind := signal_wire_varint hw
    subst kind
    have heq : error = skipError invalidError := he.trans rfl
    rw [heq]
    intro positions
    exact top_rejection_fields bytes after _ state _ (BitVec.ofNat 64 tag.val) hz
      (payload_active bytes middle after position tag .Varint invalidError state hp hcap hs hn hk hd
        (Or.inl rfl) hdepth (actual_scalar_mask bytes middle position tag state.parser hp hz ht hk) positions)
  | bytesPayload ht hw he hd =>
    have hkind := signal_wire_bytes hw
    subst kind
    have heq : error = skipError invalidError := he.trans rfl
    rw [heq]
    intro positions
    exact top_rejection_fields bytes after _ state _ (BitVec.ofNat 64 tag.val) hz
      (payload_active bytes middle after position tag .LengthDelimited invalidError state hp hcap hs hn hk hd
        (Or.inr rfl) hdepth (actual_bytes_mask bytes middle position tag state.parser hp hz ht hk) positions)
  | bytesUnderflow ht hw he raw hd hshort =>
    have hkind := signal_wire_bytes hw
    subst kind
    have heq : error = skipError (decodeError .BufferUnderflow) := he.trans rfl
    have hc : (100#u32) ≠ 0#u32 := by decide
    have hskip := length_delimited_after middle after raw tag 100#u32 hc hd
    simp only [fixedResult,if_pos hshort] at hskip
    rw [heq]
    intro positions
    exact top_rejection_fields bytes after _ state _ (BitVec.ofNat 64 tag.val) hz
      (actual_length_rejection_step bytes middle after after position tag 100#u32 raw (decodeError .BufferUnderflow)
        state hp hcap hs hn hdepth hc (actual_bytes_mask bytes middle position tag state.parser hp hz ht hk) hk hd hskip positions)

#print axioms known_case_rejection
end FullParserV3.Observed
