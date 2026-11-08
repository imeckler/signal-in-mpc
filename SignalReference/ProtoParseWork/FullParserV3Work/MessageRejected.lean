import ProtoParseWork.FullParserV3Work.RejectedScan
import ProtoParseWork.FullParserV3Work.KnownMessageRejection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
set_option maxHeartbeats 2000000

/-- Complete rejected message projection used by the private compiled view.
Every unmasked field is related to its actual Rust Option, with canonical masks;
constructor/parameters, exact suffix and raw active-vs-EOF status are retained. -/
structure MessageRejected (bytes after : Slice U8) (error : prost.error.DecodeError)
    (result : State (BitVec 8) (BitVec 64)) (message : Message) : Prop where
  size : result.parser.fields.length = 6
  masks : FieldMasks result.parser.fields
  view : messageView bytes result.parser.fields size = message
  observation : RejectedObservation bytes after error result result.parser.fields

def MessageRejectedScan (bytes : Slice U8) (position : Nat) (state : State (BitVec 8) (BitVec 64))
    (after : Slice U8) (error : prost.error.DecodeError) (message : Message) :=
  MessageRejected bytes after error (finish Word64.concrete ByteAuth.concrete (scan bytes position bytes.length state)) message

private theorem view_congr (bytes : Slice U8) (left right : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (hl : left.length = 6) (hr : right.length = 6) (he : left = right) : messageView bytes left hl = messageView bytes right hr := by
  cases he
  rfl

theorem message_rejected_of_scan (bytes after : Slice U8) (position : Nat) (state : State (BitVec 8) (BitVec 64))
    (error : prost.error.DecodeError) (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) (message : Message)
    (hl : fields.length = 6) (hf : FieldMasks fields) (hv : messageView bytes fields hl = message)
    (h : RejectedScan bytes position state after error fields) : MessageRejectedScan bytes position state after error message := by
  have hsize : (finish Word64.concrete ByteAuth.concrete (scan bytes position bytes.length state)).parser.fields.length = 6 := by
    rw [h.fields_eq]; exact hl
  refine ⟨hsize,?_,?_,?_⟩
  · rw [h.fields_eq]; exact hf
  · exact (view_congr bytes _ fields hsize hl h.fields_eq).trans hv
  · exact rejected_fields_congr bytes after error _ fields _ h.fields_eq.symm h

theorem known_message_rejected_scan (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (error : prost.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (message next : Message) (ctx : prost.encoding.DecodeContext)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state.parser [])
    (hv : messageView bytes state.parser.fields hat.fields_size = message) (ht : 0 < tag.val) (hb : tag.val ≤ 6)
    (hk : LoopSupportSkip.encoding.decode_key LibSignalReference.Candidate.ProstSkipBuf.sliceBuf
      (LibSignalReference.Candidate.ProstSkipBuf.drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field DispatcherIntegration.sliceBuf
      message tag (signalWire kind) middle ctx = .ok (.Err error,next,after)) :
    MessageRejectedScan bytes position state after error next := by
  let positions := List.range' (position+1) (bytes.length-(position+1))
  obtain ⟨hl,ha,hview⟩ := actual_known_message_rejection bytes middle after position tag kind error state message next ctx
    hp hcap hat hv ht hb hk hm positions
  have ho := active_observation bytes after error state _ _ [] ha hat.frames
  have masks := initialize_masks state.parser.fields 255 (BitVec.ofNat 64 tag.val) (Or.inr rfl) hat.fields_mask
  have hmask : FieldMasks (finish Word64.concrete ByteAuth.concrete (positions.foldl
      (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
      (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position))).parser.fields := by rw [ha.fields_eq]; exact masks
  have hresult : MessageRejected bytes after error (finish Word64.concrete ByteAuth.concrete (positions.foldl
      (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
      (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position))) next :=
    ⟨hl,hmask,hview,rejected_fields_congr bytes after error _ _ _ ha.fields_eq.symm ho⟩
  unfold MessageRejectedScan scan
  have hn : bytes.length-position = (bytes.length-(position+1))+1 := by omega
  rw [hn,List.range'_succ,List.foldl_cons]
  exact hresult

#print axioms message_rejected_of_scan
#print axioms known_message_rejected_scan
end FullParserV3.Observed
