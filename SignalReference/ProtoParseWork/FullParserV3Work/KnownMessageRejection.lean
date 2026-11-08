import ProtoParseWork.FullParserV3Work.KnownRejectionStep
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstTopField ParserErrorStateV2
set_option maxHeartbeats 3000000

private theorem message_view_congr (bytes : Slice U8)
    (left right : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (hl : left.length = 6) (hr : right.length = 6) (he : left = right) :
    messageView bytes left hl = messageView bytes right hr := by
  cases he
  rfl

/-- Every actual generated known-field failure agrees with the complete
remaining public scan, exact native error, cursor/suffix and all six Rust
Options. Existing and absent values, duplicates and wrong wires are included. -/
theorem actual_known_message_rejection (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (error : prost.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (message next : Message) (ctx : prost.encoding.DecodeContext)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state.parser [])
    (hview : messageView bytes state.parser.fields hat.fields_size = message)
    (ht : 0 < tag.val) (hb : tag.val ≤ 6)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field DispatcherIntegration.sliceBuf
      message tag (signalWire kind) middle ctx = .ok (.Err error,next,after)) :
    ∀ positions : List Nat,
      let result := finish Word64.concrete ByteAuth.concrete (positions.foldl
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position))
      ∃ hsize : result.parser.fields.length = 6,
        ActiveRejection bytes after error state result
          (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 (BitVec.ofNat 64 tag.val) state.parser.fields) ∧
        messageView bytes result.parser.fields hsize = next := by
  obtain ⟨cases,hinit⟩ := actual_known_error_cases message next tag (signalWire kind) middle after ctx error ht hb hm
  have hz : state.parser.depth = 0 := hat.frames.depth_eq
  intro positions
  have hactive := known_case_rejection bytes middle after position tag kind error state hp hcap
    hat.ok hat.cursor hz hk cases positions
  have hsize : (finish Word64.concrete ByteAuth.concrete (positions.foldl
      (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
      (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position))).parser.fields.length = 6 := by
    rw [hactive.fields_eq,initialize_length]
    exact hat.fields_size
  refine ⟨hsize,hactive,?_⟩
  have he := message_view_congr bytes _ _ hsize
    (by rw [initialize_length]; exact hat.fields_size) hactive.fields_eq
  have hi := message_initialize_view bytes state.parser.fields (BitVec.ofNat 64 tag.val) hat.fields_size hat.fields_mask
  exact he.trans (hi.trans ((congrArg (initializeMessage (BitVec.ofNat 64 tag.val)) hview).trans hinit.symm))

#print axioms actual_known_message_rejection
end FullParserV3.Observed
