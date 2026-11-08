import ProtoParseWork.FullParserV3Work.TopBytesScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 3000000

def signalWire (kind : LoopSupportSkip.encoding.wire_type.WireType) : prost.encoding.wire_type.WireType :=
  wireToSignal (ActualMessageDriver.wireFromSkip kind)

theorem signal_wire_varint {kind : LoopSupportSkip.encoding.wire_type.WireType}
    (h : signalWire kind = .Varint) : kind = .Varint := by
  cases kind <;> cases h <;> rfl

theorem signal_wire_bytes {kind : LoopSupportSkip.encoding.wire_type.WireType}
    (h : signalWire kind = .LengthDelimited) : kind = .LengthDelimited := by
  cases kind <;> cases h <;> rfl

/-- Complete successful top-level message observation after one or more public
scan positions. Errors are not encoded by this separate success relation. -/
def MessageScan (bytes : Slice U8) (position : Nat) (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (after : Slice U8) (message : Message) : Prop :=
  ∃ finish result, position < finish ∧ finish ≤ bytes.length ∧ after = drop bytes finish ∧
    scanOf bytes position finish state = result ∧
    ∃ hat : StateAt bytes finish result [], messageView bytes result.fields hat.fields_size = message

theorem known_message_scan (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (message next : Message) (ctx : prost.encoding.DecodeContext)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state [])
    (hview : messageView bytes state.fields hat.fields_size = message)
    (ht : 0 < tag.val) (hb : tag.val ≤ 6)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field DispatcherIntegration.sliceBuf
      message tag (signalWire kind) middle ctx = .ok (.Ok (),next,after)) : MessageScan bytes position state after next := by
  have h := known_dispatch_success message next tag (signalWire kind) middle after ctx ht hb hm
  cases h with
  | scalar htag hwire raw hd hnext =>
    have he := signal_wire_varint hwire
    subst kind
    obtain ⟨finish,hp',hb',ha,hresult,hscan,hfields⟩ := top_scalar_scan bytes middle after position tag raw state hp hcap hat htag hk hd
    refine ⟨finish,stepOf bytes state position,hp',hb',ha,hscan,hresult,?_⟩
    rw [hfields,hview]
    exact hnext.symm
  | bytes htag hwire raw rest hd hn ha hnext =>
    have he := signal_wire_bytes hwire
    subst kind
    obtain ⟨finish,hp',hb',hafter,hresult,hscan,hfields⟩ := top_bytes_scan bytes middle rest after position tag raw state hp hcap hat htag hk hd hn ha
    refine ⟨finish,stepOf bytes state position,hp',hb',hafter,hscan,hresult,?_⟩
    rw [hfields,hview]
    exact hnext.symm

#print axioms known_message_scan
end FullParserV3
