import ProtoParseWork.FullParserV3Work.WrongWireFacts
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000
theorem wrong_wire_rejection_step (bytes middle : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (error : prost.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.parser.ok = 255) (hn : state.parser.next = BitVec.ofNat 64 position)
    (hd : state.parser.depth = 0)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hv : validKnownMask ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩) state.parser = 0)
    (he : statusView (.Err error) = some ⟨5,wirePair ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩)⟩) :
    ∀ positions : List Nat, ActiveRejection bytes middle error state
      (finish Word64.concrete ByteAuth.concrete (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position)))
      (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 (BitVec.ofNat 64 tag.val) state.parser.fields) := by
  obtain ⟨hp0,ha,hb,hm,hptag⟩ := wrong_wire_facts bytes middle position tag kind error state hp hcap hs hn hd hk hv he
  intro positions
  have h := freeze_active_reject bytes middle position error state hs hn hp0 ha hb hm positions
  have hfields : (if state.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255
      (planOf bytes position state.parser).tag state.parser.fields else state.parser.fields) =
      ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 (BitVec.ofNat 64 tag.val) state.parser.fields :=
    (if_pos hd).trans (congrArg (fun tag => ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 tag state.parser.fields) hptag)
  exact Eq.mp (congrArg (fun fields => ActiveRejection bytes middle error state
    (finish Word64.concrete ByteAuth.concrete (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
      (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position))) fields) hfields) h

#print axioms wrong_wire_rejection_step
end FullParserV3.Observed
