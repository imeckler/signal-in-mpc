import ProtoParseWork.FullParserV3Work.UnknownTopScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 3000000

private theorem default_count_nonzero : (100#u32) ≠ 0#u32 := by decide

theorem top_unknown_skip_scan (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state []) (ht : 6 < tag.val)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hskip : LoopSupportSkip.encoding.skip_field sliceBuf kind tag middle ⟨100#u32⟩ = .ok (.Ok (),after)) : SkipScan bytes position state after [] := by
  cases kind with
  | Varint =>
    obtain ⟨r,remaining,hr,_,_⟩ := varint_total middle
    cases r with
    | Err error => rw [skip_varint_error _ _ _ _ _ default_count_nonzero hr] at hskip; cases hskip
    | Ok raw =>
      rw [skip_varint_after _ _ _ _ _ default_count_nonzero hr] at hskip
      have ha := congrArg Prod.snd (Result.ok.inj hskip)
      change remaining = after at ha
      apply unknown_varint_scan bytes middle after position tag raw state hp hcap hat ht hk
      simpa only [ha] using hr
  | SixtyFourBit => exact unknown_fixed_scan bytes middle after position tag 100#u32 .SixtyFourBit 8 (Or.inl ⟨rfl,rfl⟩) state hp hcap hat ht hk hskip
  | ThirtyTwoBit => exact unknown_fixed_scan bytes middle after position tag 100#u32 .ThirtyTwoBit 4 (Or.inr ⟨rfl,rfl⟩) state hp hcap hat ht hk hskip
  | LengthDelimited => exact unknown_length_scan bytes middle after position tag 100#u32 state hp hcap hat ht hk hskip
  | StartGroup => exact actual_start_group_scan bytes middle after position tag 100#u32 state [] hp hcap hat (by decide) (Or.inr ht) hk hskip
  | EndGroup => rw [unexpected_end_group sliceBuf tag middle 100#u32 default_count_nonzero] at hskip; cases hskip

theorem unknown_message_scan (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (message next : Message) (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state []) (hview : messageView bytes state.fields hat.fields_size = message)
    (ht : 6 < tag.val)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field DispatcherIntegration.sliceBuf
      message tag (signalWire kind) middle ⟨100#u32⟩ = .ok (.Ok (),next,after)) : MessageScan bytes position state after next := by
  obtain ⟨result,hsem,hskip,_⟩ := skip_field_total kind tag 100#u32 middle
  rcases result with ⟨r,remaining⟩
  rw [unknown_dispatch _ _ _ _ _ _ ht] at hm
  unfold prost.encoding.skip_field at hm
  have hw : toSkipWire (signalWire kind) = kind := by cases kind <;> rfl
  rw [skip_slice_adapter,hw,hskip] at hm
  cases r with
  | Err error => cases hm
  | Ok u =>
    cases u
    cases hm
    obtain ⟨finish,result,hp',hb,ha,hscan,hat',hfields⟩ := top_unknown_skip_scan bytes middle _ position tag kind state hp hcap hat ht hk hskip
    refine ⟨finish,result,hp',hb,ha,hscan,hat',?_⟩
    simpa only [hfields] using hview

#print axioms top_unknown_skip_scan
#print axioms unknown_message_scan
end FullParserV3
