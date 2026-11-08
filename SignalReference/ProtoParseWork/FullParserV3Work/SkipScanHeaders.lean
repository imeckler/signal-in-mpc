import ProtoParseWork.FullParserV3Work.SkipScanLeaves
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 3000000

private theorem package_header_scan (bytes after : Slice U8) (position finish : Nat)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (oldTags tags : List U32)
    (hat : StateAt bytes position state oldTags) (hp : position < finish) (hb : finish ≤ bytes.length)
    (ha : after = drop bytes finish) (hs : (stepOf bytes state position).ok = 255)
    (hn : (stepOf bytes state position).next = BitVec.ofNat 64 finish)
    (hf : Frames (stepOf bytes state position).depth (stepOf bytes state position).stack tags)
    (hfields : (stepOf bytes state position).fields = state.fields)
    (hstack : (stepOf bytes state position).stack.length = min 100 bytes.length)
    (hframes : tags.length ≤ finish)
    (hscan : scanOf bytes position finish state = stepOf bytes state position) : SkipScan bytes position state after tags := by
  refine ⟨finish,stepOf bytes state position,hp,hb,ha,hscan,?_,hfields⟩
  refine {ok := hs,cursor := hn,frames := hf,frames_before := hframes,stack_size := hstack,fields_size := ?_,fields_mask := ?_}
  · rw [hfields]; exact hat.fields_size
  · rw [hfields]; exact hat.fields_mask

theorem start_header_scan (bytes middle : Slice U8) (position : Nat) (tag count : U32)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state tags) (hc : count ≠ 0#u32) (hbudget : count.val+tags.length = 100)
    (hskip : state.depth ≠ 0 ∨ 6 < tag.val)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.StartGroup),middle)) :
    SkipScan bytes position state middle (tags++[tag]) := by
  have hlimit : tags.length ≤ 99 := by have := budget_depth_limit hat count hc hbudget; rw [hat.depth_nat] at this; exact this
  obtain ⟨finish,hp',hb,ha,hs,hn,hf,hfields,hstack,hframes,hscan⟩ := group_start_scan bytes middle position tag tags state
    hp hcap hat.ok hat.cursor hat.frames hat.frames_before hlimit hat.stack_size (by rw [hat.fields_size]) hskip hk
  exact package_header_scan bytes middle position finish state tags (tags++[tag]) hat hp' hb ha hs hn hf hfields hstack hframes hscan

theorem end_header_scan (bytes after : Slice U8) (position : Nat) (tag : U32)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state (tags++[tag]))
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.EndGroup),after)) :
    SkipScan bytes position state after tags := by
  obtain ⟨finish,hp',hb,ha,hs,hn,hf,hfields,hstack,hframes,hscan⟩ := group_end_scan bytes after position tag tags state
    hp hcap hat.ok hat.cursor hat.frames hat.frames_before hat.stack_size hk
  exact package_header_scan bytes after position finish state (tags++[tag]) tags hat hp' hb ha hs hn hf hfields hstack hframes hscan

theorem concat_skip_scan (bytes after : Slice U8) (position middle : Nat)
    (state intermediate : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < middle)
    (hscan : scanOf bytes position middle state = intermediate)
    (hf : intermediate.fields = state.fields)
    (rest : SkipScan bytes middle intermediate after tags) : SkipScan bytes position state after tags := by
  obtain ⟨finish,result,hm,hb,ha,hr,hat,hfields⟩ := rest
  refine ⟨finish,result,by omega,hb,ha,?_,hat,hfields.trans hf⟩
  unfold scanOf at *
  rw [scan_split bytes.length position middle finish (rowsOf bytes) state (by omega) (by omega),hscan,hr]

#print axioms start_header_scan
#print axioms end_header_scan
#print axioms concat_skip_scan
end FullParserV3
