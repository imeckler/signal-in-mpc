import ProtoParseWork.FullParserV3Work.GroupHeaderScan
import ProtoParseWork.FullParserV3Work.ScanMasks
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipKey LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 2000000

abbrev rowsOf (bytes : Slice U8) := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
  (LibSignalReference.Candidate.ProstSkipSlice.contents bytes)
abbrev stepOf (bytes : Slice U8) := ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes)
def scanOf (bytes : Slice U8) (start finish : Nat) (state : ProtoParse.State (BitVec 8) (BitVec 64)) :=
  (List.range' start (finish-start)).foldl (stepOf bytes) state

structure StateAt (bytes : Slice U8) (position : Nat) (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32) : Prop where
  ok : state.ok = 255
  cursor : state.next = BitVec.ofNat 64 position
  frames : Frames state.depth state.stack tags
  frames_before : tags.length ≤ position
  stack_size : state.stack.length = min 100 bytes.length
  fields_size : state.fields.length = 6
  fields_mask : FieldMasks state.fields

theorem StateAt.depth_nat {bytes position state tags} (h : StateAt bytes position state tags) :
    state.depth.toNat = tags.length := by
  have hb := h.frames.bound.trans h.frames.limit
  rw [h.frames.depth_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

theorem StateAt.nested {bytes position state tags} (h : StateAt bytes position state tags) (hn : tags ≠ []) :
    state.depth ≠ 0 := by
  intro hz
  have hd := h.depth_nat
  rw [hz] at hd
  have hl : tags.length = 0 := by change 0 = tags.length at hd; omega
  exact hn (List.length_eq_zero_iff.mp hl)

/-- Successful full interval observation for skips; live stack frames, complete
fields and exact suffix remain in the relation. Only dead stack scratch differs. -/
def SkipScan (bytes : Slice U8) (position : Nat) (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (after : Slice U8) (tags : List U32) : Prop :=
  ∃ finish result, position < finish ∧ finish ≤ bytes.length ∧ after = drop bytes finish ∧
    scanOf bytes position finish state = result ∧ StateAt bytes finish result tags ∧ result.fields = state.fields

theorem apply_nonstart_stack (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : p.kind ≠ 3) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).stack = state.stack := by
  have ht : Word64.eq Word64.concrete ByteAuth.concrete p.kind (Word64.concrete.const 3) = 0 := by
    rw [word_eq_value]; exact if_neg hk
  have hz (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [ProtoParse.applyPlan,ht,hz,ParserErrorStateV2.stack_zero]

theorem actual_nonstart_stack (bytes middle : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hp : position < bytes.length)
    (hn : kind ≠ .StartGroup)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle)) :
    (stepOf bytes state position).stack = state.stack := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hkind,_⟩ := actual_key_row bytes middle position tag kind hp hk
  apply apply_nonstart_stack
  change ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩).value &&& 7 ≠ 3
  rw [hkind]
  cases kind <;> simp_all [wireNumber]

theorem package_leaf_scan (bytes after : Slice U8) (position finish : Nat)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hat : StateAt bytes position state tags) (hp : position < finish) (hb : finish ≤ bytes.length)
    (ha : after = drop bytes finish)
    (hs : (stepOf bytes state position).ok = 255)
    (hn : (stepOf bytes state position).next = BitVec.ofNat 64 finish)
    (hd : (stepOf bytes state position).depth = state.depth)
    (hf : (stepOf bytes state position).fields = state.fields)
    (hstack : (stepOf bytes state position).stack = state.stack)
    (hscan : scanOf bytes position finish state = stepOf bytes state position) : SkipScan bytes position state after tags := by
  refine ⟨finish,stepOf bytes state position,hp,hb,ha,hscan,?_,hf⟩
  refine {ok := hs,cursor := hn,frames := ?_,frames_before := ?_,stack_size := ?_,fields_size := ?_,fields_mask := ?_}
  · simpa only [hd,hstack] using hat.frames
  · have := hat.frames_before; omega
  · rw [hstack]; exact hat.stack_size
  · rw [hf]; exact hat.fields_size
  · rw [hf]; exact hat.fields_mask

#print axioms actual_nonstart_stack
#print axioms package_leaf_scan
end FullParserV3
