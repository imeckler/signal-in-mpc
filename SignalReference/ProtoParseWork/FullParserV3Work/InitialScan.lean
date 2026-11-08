import ProtoParseWork.FullParserV3Work.SuccessfulMessageScan
import ProtoParseWork.FullParserV3Work.DriverTotality
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 3000000

/-- Explicit six-None Rust record constructor used for the merge input. This
is not an assumed correctness axiom for a separate Message::decode wrapper. -/
def emptyMessage : Message := ⟨none,none,none,none,none,none⟩
abbrev initialOf (bytes : Slice U8) := ProtoParse.initial Word64.concrete ByteAuth.concrete bytes.length

theorem initial_at (bytes : Slice U8) : StateAt bytes 0 (initialOf bytes) [] := by
  refine {ok := rfl,cursor := rfl,frames := ?_,frames_before := by simp,stack_size := ?_,fields_size := ?_,fields_mask := ?_}
  · refine {depth_eq := rfl,bound := ?_,limit := ?_,entries := ?_}
    · simp
    · simp only [initialOf,ProtoParse.initial,List.length_replicate]; omega
    · intro i hi; simp at hi
  · simp only [initialOf,ProtoParse.initial,List.length_replicate]
  · simp only [initialOf,ProtoParse.initial,List.length_replicate]
  · intro i hi
    simp only [initialOf,ProtoParse.initial,List.getElem_replicate]
    exact Or.inl rfl

theorem initial_view (bytes : Slice U8) : messageView bytes (initialOf bytes).fields (initial_at bytes).fields_size = emptyMessage := rfl

theorem scan_initial_parse (bytes : Slice U8) : scanOf bytes 0 bytes.length (initialOf bytes) =
    ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (LibSignalReference.Candidate.ProstSkipSlice.contents bytes) := by
  have hl : (LibSignalReference.Candidate.ProstSkipSlice.contents bytes).length = bytes.length := List.length_map _
  simp only [scanOf,ProtoParse.parseBody,hl,List.range_eq_range',Nat.sub_zero]

theorem successful_trace_parse {result} (bytes : Slice U8) (hcap : bytes.length ≤ 512)
    (trace : MergeTrace ⟨100#u32⟩ emptyMessage bytes result) (hs : result.1 = .Ok ()) :
    let parsed := ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (LibSignalReference.Candidate.ProstSkipSlice.contents bytes)
    ∃ hat : StateAt bytes bytes.length parsed [], result.2.2 = drop bytes bytes.length ∧
      messageView bytes parsed.fields hat.fields_size = result.2.1 := by
  dsimp only
  obtain ⟨finalState,hscan,hat,hrest,hview⟩ := successful_message_scan trace hs bytes 0 (initialOf bytes)
    (Nat.zero_le _) hcap (initial_at bytes) rfl (initial_view bytes)
  have he : finalState = ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (LibSignalReference.Candidate.ProstSkipSlice.contents bytes) := hscan.symm.trans (scan_initial_parse bytes)
  subst finalState
  rw [← scan_initial_parse bytes]
  exact ⟨hat,hrest,hview⟩

/-- Actual extracted default Prost merge success implies full numeric parser
agreement on every supported bounded body, including all duplicates and groups.
No finite trace, primitive correctness or termination is assumed by the caller. -/
theorem actual_successful_parse (unused : ActualMessageDriver.prost.message.Message Message)
    (bytes : Slice U8) (message : Message) (hcap : bytes.length ≤ 512)
    (hactual : ActualMessageDriver.prost.message.Message.merge.default (withDispatcher unused) driverBuf emptyMessage bytes =
      .ok (.Ok (),message)) :
    let parsed := ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (LibSignalReference.Candidate.ProstSkipSlice.contents bytes)
    ∃ hat : StateAt bytes bytes.length parsed [], messageView bytes parsed.fields hat.fields_size = message := by
  obtain ⟨result,htrace,hr,_⟩ := actual_merge_total unused emptyMessage bytes
  rw [hactual] at hr
  have hs : result.1 = .Ok () := (congrArg Prod.fst (Result.ok.inj hr)).symm
  have hm : result.2.1 = message := (congrArg Prod.snd (Result.ok.inj hr)).symm
  obtain ⟨hat,_,hview⟩ := successful_trace_parse bytes hcap htrace hs
  exact ⟨hat,hview.trans hm⟩

#print axioms initial_at
#print axioms successful_trace_parse
#print axioms actual_successful_parse
end FullParserV3
