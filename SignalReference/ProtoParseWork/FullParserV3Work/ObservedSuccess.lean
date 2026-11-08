import ProtoParseWork.FullParserV3Work.InitialScan
import ProtoParseWork.FullParserV3Work.ObservedScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkipKey ParserErrorStateV2
set_option maxHeartbeats 3000000

theorem finish_closed_error (state : State (BitVec 8) (BitVec 64)) (hd : state.parser.depth = 0) :
    (finish Word64.concrete ByteAuth.concrete state).error = state.error := by
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.parser.depth (Word64.concrete.const 0) = 255 := by
    rw [hd]; exact word_eq_self _
  have hn : ByteAuth.concrete.not 255 = 0 := rfl
  have hz (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [finish,hh,hn,hz,Word64.select_reject]

theorem successful_parse_error (bytes : Slice U8)
    (hok : (ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)).ok = 255)
    (hd : (ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)).depth = 0) :
    (parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)).error = ⟨0,0⟩ := by
  let initial : State (BitVec 8) (BitVec 64) := ⟨initialOf bytes,⟨0,0⟩⟩
  have hl : (contents bytes).length = bytes.length := List.length_map _
  have hf : ((List.range bytes.length).foldl (ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
      initial.parser).ok = 255 := by simpa only [ProtoParse.parseBody,hl] using hok
  have herror := successful_fold_error bytes.length (List.range bytes.length) (rowsOf bytes) initial
    (table_masks bytes) rfl (initial_at bytes).fields_mask hf
  have hp := fold_erasure bytes.length (List.range bytes.length) (rowsOf bytes) initial
  have hdepth : ((List.range bytes.length).foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes)) initial).parser.depth = 0 := by
    rw [hp]
    simpa only [ProtoParse.parseBody,hl] using hd
  unfold parse
  simp only [hl]
  change (finish Word64.concrete ByteAuth.concrete ((List.range bytes.length).foldl
    (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes)) initial)).error = ⟨0,0⟩
  rw [finish_closed_error _ hdepth]
  exact herror

/-- Actual extracted merge success has success metadata in the isolated
observed-state wrapper, while erasure keeps production parser behavior exact. -/
theorem actual_successful_observation (unused : ActualMessageDriver.prost.message.Message Message)
    (bytes : Slice U8) (message : Message) (hcap : bytes.length ≤ 512)
    (hactual : ActualMessageDriver.prost.message.Message.merge.default (withDispatcher unused) driverBuf emptyMessage bytes =
      .ok (.Ok (),message)) :
    let observed := parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
    ∃ hat : StateAt bytes bytes.length observed.parser [],
      messageView bytes observed.parser.fields hat.fields_size = message ∧ observed.error = ⟨0,0⟩ := by
  obtain ⟨hat,hview⟩ := actual_successful_parse unused bytes message hcap hactual
  have he := erase_parse VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
  have hd : (ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)).depth = 0 := hat.frames.depth_eq
  have herr := successful_parse_error bytes hat.ok hd
  dsimp only
  simp only [he]
  exact ⟨hat,hview,herr⟩

#print axioms successful_parse_error
#print axioms actual_successful_observation
end FullParserV3.Observed
