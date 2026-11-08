import ProtoParseWork.FullParserV3Work.RejectionState
import ProtoParseWork.FullParserV3Work.ObservedSuccess
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LoopSupportSkip LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkipKey ParserErrorStateV2
set_option maxHeartbeats 3000000

theorem key_empty_error (bytes : Slice U8) (hlen : bytes.length = 0) :
    encoding.decode_key sliceBuf bytes = .ok (.Err invalidError,bytes) := by
  have hz : bytes.len = 0#usize := by apply UScalar.eq_of_val_eq; rw [Slice.len_val]; exact hlen
  have hv : encoding.varint.decode_varint sliceBuf bytes = .ok (.Err invalidError,bytes) := by
    rw [encoding.varint.decode_varint,chunk_spec]
    simp only [bind_tc_ok]
    rw [if_pos hz,invalid_conversion]
    rfl
  exact key_from_varint bytes bytes (.Err invalidError) hv

namespace Observed

theorem finish_unclosed (state : State (BitVec 8) (BitVec 64))
    (hs : state.parser.ok = 255) (hd : state.parser.depth ≠ 0) :
    finish Word64.concrete ByteAuth.concrete state = ⟨state.parser,⟨1,0⟩⟩ := by
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.parser.depth (Word64.concrete.const 0) = 0 := by
    rw [word_eq_value]; exact if_neg hd
  simp only [finish,hs,hh]
  change (⟨state.parser,⟨Word64.concrete.select 255 (Word64.concrete.const 1) _,
    Word64.concrete.select 255 (Word64.concrete.const 0) _⟩⟩ : State (BitVec 8) (BitVec 64)) = _
  simp only [Word64.select_accept]
  rfl

/-- EOF in an open group is an actual InvalidVarint rejection with an unchanged
record and exact empty suffix. Raw numeric ok remains255, while completeMask=0;
this distinct error observation is preserved rather than disguised as success. -/
theorem actual_eof_group_rejection (bytes after : Slice U8) (error : LoopSupportSkip.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hcap : bytes.length ≤ 512) (hat : StateAt bytes bytes.length state.parser tags) (hn : tags ≠ [])
    (hd : encoding.decode_key sliceBuf (drop bytes bytes.length) = .ok (.Err error,after)) :
    let result := finish Word64.concrete ByteAuth.concrete state
    result.parser.ok = 255 ∧ ProtoParse.completeMask Word64.concrete ByteAuth.concrete bytes.length result.parser = 0 ∧
      after = drop bytes result.parser.next.toNat ∧ result.parser.next.toNat ≤ bytes.length ∧
      result.parser.fields = state.parser.fields ∧ result.parser.stack = state.parser.stack ∧
      statusView (.Err (SignalMessageIntegration.skipError error)) = some result.error := by
  have he := key_empty_error (drop bytes bytes.length) (by rw [drop_length]; omega)
  rw [hd] at he
  have herr : error = invalidError := core.result.Result.Err.inj (congrArg Prod.fst (Result.ok.inj he))
  have hafter : after = drop bytes bytes.length := congrArg Prod.snd (Result.ok.inj he)
  have hdepth : state.parser.depth ≠ 0 := hat.nested hn
  dsimp only
  rw [finish_unclosed state hat.ok hdepth]
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.parser.depth (Word64.concrete.const 0) = 0 := by
    rw [word_eq_value]; exact if_neg hdepth
  have hnext : state.parser.next.toNat = bytes.length := by
    rw [hat.cursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  refine ⟨hat.ok,?_,?_,?_,rfl,rfl,?_⟩
  · have hz (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
    simp only [ProtoParse.completeMask,hh,hz]
  · rw [hnext]; exact hafter
  · rw [hnext]
  · rw [herr]; rfl

#print axioms finish_unclosed
#print axioms actual_eof_group_rejection
end Observed
#print axioms key_empty_error
end FullParserV3
