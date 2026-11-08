import ProtoParseWork.FullParserV3Work.KeyRejectionCursor
import ProtoParseWork.FullParserV3Work.ObservedScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipKey
open ParserErrorStateV2
set_option maxHeartbeats 3000000

private theorem initialize_zero_tag_any (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (enabled : BitVec 8) (hl : fields.length ≤ 6) :
    ProtoParse.initializeFields Word64.concrete ByteAuth.concrete enabled 0 fields = fields := by
  apply List.ext_getElem
  · simp only [ProtoParse.initializeFields,List.length_map,List.length_zipIdx]
  · intro i h1 h2
    have hn : (0 : BitVec 64) ≠ Word64.concrete.const (i+1) := by
      intro he
      have hv := congrArg BitVec.toNat he
      change 0 = (BitVec.ofNat 64 (i+1)).toNat at hv
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hv
      omega
    have hz (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
    simp only [ProtoParse.initializeFields,List.getElem_map,List.getElem_zipIdx,Nat.zero_add,word_eq_value,if_neg hn,hz]
    exact select_zero _ _

theorem apply_key_reject (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hs : state.ok = 255) (hn : state.next = BitVec.ofNat 64 position)
    (hp : p.ok = 0) (ht : p.tag = 0) (hl : state.fields.length ≤ 6) :
    let result := ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state
    result.ok = 0 ∧ result.next = p.stop ∧ result.depth = state.depth ∧
      result.stack = state.stack ∧ result.fields = state.fields := by
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.next (Word64.concrete.const position) = 255 := by
    rw [hn]; exact word_eq_self _
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [ProtoParse.applyPlan,hs,hh,hp,ht,show ByteAuth.concrete.and 255 255 = 255 from rfl,
    show ByteAuth.concrete.and 255 0 = 0 from rfl,hz]
  refine ⟨rfl,?_,?_,?_,?_⟩
  · exact Word64.select_accept _ _
  · exact Word64.select_reject _ _
  · exact ParserErrorStateV2.stack_zero state.depth 0 state.stack
  · rw [write_zero,initialize_zero_tag_any _ _ hl]

namespace Observed

theorem step_rejection_error (capacity position : Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64))) (state : State (BitVec 8) (BitVec 64))
    (hs : state.parser.ok = 255) (hn : state.parser.next = BitVec.ofNat 64 position)
    (hp : (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position
      (rows[capacity-1]?.getD ⟨0,BitVec.ofNat 64 (capacity-1),0⟩).ok
      (rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩)
      (ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete
        (rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩).stop (position+1) ((rows.drop (position+1)).take 10)) state.parser).ok = 0) :
    (step Word64.concrete ByteAuth.concrete capacity rows state position).error =
    classify Word64.concrete ByteAuth.concrete (rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩)
      (ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete
        (rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩).stop (position+1) ((rows.drop (position+1)).take 10)) state.parser := by
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  let lastClear := (rows[capacity-1]?.getD ⟨0,BitVec.ofNat 64 (capacity-1),0⟩).ok
  let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload state.parser
  have hp' : p.ok = 0 := hp
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.parser.next (Word64.concrete.const position) = 255 := by
    rw [hn]; exact word_eq_self _
  let failed := ByteAuth.concrete.and state.parser.ok
    (ByteAuth.concrete.and (Word64.eq Word64.concrete ByteAuth.concrete state.parser.next (Word64.concrete.const position))
      (ByteAuth.concrete.not p.ok))
  have hfailed : failed = 255 := by dsimp only [failed]; rw [hs,hh,hp']; rfl
  dsimp only [step]
  change (⟨Word64.concrete.select failed (classify Word64.concrete ByteAuth.concrete key payload state.parser).code state.error.code,
    Word64.concrete.select failed (classify Word64.concrete ByteAuth.concrete key payload state.parser).parameter state.error.parameter⟩ : ErrorMeta (BitVec 64)) =
    classify Word64.concrete ByteAuth.concrete key payload state.parser
  rw [hfailed]
  simp only [Word64.select_accept]

/-- Every actual malformed key freezes exact rejection, full fields, Rust suffix
and constructor/parameters through every later public position. This observes
internal error state rather than the production all-zero external mask. -/
theorem actual_key_rejection_step (bytes after : Slice U8) (position : Nat)
    (error : LoopSupportSkip.error.DecodeError) (state : State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.parser.ok = 255) (hn : state.parser.next = BitVec.ofNat 64 position)
    (hl : state.parser.fields.length = 6)
    (hd : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Err error,after)) :
    ∀ positions : List Nat,
      let result := positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position)
      result.parser.ok = 0 ∧ after = drop bytes result.parser.next.toNat ∧
      result.parser.next.toNat ≤ bytes.length ∧ result.parser.fields = state.parser.fields ∧
      statusView (.Err (SignalMessageIntegration.skipError error)) = some result.error := by
  let rows := rowsOf bytes
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  let lastClear := (rows[bytes.length-1]?.getD ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok
  let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position lastClear key payload state.parser
  have hplan := actual_key_rejection_plan bytes after position error payload state.parser hp hcap hd
  have hp0 : p.ok = 0 := hplan.1
  have ht0 : p.tag = 0 := hplan.2.1
  have ha : after = drop bytes p.stop.toNat := hplan.2.2.1
  have hb : p.stop.toNat ≤ bytes.length := hplan.2.2.2.1
  have hm := hplan.2.2.2.2
  have hnumeric := apply_key_reject position p state.parser hs hn hp0 ht0 (by omega)
  have hparser : (step Word64.concrete ByteAuth.concrete bytes.length rows state position).parser =
      ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state.parser := rfl
  have herror := step_rejection_error bytes.length position rows state hs hn hp0
  intro positions
  dsimp only
  rw [scan_failed bytes.length positions rows _ (by rw [hparser]; exact hnumeric.1)]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hparser]; exact hnumeric.1
  · rw [hparser,hnumeric.2.1]; exact ha
  · rw [hparser,hnumeric.2.1]; exact hb
  · rw [hparser]; exact hnumeric.2.2.2.2
  · rw [herror]
    exact hm

#print axioms step_rejection_error
#print axioms actual_key_rejection_step
end Observed
#print axioms apply_key_reject
end FullParserV3
