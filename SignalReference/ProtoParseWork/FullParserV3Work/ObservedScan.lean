import ProtoParseWork.FullParserV3Work.ObservedProofs
import ProtoParseWork.FullParserV3Work.ScanMasks
open TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
private theorem and_zero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
private theorem accept_not_mask (x : BitVec 8) :
    ByteAuth.concrete.and 255 (ByteAuth.concrete.not (ByteAuth.concrete.and 255 (ByteAuth.concrete.not x))) = x := by
  change (255 : BitVec 8) &&& ~~~((255 : BitVec 8) &&& ~~~x) = x
  simp only [show (255 : BitVec 8) = BitVec.allOnes 8 from rfl,BitVec.allOnes_and,BitVec.not_not]

theorem step_failed (capacity position : Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64))) (state : State (BitVec 8) (BitVec 64))
    (hs : state.parser.ok = 0) : step Word64.concrete ByteAuth.concrete capacity rows state position = state := by
  have hp := ParserErrorStateV2.step_failed capacity rows state.parser position hs
  dsimp only [step]
  rw [hp,hs]
  simp only [zero_and,Word64.select_reject]

theorem scan_failed (capacity : Nat) (positions : List Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64))) (state : State (BitVec 8) (BitVec 64))
    (hs : state.parser.ok = 0) : positions.foldl (step Word64.concrete ByteAuth.concrete capacity rows) state = state := by
  induction positions with
  | nil => rfl
  | cons p rest ih => rw [List.foldl_cons,step_failed capacity p rows state hs]; exact ih

/-- Full failed-state instrumentation freezes with the actual numeric rejection;
constructors/parameters are not recomputed from speculative later decodes. -/
theorem step_success_error (capacity position : Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64))) (state : State (BitVec 8) (BitVec 64))
    (hs : state.parser.ok = 255)
    (hout : (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows state.parser position).ok = 255) :
    (step Word64.concrete ByteAuth.concrete capacity rows state position).error = state.error := by
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  let lastClear := (rows[capacity-1]?.getD ⟨0,BitVec.ofNat 64 (capacity-1),0⟩).ok
  let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload state.parser
  have hfailed : ByteAuth.concrete.and state.parser.ok
      (ByteAuth.concrete.and (Word64.eq Word64.concrete ByteAuth.concrete state.parser.next (Word64.concrete.const position))
        (ByteAuth.concrete.not p.ok)) = 0 := by
    by_cases hn : state.parser.next = BitVec.ofNat 64 position
    · have hh : Word64.eq Word64.concrete ByteAuth.concrete state.parser.next (Word64.concrete.const position) = 255 := by
        rw [word_eq_value]; exact if_pos hn
      have hp : p.ok = 255 := by
        change ByteAuth.concrete.and state.parser.ok (ByteAuth.concrete.not
          (ByteAuth.concrete.and (Word64.eq Word64.concrete ByteAuth.concrete state.parser.next (Word64.concrete.const position))
            (ByteAuth.concrete.not p.ok))) = 255 at hout
        rw [hs,hh,accept_not_mask] at hout
        exact hout
      rw [hs,hh,hp]
      rfl
    · have hh : Word64.eq Word64.concrete ByteAuth.concrete state.parser.next (Word64.concrete.const position) = 0 := by
        rw [word_eq_value]; exact if_neg hn
      rw [hh,zero_and,and_zero]
  dsimp only [step]
  change (⟨Word64.concrete.select (ByteAuth.concrete.and state.parser.ok
      (ByteAuth.concrete.and (Word64.eq Word64.concrete ByteAuth.concrete state.parser.next (Word64.concrete.const position))
        (ByteAuth.concrete.not p.ok))) (classify Word64.concrete ByteAuth.concrete key payload state.parser).code state.error.code,
    Word64.concrete.select (ByteAuth.concrete.and state.parser.ok
      (ByteAuth.concrete.and (Word64.eq Word64.concrete ByteAuth.concrete state.parser.next (Word64.concrete.const position))
        (ByteAuth.concrete.not p.ok))) (classify Word64.concrete ByteAuth.concrete key payload state.parser).parameter state.error.parameter⟩ : ErrorMeta (BitVec 64)) = state.error
  rw [hfailed]
  simp only [Word64.select_reject]
  all_goals rfl

theorem fold_erasure (capacity : Nat) (positions : List Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64))) (state : State (BitVec 8) (BitVec 64)) :
    (positions.foldl (step Word64.concrete ByteAuth.concrete capacity rows) state).parser =
    positions.foldl (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows) state.parser := by
  induction positions generalizing state with
  | nil => rfl
  | cons p rest ih => exact ih _

theorem successful_fold_error (capacity : Nat) (positions : List Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64))) (state : State (BitVec 8) (BitVec 64))
    (hr : DecoderMasks rows) (hs : state.parser.ok = 255) (hf : FieldMasks state.parser.fields)
    (hout : (positions.foldl (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows) state.parser).ok = 255) :
    (positions.foldl (step Word64.concrete ByteAuth.concrete capacity rows) state).error = state.error := by
  induction positions generalizing state with
  | nil => rfl
  | cons p rest ih =>
    have hm := FullParserV3.step_masks capacity p rows state.parser hr (Or.inr hs) hf
    rcases hm.1 with hz | ha
    · have he := ParserErrorStateV2.scan_failed capacity rows rest
        (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows state.parser p) hz
      rw [List.foldl_cons,he,hz] at hout
      cases hout
    · have h := ih (step Word64.concrete ByteAuth.concrete capacity rows state p) ha hm.2 hout
      exact h.trans (step_success_error capacity p rows state hs ha)

#print axioms step_failed
#print axioms scan_failed
#print axioms step_success_error
#print axioms successful_fold_error
end FullParserV3.Observed
