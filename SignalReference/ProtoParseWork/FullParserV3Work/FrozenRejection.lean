import ProtoParseWork.FullParserV3Work.RejectionState
import ProtoParseWork.FullParserV3Work.FieldErrorProjection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
set_option maxHeartbeats 3000000

/-- Full internal active-failure observation. Fields are unmasked records; the
Rust diagnostic stack alone is quotiented by statusView. EOF/open-group failure
has a separate relation because its raw numeric ok need not be zero. -/
structure ActiveRejection (bytes after : Slice U8) (error : prost.error.DecodeError)
    (before result : State (BitVec 8) (BitVec 64))
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) : Prop where
  raw_rejected : result.parser.ok = 0
  cursor : after = LibSignalReference.Candidate.ProstSkipBuf.drop bytes result.parser.next.toNat
  cursor_bound : result.parser.next.toNat ≤ bytes.length
  depth : result.parser.depth = before.parser.depth
  stack : result.parser.stack = before.parser.stack
  fields_eq : result.parser.fields = fields
  error_eq : statusView (.Err error) = some result.error

def planOf (bytes : Slice U8) (position : Nat) (state : ProtoParse.State (BitVec 8) (BitVec 64)) :=
  let rows := rowsOf bytes
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position
    (rows[bytes.length-1]?.getD ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok key payload state

def classifiedAt (bytes : Slice U8) (position : Nat) (state : ProtoParse.State (BitVec 8) (BitVec 64)) :=
  let rows := rowsOf bytes
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  classify Word64.concrete ByteAuth.concrete key payload state

/-- Algebraic composition helper. Actual branch theorems discharge its plan,
metadata and suffix premises from extracted calls; this helper alone makes no
claim to be a Rust refinement. -/
theorem freeze_active_reject (bytes after : Slice U8) (position : Nat) (error : prost.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (hs : state.parser.ok = 255)
    (hn : state.parser.next = BitVec.ofNat 64 position)
    (hp : (planOf bytes position state.parser).ok = 0)
    (ha : after = LibSignalReference.Candidate.ProstSkipBuf.drop bytes (planOf bytes position state.parser).stop.toNat)
    (hb : (planOf bytes position state.parser).stop.toNat ≤ bytes.length)
    (hm : statusView (.Err error) = some (classifiedAt bytes position state.parser)) :
    ∀ positions : List Nat,
      ActiveRejection bytes after error state
        (finish Word64.concrete ByteAuth.concrete
          (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
            (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position)))
        (if state.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete
          255 (planOf bytes position state.parser).tag state.parser.fields else state.parser.fields) := by
  let p := planOf bytes position state.parser
  have hnumeric := apply_reject_any position p state.parser hs hn hp
  have hparser : (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position).parser =
      ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state.parser := rfl
  have herror : (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position).error =
      classifiedAt bytes position state.parser := step_rejection_error bytes.length position (rowsOf bytes) state hs hn hp
  intro positions
  rw [scan_failed bytes.length positions (rowsOf bytes) _ (by rw [hparser]; exact hnumeric.1),
    finish_failed _ (by rw [hparser]; exact hnumeric.1)]
  refine {raw_rejected := ?_,cursor := ?_,cursor_bound := ?_,depth := ?_,stack := ?_,fields_eq := ?_,error_eq := ?_}
  · rw [hparser]; exact hnumeric.1
  · rw [hparser,hnumeric.2.1]; exact ha
  · rw [hparser,hnumeric.2.1]; exact hb
  · rw [hparser]; exact hnumeric.2.2.1
  · rw [hparser]; exact hnumeric.2.2.2.1
  · rw [hparser]; exact hnumeric.2.2.2.2
  · rw [herror]; exact hm

#print axioms freeze_active_reject
end FullParserV3.Observed
