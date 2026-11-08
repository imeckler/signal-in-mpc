import ProtoParseWork.FullParserV3Work.ObservedIntervals
import ProtoParseWork.FullParserV3Work.FrozenRejection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 2000000

/-- Complete internal failure observation. EOF in a group retains raw ok255;
active decoder/field failure has raw ok0. Both retain exact suffix, error
constructor/parameters and full unmasked records. Live frames remain explicit. -/
structure RejectedObservation (bytes after : Slice U8) (error : prost.error.DecodeError)
    (result : State (BitVec 8) (BitVec 64)) (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) : Prop where
  complete : ProtoParse.completeMask Word64.concrete ByteAuth.concrete bytes.length result.parser = 0
  raw : result.parser.ok = 0 ∨ (result.parser.ok = 255 ∧ result.parser.depth ≠ 0)
  cursor : after = drop bytes result.parser.next.toNat
  cursor_bound : result.parser.next.toNat ≤ bytes.length
  fields_eq : result.parser.fields = fields
  error_eq : statusView (.Err error) = some result.error
  frames : ∃ tags, Frames result.parser.depth result.parser.stack tags

def RejectedScan (bytes : Slice U8) (position : Nat) (state : State (BitVec 8) (BitVec 64))
    (after : Slice U8) (error : prost.error.DecodeError) (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) :=
  RejectedObservation bytes after error (finish Word64.concrete ByteAuth.concrete (scan bytes position bytes.length state)) fields

theorem active_observation (bytes after : Slice U8) (error : prost.error.DecodeError)
    (before result : State (BitVec 8) (BitVec 64)) (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) (tags : List U32)
    (h : ActiveRejection bytes after error before result fields)
    (hf : Frames before.parser.depth before.parser.stack tags) : RejectedObservation bytes after error result fields := by
  refine ⟨?_,Or.inl h.raw_rejected,h.cursor,h.cursor_bound,h.fields_eq,h.error_eq,?e⟩
  · have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
    simp only [ProtoParse.completeMask,h.raw_rejected,hz]
  · exact ⟨tags,by rw [h.depth,h.stack]; exact hf⟩

theorem active_remaining_scan (bytes after : Slice U8) (position : Nat) (error : prost.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) (tags : List U32)
    (hp : position < bytes.length) (hf : Frames state.parser.depth state.parser.stack tags)
    (h : ∀ positions : List Nat, ActiveRejection bytes after error state
      (finish Word64.concrete ByteAuth.concrete (positions.foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes))
        (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes) state position))) fields) :
    RejectedScan bytes position state after error fields := by
  unfold RejectedScan scan
  have hn : bytes.length-position = (bytes.length-(position+1))+1 := by omega
  rw [hn,List.range'_succ,List.foldl_cons]
  exact active_observation bytes after error state _ fields tags (h _) hf

theorem rejected_fields_congr (bytes after : Slice U8) (error : prost.error.DecodeError)
    (result : State (BitVec 8) (BitVec 64)) (left right : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (he : left = right) (h : RejectedObservation bytes after error result left) :
    RejectedObservation bytes after error result right := he ▸ h

/-- A complete successful prefix may precede an error without changing its
metadata or replacing the failed record with successful output. -/
theorem rejected_scan_prefix (bytes after : Slice U8) (position middle : Nat)
    (state : State (BitVec 8) (BitVec 64)) (intermediate : ProtoParse.State (BitVec 8) (BitVec 64))
    (error : prost.error.DecodeError) (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (hp : position ≤ middle) (hb : middle ≤ bytes.length)
    (hs : state.parser.ok = 255) (hf : FieldMasks state.parser.fields)
    (he : scanOf bytes position middle state.parser = intermediate) (hok : intermediate.ok = 255)
    (hr : RejectedScan bytes middle ⟨intermediate,state.error⟩ after error fields) :
    RejectedScan bytes position state after error fields := by
  have hprefix := lift_successful_interval bytes position middle state intermediate hs hf he hok
  have hscan := scan_split bytes position middle bytes.length state hp hb
  rw [hprefix] at hscan
  unfold RejectedScan
  rw [hscan]
  exact hr

#print axioms active_observation
#print axioms active_remaining_scan
#print axioms rejected_scan_prefix
end FullParserV3.Observed
