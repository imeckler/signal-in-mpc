import ProtoParseWork.FullParserV3Work.ObservedScan
import ProtoParseWork.FullParserV3Work.ScanState
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
set_option maxHeartbeats 2000000

def scan (bytes : Slice U8) (start finish : Nat) (state : State (BitVec 8) (BitVec 64)) :=
  (List.range' start (finish-start)).foldl (step Word64.concrete ByteAuth.concrete bytes.length (rowsOf bytes)) state

theorem scan_split (bytes : Slice U8) (start middle finish : Nat)
    (state : State (BitVec 8) (BitVec 64)) (h1 : start ≤ middle) (h2 : middle ≤ finish) :
    scan bytes start finish state = scan bytes middle finish (scan bytes start middle state) := by
  unfold scan
  have hn : finish-start = (middle-start)+(finish-middle) := by omega
  rw [hn,←List.range'_append,List.foldl_append]
  simp only [Nat.one_mul]
  have hi : start+(middle-start) = middle := by omega
  rw [hi]

/-- Lift any proved successful complete numeric interval, retaining the exact
error metadata already present. The production parser is the first projection. -/
theorem lift_successful_interval (bytes : Slice U8) (start finish : Nat)
    (state : State (BitVec 8) (BitVec 64)) (result : ProtoParse.State (BitVec 8) (BitVec 64))
    (hs : state.parser.ok = 255) (hf : FieldMasks state.parser.fields)
    (he : scanOf bytes start finish state.parser = result) (hok : result.ok = 255) :
    scan bytes start finish state = ⟨result,state.error⟩ := by
  have hp := fold_erasure bytes.length (List.range' start (finish-start)) (rowsOf bytes) state
  have herr := successful_fold_error bytes.length (List.range' start (finish-start)) (rowsOf bytes) state
    (table_masks bytes) hs hf (by change (scanOf bytes start finish state.parser).ok = 255; rw [he]; exact hok)
  have hparser : (scan bytes start finish state).parser = result := hp.trans he
  have herror : (scan bytes start finish state).error = state.error := herr
  generalize scan bytes start finish state = output at *
  cases output
  cases hparser
  cases herror
  rfl

#print axioms scan_split
#print axioms lift_successful_interval
end FullParserV3.Observed
