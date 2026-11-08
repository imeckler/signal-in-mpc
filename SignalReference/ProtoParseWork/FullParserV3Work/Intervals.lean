import ProtoParseWork.FullParserV3Work.SuccessScan
open TlsMpc TlsMpc.Signal
namespace FullParserV3
set_option maxHeartbeats 1000000

/-- Absolute bounded cursors cannot alias earlier public scan positions. -/
theorem cursor_not_earlier (cursor position capacity : Nat)
    (hp : position < cursor) (hc : cursor ≤ capacity) (hcap : capacity ≤ 512) :
    BitVec.ofNat 64 cursor ≠ BitVec.ofNat 64 position := by
  intro h
  have he := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : cursor < 2^64),
    Nat.mod_eq_of_lt (by omega : position < 2^64)] at he
  omega

theorem scan_before_cursor (capacity start cursor : Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hnext : state.next = BitVec.ofNat 64 cursor) (hs : start ≤ cursor)
    (hc : cursor ≤ capacity) (hcap : capacity ≤ 512) :
    (List.range' start (cursor-start)).foldl
      (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows) state = state := by
  apply scan_inactive
  intro position hp
  rw [List.mem_range'] at hp
  rw [hnext]
  exact cursor_not_earlier cursor position capacity (by omega) hc hcap

/-- One actual successful field transition accounts for its entire public scan
interval; speculative decodes inside consumed payloads cannot mutate fields. -/
theorem scan_step_interval (capacity position cursor : Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (before after : ProtoParse.State (BitVec 8) (BitVec 64))
    (hstep : ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows before position = after)
    (hnext : after.next = BitVec.ofNat 64 cursor) (hp : position < cursor)
    (hc : cursor ≤ capacity) (hcap : capacity ≤ 512) :
    (List.range' position (cursor-position)).foldl
      (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows) before = after := by
  have he : cursor-position = (cursor-(position+1))+1 := by omega
  rw [he,List.range'_succ,List.foldl_cons,hstep]
  exact scan_before_cursor capacity (position+1) cursor rows after hnext (by omega) hc hcap

/-- Interval concatenation used by field and nested-group induction. -/
theorem scan_split (capacity start middle finish : Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (h1 : start ≤ middle) (h2 : middle ≤ finish) :
    (List.range' start (finish-start)).foldl (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows) state =
      (List.range' middle (finish-middle)).foldl (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows)
        ((List.range' start (middle-start)).foldl (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows) state) := by
  have hn : finish-start = (middle-start)+(finish-middle) := by omega
  rw [hn,←List.range'_append,List.foldl_append]
  simp only [Nat.one_mul]
  have hi : start+(middle-start) = middle := by omega
  rw [hi]

#print axioms scan_before_cursor
#print axioms scan_step_interval
#print axioms scan_split
end FullParserV3
