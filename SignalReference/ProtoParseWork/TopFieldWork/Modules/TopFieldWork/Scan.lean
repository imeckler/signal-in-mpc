import TopFieldWork.Table

namespace LibSignalReference.Candidate.ProstTopField
open TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstSkipKey LibSignalReference.Candidate.ProstSkipPlan
set_option maxHeartbeats 500000

theorem write_stack_zero (index tag : BitVec 64) (stack : List (BitVec 64)) :
    ProtoParse.writeStack Word64.concrete ByteAuth.concrete 0 index tag stack = stack := by
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [ProtoParse.writeStack,hz,Word64.select_reject]
  exact List.zipIdx_map_fst 0 stack

/-- Public scan positions inside a previously consumed field have no effect,
regardless of the speculative decoder and field plan at that byte. -/
theorem apply_inactive (position : Nat)
    (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hn : state.next ≠ BitVec.ofNat 64 position) :
    ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state = state := by
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.next (Word64.concrete.const position) = 0 := by
    rw [word_eq_value]; exact if_neg hn
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have hz' (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  simp only [ProtoParse.applyPlan,hh,hz,hz',Word64.select_reject,write_stack_zero,write_fields_zero]
  cases state
  simp [ByteAuth.concrete]
  exact BitVec.and_allOnes

/-- Failure is absorbing: all later public scan positions preserve the rejected
state, including secret offsets, stack and field metadata. -/
theorem apply_failed (position : Nat)
    (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hs : state.ok = 0) :
    ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state = state := by
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [ProtoParse.applyPlan,hs,hz,Word64.select_reject,write_stack_zero,write_fields_zero]
  cases state
  simp_all

theorem step_inactive (capacity position : Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hn : state.next ≠ BitVec.ofNat 64 position) :
    ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows state position = state := by
  exact apply_inactive position _ state hn

theorem step_failed (capacity position : Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hs : state.ok = 0) :
    ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows state position = state := by
  exact apply_failed position _ state hs

theorem scan_inactive (capacity : Nat) (positions : List Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hn : ∀ p ∈ positions, state.next ≠ BitVec.ofNat 64 p) :
    positions.foldl (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows) state = state := by
  induction positions with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons,step_inactive capacity p rows state (hn p (by simp))]
    exact ih (by intro p hp; exact hn p (by simp [hp]))

theorem scan_failed (capacity : Nat) (positions : List Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hs : state.ok = 0) :
    positions.foldl (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows) state = state := by
  induction positions with
  | nil => rfl
  | cons p ps ih => simpa only [List.foldl_cons,step_failed capacity p rows state hs] using ih

/-- Only an encountered failed plan poisons the parser; speculative errors at
other offsets are covered by apply_inactive above. -/
theorem apply_reject (position : Nat)
    (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hn : state.next = BitVec.ofNat 64 position) (hp : p.ok = 0) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).ok = 0 := by
  simp only [ProtoParse.applyPlan,word_eq_value]
  simp_all [Word64.concrete,ByteAuth.concrete]

#print axioms write_stack_zero
#print axioms apply_inactive
#print axioms apply_failed
#print axioms step_inactive
#print axioms step_failed
#print axioms scan_inactive
#print axioms scan_failed
#print axioms apply_reject
end LibSignalReference.Candidate.ProstTopField
