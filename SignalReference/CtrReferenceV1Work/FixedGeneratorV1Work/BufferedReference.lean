import CtrReferenceV1Work.FixedGeneratorV1Work.DriverReference
namespace LibSignalReference.Candidate.FixedCtr
open Aeneas Aeneas.Std
open LibSignalReference.Candidate
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- Logical unread suffix only. Actual ReadBuffer stores its cursor in consumed byte0;
that physical representation/borrow library relation is an explicit remaining boundary. -/
structure BufferState where
 counter : U32
 unread : List (BitVec 8)

def bytesOfBlocks (blocks : List (Array U8 16#usize)) : List (BitVec 8) :=
 blocks.flatMap (fun block => block.val.map UScalar.bv)

theorem stream_bytes_length (keys : Nat → Words (BitVec 64)) (n : Nat) (counter : U32) :
 (bytesOfBlocks (blocksValue keys n counter)).length = 16*n := by
 induction n generalizing counter with
 | zero => rfl
 | succ n ih =>
   simp only [blocksValue, bytesOfBlocks, List.flatMap_cons, List.length_append,
    List.length_map, streamBlock, FixedDispatch.blockOf, Subtype.coe_mk, List.length_map,
    List.length_range]
   change 16 + (bytesOfBlocks (blocksValue keys n (successor counter))).length = _
   rw [ih]
   omega

def xorBytes (input stream : List (BitVec 8)) : List (BitVec 8) :=
 List.zipWith (· ^^^ ·) input stream

structure ApplyResult where
 accepted : Bool
 output : List (BitVec 8)
 state : BufferState

/-- Functional buffer/content composition, with preflight failure before any generator call.
Full Rust StreamCipherCoreWrapper/parallel batching dispatch linkage remains separate. -/
def buffered (keys : Nat → Words (BitVec 64)) (state : BufferState)
 (input old : List (BitVec 8)) : ApplyResult :=
 let n := requiredBlocks input.length state.unread.length
 if input.length != old.length || 4294967295-state.counter.val < n then
  ⟨false,old,state⟩
 else
  let stream := state.unread ++ bytesOfBlocks (blocksValue keys n state.counter)
  ⟨true, xorBytes input stream,
   ⟨after n state.counter, stream.drop input.length⟩⟩

theorem length_reject (keys : Nat → Words (BitVec 64)) (state : BufferState)
 (input old : List (BitVec 8)) (different : input.length ≠ old.length) :
 buffered keys state input old = ⟨false,old,state⟩ := by
 simp [buffered, different]

theorem exhausted_reject (keys : Nat → Words (BitVec 64)) (state : BufferState)
 (input old : List (BitVec 8))
 (exhausted : 4294967295-state.counter.val < requiredBlocks input.length state.unread.length) :
 buffered keys state input old = ⟨false,old,state⟩ := by simp [buffered, exhausted]

theorem buffered_success (keys : Nat → Words (BitVec 64)) (state : BufferState)
 (input old : List (BitVec 8)) (same : input.length = old.length)
 (allowed : requiredBlocks input.length state.unread.length ≤ 4294967295-state.counter.val) :
 buffered keys state input old =
 let stream := state.unread ++ bytesOfBlocks
  (blocksValue keys (requiredBlocks input.length state.unread.length) state.counter)
 ⟨true,xorBytes input stream,
  ⟨after (requiredBlocks input.length state.unread.length) state.counter,
   stream.drop input.length⟩⟩ := by
 simp [buffered, same, Nat.not_lt_of_ge allowed]
 simpa only [same] using allowed

theorem cache_arithmetic (bytes cached : Nat) (bounded : cached < 16) :
 bytes ≤ cached + 16*requiredBlocks bytes cached ∧
 cached + 16*requiredBlocks bytes cached - bytes < 16 := by
 unfold requiredBlocks
 omega

theorem success_lengths (keys : Nat → Words (BitVec 64)) (state : BufferState)
 (input old : List (BitVec 8)) (cache : state.unread.length < 16)
 (same : input.length = old.length)
 (allowed : requiredBlocks input.length state.unread.length ≤ 4294967295-state.counter.val) :
 (buffered keys state input old).output.length = input.length ∧
 (buffered keys state input old).state.unread.length < 16 := by
 rw [buffered_success keys state input old same allowed]
 have h := cache_arithmetic input.length state.unread.length cache
 simp only [xorBytes, List.length_zipWith, List.length_append, stream_bytes_length,
  List.length_drop]
 constructor <;> omega

theorem success_counter (keys : Nat → Words (BitVec 64)) (state : BufferState)
 (input old : List (BitVec 8)) (same : input.length = old.length)
 (allowed : requiredBlocks input.length state.unread.length ≤ 4294967295-state.counter.val) :
 (buffered keys state input old).state.counter.val =
 state.counter.val + requiredBlocks input.length state.unread.length := by
 rw [buffered_success keys state input old same allowed]
 exact after_no_wrap _ _ ((exact_remaining_guard _ _ _).mp allowed)

end LibSignalReference.Candidate.FixedCtr
