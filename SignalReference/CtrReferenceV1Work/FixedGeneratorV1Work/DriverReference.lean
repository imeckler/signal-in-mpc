import CtrReferenceV1Work.FixedGeneratorV1Work.GeneratorReference
import CtrReferenceV1Work.StreamCounterReference
namespace LibSignalReference.Candidate.FixedCtr
open Aeneas Aeneas.Std
open LibSignalReference.Candidate
open LibSignalReference.Candidate.FixedDispatch
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def successor (counter : U32) : U32 := core.num.U32.wrapping_add counter (1#u32)
def after : Nat → U32 → U32
 | 0,counter => counter
 | n+1,counter => after n (successor counter)
def streamBlock (keys : Nat → Words (BitVec 64)) (counter : U32) : Array U8 16#usize :=
 blockOf (encrypted keys (embed (blockBytes (CtrState.expected counter))) 0)
def blocksValue (keys : Nat → Words (BitVec 64)) : Nat → U32 → List (Array U8 16#usize)
 | 0,_ => []
 | n+1,counter => streamBlock keys counter :: blocksValue keys n (successor counter)

/-- Authored bounded composition of actual selected gen_ks_block, retaining its owner continuation.
This is not yet an extraction of cipher's generic StreamCipherCore/ReadBuffer wrapper. -/
def runBlocks : Nat → FixedCtrGenerator.CtrBackend →
 Result (List (Array U8 16#usize) × FixedCtrGenerator.CtrBackend)
 | 0,state => .ok ([],state)
 | n+1,state => do
   let (updated,back,block) ← FixedCtrGenerator.CtrBackend.gen_ks_block state CtrState.zeroBlock
   let (blocks,last) ← runBlocks n (back updated)
   .ok (block::blocks,last)

theorem run_actual (n : Nat) (keys : Nat → Words (BitVec 64)) (counter : U32) :
 runBlocks n ⟨zeroNonce counter, ⟨AesKeyRanges.keyArray keys⟩⟩ =
 .ok (blocksValue keys n counter,
      ⟨zeroNonce (after n counter), ⟨AesKeyRanges.keyArray keys⟩⟩) := by
 induction n generalizing counter with
 | zero => rfl
 | succ n ih =>
   rw [runBlocks, generator_actual]
   simp only [uncurry_apply_pair, bind_tc_ok]
   rw [ih]
   rfl

theorem after_no_wrap (n : Nat) (counter : U32) (bound : counter.val + n ≤ 4294967295) :
 (after n counter).val = counter.val + n := by
 induction n generalizing counter with
 | zero => simp [after]
 | succ n ih =>
   have step := CtrState.increment_no_wrap counter (by omega)
   change (after n (successor counter)).val = _
   have step' : (successor counter).val = counter.val + 1 := step
   rw [ih _ (by rw [step']; omega), step']
   omega

theorem blocks_length (n : Nat) (keys : Nat → Words (BitVec 64)) (counter : U32) :
 (blocksValue keys n counter).length = n := by
 induction n generalizing counter with
 | zero => rfl
 | succ n ih => simp [blocksValue,ih]

/-- Same ceil count as checked_sub(...).div_ceil(16), including fully cached requests. -/
def requiredBlocks (bytes cached : Nat) : Nat := (bytes - cached + 15) / 16

theorem required_ceil (bytes cached : Nat) :
 requiredBlocks bytes cached =
 (bytes-cached)/16 + (if (bytes-cached)%16 = 0 then 0 else 1) := by
 unfold requiredBlocks
 split <;> omega

theorem cached_only (bytes cached : Nat) (bound : bytes ≤ cached) :
 requiredBlocks bytes cached = 0 := by simp [requiredBlocks, Nat.sub_eq_zero_of_le bound]

theorem exact_remaining_guard (counter : U32) (bytes cached : Nat) :
 requiredBlocks bytes cached ≤ 4294967295-counter.val ↔
 counter.val + requiredBlocks bytes cached ≤ 4294967295 := by
 have bound := counter.hmax
 simp only [UScalar.cMax, UScalarTy.U32_numBits_eq] at bound
 omega

theorem actual_remaining_authorizes (counter : U32) (bytes cached : Nat)
 (allowed : requiredBlocks bytes cached ≤ 4294967295-counter.val) :
 ∃ remaining, CtrStateV1.remaining (CtrState.zeroNonce counter) =
 .ok (CtrStateRemaining.SomeRemaining remaining) ∧
 requiredBlocks bytes cached ≤ remaining.val := by
 apply CtrStreamCounter.remaining_authorizes
 exact (exact_remaining_guard counter bytes cached).mp allowed

end LibSignalReference.Candidate.FixedCtr
