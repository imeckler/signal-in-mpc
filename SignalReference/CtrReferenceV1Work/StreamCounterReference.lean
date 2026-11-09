import CtrReferenceV1Work.StateCircuitAgreement
import CtrReferenceV1Work.StateInitReference
import CtrReferenceV1Work.StateRemainingReference
namespace LibSignalReference.Candidate.CtrStreamCounter
open Aeneas Aeneas.Std
open LibSignalReference.Candidate.CtrState
/-- Authored composition of repeated unchanged actual next_block calls.
This is not the Rust StreamCipherCore/AES wrapper extraction. -/
def runCounters : Nat → Nonce → Result (List Block × Nonce)
 | 0,state => .ok ([],state)
 | n+1,state => do
   let (block,next) ← _root_.CtrStateV1.next state
   let (blocks,last) ← runCounters n next
   .ok (block::blocks,last)

theorem run_counters (n : Nat) (counter : U32)
 (bound : counter.val+n≤4294967295) :
 ∃ blocks last, runCounters n (zeroNonce counter) = .ok (blocks,zeroNonce last) ∧
   blocks.map (fun block => block.val.map UScalar.bv) =
     (List.range' counter.val n).map (TlsMpc.Signal.SealedSenderV1.counter TlsMpc.Aes.concrete) ∧
   last.val=counter.val+n := by
 induction n generalizing counter with
 | zero =>
   refine ⟨[],counter,rfl,?_,?_⟩ <;> simp
 | succ n ih =>
   have nextval := increment_no_wrap counter (by omega)
   obtain ⟨blocks,last,hr,hblocks,hlast⟩ := ih (core.num.U32.wrapping_add counter (1#u32)) (by rw [nextval];omega)
   refine ⟨expected counter::blocks,last,?_,?_,?_⟩
   · rw [runCounters, actual_next_zero_nonce]
     change (do
       let result ← runCounters n (zeroNonce (core.num.U32.wrapping_add counter (1#u32)))
       .ok (expected counter::result.1,result.2)) = .ok (expected counter::blocks,zeroNonce last)
     rw [hr]
     rfl
   · simp only [List.map_cons, counter_circuit, List.range'_succ]
     rw [hblocks,nextval]
   · rw [nextval] at hlast
     omega

/-- The actual remaining body authorizes the entire no-wrap driver domain.
Its typed Std Result::ok success-path boundary remains explicit. -/
theorem remaining_authorizes (n : Nat) (counter : U32)
 (bound : counter.val+n≤4294967295) :
 ∃ remaining, _root_.CtrStateV1.remaining (zeroNonce counter) =
   .ok (LibSignalReference.Candidate.CtrStateRemaining.SomeRemaining remaining) ∧ n≤remaining.val := by
 exact LibSignalReference.Candidate.CtrStateRemaining.supported_blocks (zeroNonce counter) n bound

theorem sealed_sender_profile_bound (bytes : Nat) (bound : bytes≤8192) :
  (bytes+15)/16≤4294967295 := by omega
end LibSignalReference.Candidate.CtrStreamCounter
