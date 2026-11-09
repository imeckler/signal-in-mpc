import CtrReferenceV1Work.FixedGeneratorV1Work.BufferedReference
namespace LibSignalReference.Candidate.FixedCtr
open Aeneas Aeneas.Std TlsMpc
open _root_.Std.Tactic.BVDecide
open LibSignalReference.Candidate
open LibSignalReference.Candidate.FixedDispatch
open LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- Counter is the public deterministic stream-block index; the key/plaintext remain symbolic.
No secret counter is reconstructed by this reference or by its backend-neutral expression. -/
def streamExpression (keys : Nat → Words (BVExpr 64)) (counter : U32) : List (BVExpr 8) :=
 expression16 ⟨0,by decide⟩ keys
  (singleInput (fun byte => .const (blockBytes (CtrState.expected counter) byte)))

theorem stream_expression_correct (keys : Nat → Words (BVExpr 64)) (counter : U32)
 (assign : BVExpr.Assignment) :
 (streamExpression keys counter).map (BVExpr.eval assign) =
 (streamBlock (fun r => mapWords (BVExpr.eval assign) (keys r)) counter).val.map UScalar.bv := by
 have h := expression16_correct ⟨0,by decide⟩ keys
  (singleInput (fun byte => .const (blockBytes (CtrState.expected counter) byte))) assign
 have hin : (fun b i =>
  (singleInput (fun byte => BVExpr.const (blockBytes (CtrState.expected counter) byte)) b i).eval assign) =
  embed (blockBytes (CtrState.expected counter)) := by
  funext b i
  simp only [singleInput,embed]
  split <;> rfl
 rw [hin] at h
 simpa only [streamExpression, streamBlock, blockOf, List.map_map, Function.comp_def,
  UScalar.bv,encrypted] using h

def keystreamExpression (keys : Nat → Words (BVExpr 64)) : Nat → U32 → List (BVExpr 8)
 | 0,_ => []
 | n+1,counter => streamExpression keys counter ++ keystreamExpression keys n (successor counter)

theorem keystream_expression_correct (keys : Nat → Words (BVExpr 64)) (n : Nat)
 (counter : U32) (assign : BVExpr.Assignment) :
 (keystreamExpression keys n counter).map (BVExpr.eval assign) =
 bytesOfBlocks (blocksValue (fun r => mapWords (BVExpr.eval assign) (keys r)) n counter) := by
 induction n generalizing counter with
 | zero => rfl
 | succ n ih =>
   simp only [keystreamExpression, List.map_append,stream_expression_correct,ih,
    blocksValue,bytesOfBlocks,List.flatMap_cons]

def xorExpression (input stream : List (BVExpr 8)) : List (BVExpr 8) :=
 List.zipWith (fun a b => BvConstruct.bin a .xor b) input stream

theorem xor_expression_correct (input stream : List (BVExpr 8)) (assign : BVExpr.Assignment) :
 (xorExpression input stream).map (BVExpr.eval assign) =
 xorBytes (input.map (BVExpr.eval assign)) (stream.map (BVExpr.eval assign)) := by
 simp only [xorExpression,xorBytes,List.map_zipWith,List.zipWith_map,BvConstruct.eval_bin,BVExpr.eval_bin,BVBinOp.eval]

/-- One shared computed key schedule, one reduced block core per public capacity block. -/
def freshExpression (key : Nat → BVExpr 8) (input : List (BVExpr 8)) : List (BVExpr 8) :=
 xorExpression input (keystreamExpression (keyGroupsExpression key) ((input.length+15)/16) (0#u32))

theorem fresh_expression_correct (key : Nat → BVExpr 8) (input : List (BVExpr 8))
 (assign : BVExpr.Assignment) :
 (freshExpression key input).map (BVExpr.eval assign) =
 xorBytes (input.map (BVExpr.eval assign))
  (bytesOfBlocks (blocksValue (groupAt 0 (scheduleValue (fun i => (key i).eval assign)))
   ((input.length+15)/16) (0#u32))) := by
 have hk : (fun r => mapWords (BVExpr.eval assign) (keyGroupsExpression key r)) =
  groupAt 0 (scheduleValue (fun i => (key i).eval assign)) := by
  funext r
  exact keyGroupsExpression_correct key assign r
 simp only [freshExpression,xor_expression_correct,keystream_expression_correct,hk]

def freshState : BufferState := ⟨0#u32,[]⟩

theorem fresh_buffered_correct (key : Nat → BVExpr 8) (input : List (BVExpr 8))
 (assign : BVExpr.Assignment) (old : List (BitVec 8))
 (same : input.length = old.length) (bounded : input.length ≤ 8192) :
 (freshExpression key input).map (BVExpr.eval assign) =
 (buffered (groupAt 0 (scheduleValue (fun i => (key i).eval assign))) freshState
  (input.map (BVExpr.eval assign)) old).output := by
 have allowed : requiredBlocks (input.map (BVExpr.eval assign)).length freshState.unread.length ≤
  4294967295-freshState.counter.val := by
  have hz : freshState.counter.val = 0 := by decide
  rw [hz]
  simpa only [List.length_map, freshState, requiredBlocks, List.length_nil,
   Nat.sub_zero] using
   CtrStreamCounter.sealed_sender_profile_bound input.length bounded
 rw [buffered_success _ _ _ old (by simpa using same) allowed]
 simpa only [freshState,requiredBlocks,List.length_map,List.length_nil,Nat.sub_zero,
  List.nil_append] using fresh_expression_correct key input assign

theorem compiled_fresh_buffered (key : Nat → BVExpr 8) (input : List (BVExpr 8))
 (assign : BVExpr.Assignment) (old : List (BitVec 8))
 (same : input.length = old.length) (bounded : input.length ≤ 8192)
 (index : Nat) (hi : index < 8*(freshExpression key input).length) :
 AigExport.evalRef
  (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (freshExpression key input))).aig)
  (fun varId bit => (assign.get varId).bv.getLsbD bit)
  (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (freshExpression key input))).vec.get index hi)) =
 (ByteCircuit.joinValue
  (buffered (groupAt 0 (scheduleValue (fun i => (key i).eval assign))) freshState
   (input.map (BVExpr.eval assign)) old).output).getLsbD index := by
 rw [ByteCircuit.compile_bytes_correct, fresh_buffered_correct key input assign old same bounded]

/-- The compiled XOR is fed by an actual-key-schedule, actual counter/AES generator trace.
The recursive driver is authored; full generic Rust buffer/parallel-dispatch linkage is not claimed. -/
theorem compiled_fresh_actual_driver (key : Nat → BVExpr 8) (input : List (BVExpr 8))
 (assign : BVExpr.Assignment) (bounded : input.length ≤ 8192) :
 ∃ schedule blocks last,
  RustCryptoAesKeySchedule.soft.fixslice.aes256_key_schedule
   (AesKeySchedule.keyArray (fun i => (⟨(key i).eval assign⟩ : U8))) = .ok schedule ∧
  runBlocks ((input.length+15)/16) ⟨zeroNonce (0#u32),⟨schedule⟩⟩ = .ok (blocks,last) ∧
  (∃ remaining, CtrStateV1.remaining (CtrState.zeroNonce (0#u32)) =
   .ok (CtrStateRemaining.SomeRemaining remaining) ∧ (input.length+15)/16 ≤ remaining.val) ∧
  ∀ (index : Nat) (hi : index < 8*(freshExpression key input).length),
   AigExport.evalRef
    (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (freshExpression key input))).aig)
    (fun varId bit => (assign.get varId).bv.getLsbD bit)
    (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (freshExpression key input))).vec.get index hi)) =
   (ByteCircuit.joinValue (xorBytes (input.map (BVExpr.eval assign)) (bytesOfBlocks blocks))).getLsbD index := by
 obtain ⟨schedule,hkey,hkeys⟩ := actual_schedule (fun i => (key i).eval assign)
 let keys := groupAt 0 (scheduleValue (fun i => (key i).eval assign))
 refine ⟨schedule,blocksValue keys ((input.length+15)/16) (0#u32),
  ⟨zeroNonce (after ((input.length+15)/16) (0#u32)),⟨AesKeyRanges.keyArray keys⟩⟩,hkey,?_,?_,?_⟩
 · rw [hkeys]
   exact run_actual _ _ _
 · apply CtrStreamCounter.remaining_authorizes
   have hz : (0#u32).val = 0 := by decide
   rw [hz,Nat.zero_add]
   exact CtrStreamCounter.sealed_sender_profile_bound _ bounded
 · intro index hi
   rw [ByteCircuit.compile_bytes_correct,fresh_expression_correct]

end LibSignalReference.Candidate.FixedCtr
