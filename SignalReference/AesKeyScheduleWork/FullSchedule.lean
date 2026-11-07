import AesKeyScheduleWork.Initialization
import AesKeyScheduleWork.ExpansionLoop
import AesKeyScheduleFinishWork.Finish

namespace LibSignalReference.Candidate.AesKeySchedule

open Aeneas Aeneas.Std TlsMpc
open RustCryptoAesKeySchedule
open _root_.Std.Tactic.BVDecide

set_option maxHeartbeats 200000
set_option maxRecDepth 100000

def factoredSchedule (key : Array U8 32#usize) : Result (Array U64 120#usize) := do
  let initial ← initialState key
  let expanded ← soft.fixslice.aes256_key_schedule_loop0 initial 8#usize 0#usize
  AesKeyScheduleFinish.finishActual expanded

theorem factoredSchedule_eq (key : Array U8 32#usize) :
    soft.fixslice.aes256_key_schedule key = factoredSchedule key := by
  with_unfolding_all simp [soft.fixslice.aes256_key_schedule, factoredSchedule,
    initialState, AesKeyScheduleFinish.finishActual, bind_tc_ok]

/- Keep the proof-only factor folded while inferring its postcondition.
Explicit unfolding still proves its exact generated-code composition above. -/
attribute [local irreducible] initialState

theorem key_schedule_spec (key : Nat → U8) :
    ∃ result, soft.fixslice.aes256_key_schedule (keyArray key) = .ok result ∧
      result.val.map UScalar.bv = Signal.AesKeySchedule.scheduleCore Signal.AesKeySchedule.concrete
        (Signal.AesKeySchedule.initialWords (fun i => (key i).bv) 0)
        (Signal.AesKeySchedule.initialWords (fun i => (key i).bv) 16) := by
  have hinit := initialState_spec key
  generalize hcall : initialState (keyArray key) = initialOutcome at hinit
  obtain ⟨initial, hi', hvi⟩ := WP.spec_imp_exists (m := initialOutcome) hinit
  have hi : initialState (keyArray key) = .ok initial := hcall.trans hi' 
  obtain ⟨expanded, he, hve⟩ := expansion_loop initial 8#usize 0#usize (by decide) (by decide)
  obtain ⟨result, hf, hvf⟩ := AesKeyScheduleFinish.finishActual_spec expanded
  refine ⟨result, ?_, ?_⟩
  · rw [factoredSchedule_eq]
    simp [factoredSchedule, hi, he, hf]
  · rw [hvf, hve, hvi]
    simp [Signal.AesKeySchedule.scheduleCore, initialWords_network, Signal.AesLayout.Words.list]
    rfl

theorem key_schedule_all_arrays (key : Array U8 32#usize) :
    ∃ result, soft.fixslice.aes256_key_schedule key = .ok result ∧
      result.val.map UScalar.bv = Signal.AesKeySchedule.scheduleCore Signal.AesKeySchedule.concrete
        (Signal.AesKeySchedule.initialWords (fun i => (key.val[i]?.getD 0#u8).bv) 0)
        (Signal.AesKeySchedule.initialWords (fun i => (key.val[i]?.getD 0#u8).bv) 16) := by
  simpa only [keyArray_all] using key_schedule_spec (fun i => key.val[i]?.getD 0#u8)

/-- Complete actual portable AES256 key expansion versus its numeric circuit.
All 256 input key bits and all 7680 output schedule bits remain secret. -/
theorem key_schedule_refines_artifact (secret : Nat → BVExpr 8) (assign : BVExpr.Assignment) :
    ∃ result,
      soft.fixslice.aes256_key_schedule (keyArray (fun i => ⟨(secret i).eval assign⟩)) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (Signal.AesKeySchedule.keyExpr secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile
            (ByteCircuit.joinExpr (Signal.AesKeySchedule.keyExpr secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile
            (ByteCircuit.joinExpr (Signal.AesKeySchedule.keyExpr secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (Signal.AesKeyCopy.encode (result.val.map UScalar.bv))).getLsbD index := by
  obtain ⟨result, hr, hv⟩ := key_schedule_spec (fun i => ⟨(secret i).eval assign⟩)
  refine ⟨result, hr, ?_⟩
  intro index hi
  rw [Signal.AesKeySchedule.compiled_keyExpr_correct, hv]
  rfl

end LibSignalReference.Candidate.AesKeySchedule
