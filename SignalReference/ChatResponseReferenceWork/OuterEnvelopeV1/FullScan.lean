import ChatResponseReferenceWork.OuterEnvelopeV1.Consumption
import ChatResponseReferenceWork.InnerScanV1.DriverReference
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.OuterEnvelopeV1
open ActualInnerScanV1
noncomputable def driver : prost.message.Message Message := {
  encode_raw := fun _ _ _ => .fail .undef
  merge_field := fun inst state tag wire before ctx =>
    ActualOuterEnvelopeV1.merge_envelope (InnerScanV1.fieldBuf inst) state tag wire before ctx
  encoded_len := fun _ => .fail .undef
  merge := fun _ _ _ => .fail .undef
  clear := fun _ => .fail .undef }
noncomputable def ownedDriver : prost.message.Message Message :=
  {driver with merge := prost.message.Message.merge.default driver}
def defaults : core.default.Default Message := ⟨ActualOuterEnvelopeV1.default_envelope⟩
abbrev driverBuf := InnerScanV1.sliceBuf
noncomputable def actualDecode (before : Slice U8) :=
  owned_slice_replay.decode_buffer ownedDriver defaults driverBuf before

theorem driver_fields {B : Type} (inst : bytes.buf.buf_impl.Buf B) (state : Message)
    (tag : U32) (wire : prost.encoding.wire_type.WireType) (before : B) (ctx : prost.encoding.DecodeContext) :
    driver.merge_field inst state tag wire before ctx =
      fieldSpec (InnerScanV1.fieldBuf inst) state tag wire before ctx :=
  dispatcher_reference _ _ _ _ _ _

noncomputable def step (ctx : prost.encoding.DecodeContext) (state : Message) (before : Slice U8) :
    Result (ControlFlow (Message × Slice U8) (core.result.Result Unit Error × Message)) := do
  if 0 < before.length then
    let (key,middle) ← prost.encoding.decode_key driverBuf before
    match key with
    | .Err error => .ok (.done (.Err error,state))
    | .Ok (tag,wire) =>
      let (status,next,after) ← fieldSpec (InnerScanV1.fieldBuf driverBuf) state tag wire middle ctx
      match status with
      | .Err error => .ok (.done (.Err error,next))
      | .Ok _ => .ok (.cont (next,after))
  else .ok (.done (.Ok (),state))

theorem step_reference (ctx : prost.encoding.DecodeContext) (state : Message) (before : Slice U8) :
    prost.message.Message.merge.default_loop.body driver driverBuf ctx state before = step ctx state before := by
  by_cases nonempty : 0 < before.length
  · unfold prost.message.Message.merge.default_loop.body step
    rw [show driverBuf.has_remaining before = .ok true from by simp [driverBuf,InnerScanV1.sliceBuf,nonempty]]
    simp only [bind_tc_ok,if_true,nonempty]
    cases keyRun : prost.encoding.decode_key driverBuf before with
    | fail error => simp only [bind_tc_fail]
    | div => simp only [bind_tc_div]
    | ok pair =>
      rcases pair with ⟨key,middle⟩
      simp only [bind_tc_ok]
      cases key with
      | Err error => rfl
      | Ok pair =>
        rcases pair with ⟨tag,wire⟩
        dsimp! only
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,InnerScanV1.clone_ctx,driver_fields]
        cases fieldRun : fieldSpec (InnerScanV1.fieldBuf driverBuf) state tag wire middle ctx with
        | fail error => rfl
        | div => rfl
        | ok pair => rcases pair with ⟨status,next,after⟩; cases status <;> rfl
  · simp [prost.message.Message.merge.default_loop.body,step,driverBuf,InnerScanV1.sliceBuf,nonempty]

theorem step_decreases (ctx : prost.encoding.DecodeContext) (state next : Message) (before after : Slice U8)
    (continued : step ctx state before = .ok (.cont (next,after))) : after.length < before.length := by
  by_cases nonempty : 0 < before.length
  · obtain ⟨key,middle,keyRun,actualKey,bound,strict⟩ := InnerScanV1.key_total before
    cases key with
    | Err error => simp [step,nonempty,actualKey] at continued
    | Ok pair =>
      rcases pair with ⟨tag,wire⟩
      have keyStrict := strict (tag,wire) rfl
      simp only [step,if_pos nonempty,actualKey,bind_tc_ok] at continued
      dsimp! only at continued
      cases fieldRun : fieldSpec (InnerScanV1.fieldBuf driverBuf) state tag
          (ActualResponseBytesV1.fromSkipWire wire) middle ctx with
      | fail error => simp [fieldRun] at continued
      | div => simp [fieldRun] at continued
      | ok output =>
        rcases output with ⟨status,value,suffix⟩
        have sourceRun : ActualOuterEnvelopeV1.merge_envelope InnerResponseV1.sliceBuf state tag
            (ActualResponseBytesV1.fromSkipWire wire) middle ctx = .ok (status,value,suffix) := by
          rw [dispatcher_reference]; exact fieldRun
        have fieldBound := envelope_field_consumption state value tag
          (ActualResponseBytesV1.fromSkipWire wire) middle suffix ctx status sourceRun
        cases status with
        | Err error => simp [fieldRun] at continued
        | Ok unit =>
          simp [fieldRun] at continued
          rcases continued with ⟨rfl,rfl⟩
          exact fieldBound.trans_lt keyStrict
  · simp [step,nonempty] at continued

/-- Complete actual generated envelope scan, including nested requests/responses,
malformed fields/groups, duplicates, ordinary Err and outer fail/div. No finite
trace or primitive correctness/termination/response-validity premise. -/
theorem actual_outer_scan_finite (ctx : prost.encoding.DecodeContext) (state : Message) (before : Slice U8) :
    ∃ result,
      InnerScanV1.FiniteRun (fun pair : Message × Slice U8 => step ctx pair.1 pair.2) (state,before) result ∧
      prost.message.Message.merge.default_loop driver driverBuf state before ctx = result := by
  obtain ⟨result,run⟩ := InnerScanV1.finite_run_exists
    (fun pair : Message × Slice U8 => step ctx pair.1 pair.2)
    (fun pair => pair.2.length)
    (by intro old next step; exact step_decreases ctx old.1 next.1 old.2 next.2 step)
    (state,before)
  refine ⟨result,run,?_⟩
  unfold prost.message.Message.merge.default_loop
  have bodies : (fun pair : Message × Slice U8 => prost.message.Message.merge.default_loop.body driver driverBuf ctx pair.1 pair.2) =
      (fun pair : Message × Slice U8 => step ctx pair.1 pair.2) := by
    funext pair; exact step_reference ctx pair.1 pair.2
  rw [bodies]
  exact InnerScanV1.finite_run_actual run

/-- Owned decode erases only the error-local message. The exact error stack,
ordinary error, outer failure and divergence remain in the returned result. -/
theorem owned_decode_exact (before : Slice U8) : actualDecode before = (do
    let initial ← ActualOuterEnvelopeV1.default_envelope
    let (status,final) ← prost.message.Message.merge.default driver driverBuf initial before
    match status with
    | .Ok _ => .ok (.Ok final)
    | .Err error => .ok (.Err error)) := by
  unfold actualDecode owned_slice_replay.decode_buffer ownedDriver defaults
  cases hd : ActualOuterEnvelopeV1.default_envelope <;> try rfl
  rename_i initial
  simp only [bind_tc_ok]
  cases hm : prost.message.Message.merge.default driver driverBuf initial before <;> try rfl
  rename_i pair
  rcases pair with ⟨status,final⟩
  simp only [bind_tc_ok]
  cases status <;> rfl
def emptyEnvelope : Message := {type := none,request := none,response := none}
/-- Real constructor/default context and owned result projection, connected to a
finite actual full-envelope trace. Failed messages are never returned as success. -/
theorem actual_owned_decode_finite (before : Slice U8) :
    ∃ outcome,
      InnerScanV1.FiniteRun (fun pair : Message × Slice U8 => step ⟨100#u32⟩ pair.1 pair.2)
        (emptyEnvelope,before) outcome ∧
      actualDecode before = (do
        let (status,final) ← outcome
        match status with
        | .Ok _ => .ok (.Ok final)
        | .Err error => .ok (.Err error)) := by
  obtain ⟨outcome,run,actual⟩ := actual_outer_scan_finite ⟨100#u32⟩ emptyEnvelope before
  refine ⟨outcome,run,?_⟩
  rw [owned_decode_exact,default_exact]
  simp only [bind_tc_ok]
  unfold prost.message.Message.merge.default
  rw [show prost.encoding.DecodeContext.Insts.CoreDefaultDefault.default = .ok ⟨100#u32⟩ from by
    unfold prost.encoding.DecodeContext.Insts.CoreDefaultDefault.default prost.RECURSION_LIMIT
    rfl]
  simp only [bind_tc_ok]
  unfold emptyEnvelope at actual
  rw [actual]
  rfl
#print axioms actual_owned_decode_finite
#print axioms driver_fields
#print axioms step_reference
#print axioms actual_outer_scan_finite
#print axioms owned_decode_exact
end ChatResponseReference.OuterEnvelopeV1
