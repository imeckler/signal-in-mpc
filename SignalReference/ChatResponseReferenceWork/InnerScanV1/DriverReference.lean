import ChatResponseReferenceWork.InnerScanV1.Replayed.Funs
import ChatResponseReferenceWork.InnerResponseV1.DispatcherReference
import ProtoParseWork.FullParserV3Work.SkipTotality
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerScanV1
open ActualInnerScanV1
abbrev Message := InnerResponseV1.Message
def fieldBuf {B : Type} (inst : bytes.buf.buf_impl.Buf B) :
    ActualInnerResponseV1.bytes.buf.buf_impl.Buf B :=
  ⟨inst.remaining,inst.chunk,inst.advance⟩
/-- Only the actual generated field dispatcher is installed. Unused trait
operations fail closed; the default merge never calls them. -/
noncomputable def schema : prost.message.Message Message := {
  encode_raw := fun _ _ _ => .fail .undef
  merge_field := fun inst state tag wire before ctx =>
    ActualInnerResponseV1.merge_response (fieldBuf inst) state tag wire before ctx
  encoded_len := fun _ => .fail .undef
  merge := fun _ _ _ => .fail .undef
  clear := fun _ => .fail .undef }
noncomputable def ownedSchema : prost.message.Message Message :=
  {schema with merge := prost.message.Message.merge.default schema}
def defaults : core.default.Default Message :=
  ⟨ActualInnerResponseV1.default_response⟩
def sliceBuf : bytes.buf.buf_impl.Buf (Slice U8) := {
  remaining := LibSignalReference.Candidate.ProstSkipBuf.remaining
  chunk := LibSignalReference.Candidate.ProstSkipBuf.chunk
  advance := LibSignalReference.Candidate.ProstSkipBuf.advance
  has_remaining := fun bytes => .ok (0 < bytes.length) }
theorem slice_adapter : toSkipBuf sliceBuf =
    LibSignalReference.Candidate.ProstSkipBuf.sliceBuf := rfl
theorem key_total (before : Slice U8) :
    ∃ result after,
      LoopSupportSkip.encoding.decode_key
        LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (result,after) ∧
      prost.encoding.decode_key sliceBuf before = .ok
        ((match result with
          | .Ok (tag,wire) => .Ok (tag,ActualResponseBytesV1.fromSkipWire wire)
          | .Err error => .Err (ActualResponseBytesV1.fromSkipError error)),after) ∧
      after.length ≤ before.length ∧
      (∀ pair, result = .Ok pair → after.length < before.length) := by
  obtain ⟨result,after,hkey,hle,hstrict⟩ := FullParserV3.key_total before
  refine ⟨result,after,hkey,?_,hle,hstrict⟩
  unfold prost.encoding.decode_key
  rw [slice_adapter,hkey]
  cases result <;> rfl
theorem actual_fields {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (state : Message) (tag : U32) (wire : prost.encoding.wire_type.WireType)
    (before : B) (ctx : prost.encoding.DecodeContext) :
    schema.merge_field inst state tag wire before ctx =
      InnerResponseV1.fieldSpec (fieldBuf inst) state tag wire before ctx :=
  InnerResponseV1.dispatcher_reference _ _ _ _ _ _
/-- Owned decode discards only the failed message value. It preserves the exact
error (including diagnostic stack), outer failure and divergence. -/
theorem owned_decode (before : Slice U8) :
    owned_slice_replay.decode_buffer ownedSchema defaults sliceBuf before = (do
      let initial ← ActualInnerResponseV1.default_response
      let (r,final) ← prost.message.Message.merge.default schema sliceBuf initial before
      match r with
      | .Ok _ => .ok (.Ok final)
      | .Err error => .ok (.Err error)) := by
  unfold owned_slice_replay.decode_buffer ownedSchema defaults
  cases hd : ActualInnerResponseV1.default_response <;> try rfl
  rename_i initial
  simp only [bind_tc_ok]
  cases hm : prost.message.Message.merge.default schema sliceBuf initial before <;> try rfl
  rename_i pair
  rcases pair with ⟨r,final⟩
  simp only [bind_tc_ok]
  cases r <;> rfl
inductive MergeTrace (ctx : ActualInnerScanV1.prost.encoding.DecodeContext) : Message → Slice U8 → (core.result.Result Unit prost.error.DecodeError × Message × Slice U8) → Prop where
  | empty (message before) (h : before.length = 0) :
      MergeTrace ctx message before (.Ok (),message,before)
  | keyError {message before after error} (hn : 0 < before.length)
      (hk : ActualInnerScanV1.prost.encoding.decode_key sliceBuf before = ok (.Err error,after)) :
      MergeTrace ctx message before (.Err error,message,after)
  | fieldError {message before middle after error next tag wire} (hn : 0 < before.length)
      (hk : ActualInnerScanV1.prost.encoding.decode_key sliceBuf before = ok (.Ok (tag,wire),middle))
      (hm : schema.merge_field sliceBuf
        message tag wire middle ctx = ok (.Err error,next,after)) :
      MergeTrace ctx message before (.Err error,next,after)
  | next {message before middle after next tag wire result} (hn : 0 < before.length)
      (hk : ActualInnerScanV1.prost.encoding.decode_key sliceBuf before = ok (.Ok (tag,wire),middle))
      (hm : schema.merge_field sliceBuf
        message tag wire middle ctx = ok (.Ok (),next,after))
      (rest : MergeTrace ctx next after result) : MergeTrace ctx message before result

theorem clone_ctx (ctx : ActualInnerScanV1.prost.encoding.DecodeContext) :
    ActualInnerScanV1.prost.encoding.DecodeContext.Insts.CoreCloneClone.clone ctx = ok ctx := by
  cases ctx
  rfl

theorem loop_body_empty (ctx : ActualInnerScanV1.prost.encoding.DecodeContext) (message : Message) (before : Slice U8)
    (hn : before.length = 0) :
    ActualInnerScanV1.prost.message.Message.merge.default_loop.body schema sliceBuf ctx message before =
      ok (.done (.Ok (),message)) := by
  simp [ActualInnerScanV1.prost.message.Message.merge.default_loop.body,sliceBuf,hn]

theorem loop_body_key_error (ctx : ActualInnerScanV1.prost.encoding.DecodeContext) (message : Message) (before after : Slice U8)
    (error : prost.error.DecodeError) (hn : 0 < before.length)
    (hk : ActualInnerScanV1.prost.encoding.decode_key sliceBuf before = ok (.Err error,after)) :
    ActualInnerScanV1.prost.message.Message.merge.default_loop.body schema sliceBuf ctx message before =
      ok (.done (.Err error,message)) := by
  simp [ActualInnerScanV1.prost.message.Message.merge.default_loop.body,
    show sliceBuf.has_remaining before = ok true from by simp [sliceBuf,hn],hk,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from]

theorem loop_body_field (ctx : ActualInnerScanV1.prost.encoding.DecodeContext) (message next : Message) (before middle after : Slice U8)
    (status : core.result.Result Unit prost.error.DecodeError) (tag : U32) (wire : ActualInnerScanV1.prost.encoding.wire_type.WireType)
    (hn : 0 < before.length)
    (hk : ActualInnerScanV1.prost.encoding.decode_key sliceBuf before = ok (.Ok (tag,wire),middle))
    (hm : schema.merge_field sliceBuf
      message tag wire middle ctx = ok (status,next,after)) :
    ActualInnerScanV1.prost.message.Message.merge.default_loop.body schema sliceBuf ctx message before =
      ok (match status with | .Ok () => .cont (next,after) | .Err error => .done (.Err error,next)) := by
  simp only [ActualInnerScanV1.prost.message.Message.merge.default_loop.body,
    show sliceBuf.has_remaining before = ok true from by simp [sliceBuf,hn],bind_tc_ok,uncurry_apply_pair,if_true,hk,
    core.result.Result.Insts.CoreOpsTry.branch,clone_ctx,hm]
  cases status <;> rfl

/-- Every finite trace projects to the unchanged extracted Prost Message::merge
loop. No success-only observation or assumed loop correctness is used. -/
theorem trace_actual_loop {ctx message before result} (trace : MergeTrace ctx message before result) :
    ActualInnerScanV1.prost.message.Message.merge.default_loop schema sliceBuf message before ctx =
      ok (result.1,result.2.1) := by
  induction trace with
  | empty message before h =>
    rw [ActualInnerScanV1.prost.message.Message.merge.default_loop,loop.eq_1]
    simp only [loop_body_empty _ _ _ h,bind_tc_ok]
  | keyError hn hk =>
    rw [ActualInnerScanV1.prost.message.Message.merge.default_loop,loop.eq_1]
    simp only [loop_body_key_error _ _ _ _ _ hn hk,bind_tc_ok]
  | fieldError hn hk hm =>
    rw [ActualInnerScanV1.prost.message.Message.merge.default_loop,loop.eq_1]
    simp only [loop_body_field _ _ _ _ _ _ _ _ _ hn hk hm,bind_tc_ok]
  | next hn hk hm rest ih =>
    rw [ActualInnerScanV1.prost.message.Message.merge.default_loop,loop.eq_1]
    simp only [loop_body_field _ _ _ _ _ _ _ _ _ hn hk hm,bind_tc_ok]
    exact ih


#print axioms trace_actual_loop
#print axioms key_total
#print axioms actual_fields
#print axioms owned_decode
end ChatResponseReference.InnerScanV1
