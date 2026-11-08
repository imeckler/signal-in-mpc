import ProtoParseWork.FullParserV3Work.GeneratedDriver.Funs
import ProtoParseWork.FullParserV3Work.MessageTotality
open Aeneas Aeneas.Std Result ControlFlow
namespace FullParserV3
open SignalMessageIntegration
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

abbrev Message := proto.wire.SignalMessage
abbrev Status := core.result.Result Unit prost.error.DecodeError
abbrev Outcome := Status × Message × Slice U8

def driverBuf : ActualMessageDriver.bytes.buf.buf_impl.Buf (Slice U8) :=
  let base := DispatcherIntegration.sliceBuf
  { remaining := base.remaining,chunk := base.chunk,advance := base.advance,
    has_remaining := fun bytes => ok (0 < bytes.length) }

theorem driver_has_remaining_default (before : Slice U8) :
    ActualMessageDriver.bytes.buf.buf_impl.Buf.has_remaining.default driverBuf before = driverBuf.has_remaining before := by
  have hn : before.len > 0#usize ↔ 0 < before.length := by scalar_tac
  change ok (decide (before.len > 0#usize)) = ok (decide (0 < before.length))
  simp only [hn]

def wireToSignal : ActualMessageDriver.prost.encoding.wire_type.WireType → prost.encoding.wire_type.WireType
  | .Varint => .Varint
  | .SixtyFourBit => .SixtyFourBit
  | .LengthDelimited => .LengthDelimited
  | .StartGroup => .StartGroup
  | .EndGroup => .EndGroup
  | .ThirtyTwoBit => .ThirtyTwoBit

def toSignalBuf {B : Type} (inst : ActualMessageDriver.bytes.buf.buf_impl.Buf B) :
    SignalMessageIntegration.bytes.buf.buf_impl.Buf B := ⟨inst.remaining,inst.chunk,inst.advance⟩

/-- Parsing uses only merge_field; all unrelated trait methods remain arbitrary. -/
noncomputable def withDispatcher (unused : ActualMessageDriver.prost.message.Message Message) :
    ActualMessageDriver.prost.message.Message Message :=
  { unused with merge_field := (fun inst self tag wire buf ctx =>
      proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
        (toSignalBuf inst) self tag (wireToSignal wire) buf ⟨ctx.recurse_count⟩) }

theorem driver_skip_adapter : ActualMessageDriver.toSkipBuf driverBuf =
    LibSignalReference.Candidate.ProstSkipBuf.sliceBuf := rfl

theorem driver_signal_adapter : toSignalBuf driverBuf = DispatcherIntegration.sliceBuf := rfl

/-- A suffix-retaining execution trace of the actual extracted merge loop.
The extracted owning-generic loop's public result omits its local buffer; the
trace retains every actual decoder/dispatcher suffix instead of erasing it. -/
inductive MergeTrace (ctx : ActualMessageDriver.prost.encoding.DecodeContext) : Message → Slice U8 → Outcome → Prop where
  | empty (message before) (h : before.length = 0) :
      MergeTrace ctx message before (.Ok (),message,before)
  | keyError {message before after error} (hn : 0 < before.length)
      (hk : ActualMessageDriver.prost.encoding.decode_key driverBuf before = ok (.Err error,after)) :
      MergeTrace ctx message before (.Err error,message,after)
  | fieldError {message before middle after error next tag wire} (hn : 0 < before.length)
      (hk : ActualMessageDriver.prost.encoding.decode_key driverBuf before = ok (.Ok (tag,wire),middle))
      (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field DispatcherIntegration.sliceBuf
        message tag (wireToSignal wire) middle ⟨ctx.recurse_count⟩ = ok (.Err error,next,after)) :
      MergeTrace ctx message before (.Err error,next,after)
  | next {message before middle after next tag wire result} (hn : 0 < before.length)
      (hk : ActualMessageDriver.prost.encoding.decode_key driverBuf before = ok (.Ok (tag,wire),middle))
      (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field DispatcherIntegration.sliceBuf
        message tag (wireToSignal wire) middle ⟨ctx.recurse_count⟩ = ok (.Ok (),next,after))
      (rest : MergeTrace ctx next after result) : MergeTrace ctx message before result

theorem clone_ctx (ctx : ActualMessageDriver.prost.encoding.DecodeContext) :
    ActualMessageDriver.prost.encoding.DecodeContext.Insts.CoreCloneClone.clone ctx = ok ctx := by
  cases ctx
  rfl

theorem loop_body_empty (unused : ActualMessageDriver.prost.message.Message Message)
    (ctx : ActualMessageDriver.prost.encoding.DecodeContext) (message : Message) (before : Slice U8)
    (hn : before.length = 0) :
    ActualMessageDriver.prost.message.Message.merge.default_loop.body (withDispatcher unused) driverBuf ctx message before =
      ok (.done (.Ok (),message)) := by
  simp [ActualMessageDriver.prost.message.Message.merge.default_loop.body,driverBuf,hn]

theorem loop_body_key_error (unused : ActualMessageDriver.prost.message.Message Message)
    (ctx : ActualMessageDriver.prost.encoding.DecodeContext) (message : Message) (before after : Slice U8)
    (error : prost.error.DecodeError) (hn : 0 < before.length)
    (hk : ActualMessageDriver.prost.encoding.decode_key driverBuf before = ok (.Err error,after)) :
    ActualMessageDriver.prost.message.Message.merge.default_loop.body (withDispatcher unused) driverBuf ctx message before =
      ok (.done (.Err error,message)) := by
  simp [ActualMessageDriver.prost.message.Message.merge.default_loop.body,
    show driverBuf.has_remaining before = ok true from by simp [driverBuf,hn],hk,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from]

theorem loop_body_field (unused : ActualMessageDriver.prost.message.Message Message)
    (ctx : ActualMessageDriver.prost.encoding.DecodeContext) (message next : Message) (before middle after : Slice U8)
    (status : Status) (tag : U32) (wire : ActualMessageDriver.prost.encoding.wire_type.WireType)
    (hn : 0 < before.length)
    (hk : ActualMessageDriver.prost.encoding.decode_key driverBuf before = ok (.Ok (tag,wire),middle))
    (hm : proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field DispatcherIntegration.sliceBuf
      message tag (wireToSignal wire) middle ⟨ctx.recurse_count⟩ = ok (status,next,after)) :
    ActualMessageDriver.prost.message.Message.merge.default_loop.body (withDispatcher unused) driverBuf ctx message before =
      ok (match status with | .Ok () => .cont (next,after) | .Err error => .done (.Err error,next)) := by
  simp only [ActualMessageDriver.prost.message.Message.merge.default_loop.body,
    show driverBuf.has_remaining before = ok true from by simp [driverBuf,hn],bind_tc_ok,uncurry_apply_pair,if_true,hk,
    core.result.Result.Insts.CoreOpsTry.branch,clone_ctx,withDispatcher,driver_signal_adapter,hm]
  cases status <;> rfl

/-- Every finite trace projects to the unchanged extracted Prost Message::merge
loop. No success-only observation or assumed loop correctness is used. -/
theorem trace_actual_loop (unused : ActualMessageDriver.prost.message.Message Message)
    {ctx message before result} (trace : MergeTrace ctx message before result) :
    ActualMessageDriver.prost.message.Message.merge.default_loop (withDispatcher unused) driverBuf message before ctx =
      ok (result.1,result.2.1) := by
  induction trace with
  | empty message before h =>
    rw [ActualMessageDriver.prost.message.Message.merge.default_loop,loop.eq_1]
    simp only [loop_body_empty unused _ _ _ h,bind_tc_ok]
  | keyError hn hk =>
    rw [ActualMessageDriver.prost.message.Message.merge.default_loop,loop.eq_1]
    simp only [loop_body_key_error unused _ _ _ _ _ hn hk,bind_tc_ok]
  | fieldError hn hk hm =>
    rw [ActualMessageDriver.prost.message.Message.merge.default_loop,loop.eq_1]
    simp only [loop_body_field unused _ _ _ _ _ _ _ _ _ hn hk hm,bind_tc_ok]
  | next hn hk hm rest ih =>
    rw [ActualMessageDriver.prost.message.Message.merge.default_loop,loop.eq_1]
    simp only [loop_body_field unused _ _ _ _ _ _ _ _ _ hn hk hm,bind_tc_ok]
    exact ih

#print axioms driver_has_remaining_default
#print axioms driver_skip_adapter
#print axioms trace_actual_loop
end FullParserV3
