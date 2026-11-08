import ProtoParseWork.DispatcherIntegrationWork.Generated.Funs
open Aeneas Aeneas.Std Result
open SignalMessageIntegration
set_option linter.unusedSimpArgs false
namespace DispatcherIntegration

def sliceBuf : bytes.buf.buf_impl.Buf (Slice U8) :=
  let i := LibSignalReference.Candidate.ProstBytesBuf.sliceBuf
  ⟨i.remaining, i.chunk, i.advance⟩

/-- Diagnostics are the only discarded data. Exact rejection kind, all fields,
and the post-error/success suffix remain observable. -/
def observe {B : Type}
    (r : Result ((core.result.Result Unit prost.error.DecodeError) × proto.wire.SignalMessage × B)) :
    Result ((core.result.Result Unit ProstBytesCandidate.error.DecodeErrorKind) × proto.wire.SignalMessage × B) := do
  let (r,m,b) ← r
  let status := match r with | .Ok x => .Ok x | .Err e => .Err e.inner.description
  ok (status,m,b)

theorem error_projection (e : prost.error.DecodeError) (stack : alloc.vec.Vec (Str × Str))
    (m : proto.wire.SignalMessage) (b : B) :
    observe (ok (.Err ⟨{e.inner with stack := stack}⟩,m,b)) =
      observe (ok (.Err e,m,b)) := rfl

/-- The extracted generated closure models retain the entire rejection kind.
Their diagnostic stack annotation is quotiented by observe, never success-only. -/
theorem projected_map_error (e : prost.error.DecodeError) (m : proto.wire.SignalMessage) (b : B) :
    observe (ok (.Err e,m,b)) = ok (.Err e.inner.description,m,b) := rfl

theorem observe_failure (error : Error) :
    observe (B := B) (.fail error) = .fail error := rfl

/-- Unknown tags call the accepted actual recursive skip body through its
structural adapter, retaining status and suffix without a success premise. -/
theorem unknown_dispatch {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (m : proto.wire.SignalMessage) (tag : U32) (wire : prost.encoding.wire_type.WireType)
    (b : B) (ctx : prost.encoding.DecodeContext) (htag : 6 < tag.val) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field inst m tag wire b ctx =
    (do let (r,rest) ← prost.encoding.skip_field inst wire tag b ctx
        ok (r,m,rest)) := by
  unfold proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
  split
  case h_1 | h_2 | h_3 | h_4 | h_5 | h_6 =>
    exfalso
    revert htag
    decide
  case h_7 => rfl

@[simp] theorem result_identity (r : core.result.Result T E) :
    (match r with | .Ok x => ok (.Ok x) | .Err e => ok (.Err e)) = (ok r : Result (core.result.Result T E)) := by
  cases r <;> rfl
@[simp] theorem scalar_zero : (0#32#uscalar : U32) = 0#u32 := by decide

/-- Dispatcher tag 2 invokes the actual accepted uint32 merger. Even failure
writes back the initialized Option and preserves the merger's exact suffix. -/
theorem counter_dispatch {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (m : proto.wire.SignalMessage) (wire : prost.encoding.wire_type.WireType)
    (b : B) (ctx : prost.encoding.DecodeContext) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field inst m 2#u32 wire b ctx =
    (do
      let (r,v,rest) ← prost.encoding.uint32.merge inst wire (m.counter.getD 0#u32) b ctx
      ok (r,{m with counter := some v},rest)) := by
  unfold proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
  split
  case h_1 | h_3 | h_4 | h_5 | h_6 =>
    rename_i heq
    have hv := congrArg UScalar.val heq
    exfalso; revert hv; decide
  case h_7 =>
    rename_i tag h1 h2 h3 h4 h5 h6
    exact (h2 (by decide)).elim
  case h_2 =>
    cases hc : m.counter <;>
      simp [core.option.Option.get_or_insert_with,
        P.Insts.CoreOpsFunctionFnOnceTupleU32.call_once, core.result.Result.map_err,
        proto.wire.MessageSignalMessage.merge_field.closure_1.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once,
        core.default.DefaultU32.default, hc]
    all_goals intro r v rest h; cases r <;> rfl
theorem previous_counter_dispatch {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (m : proto.wire.SignalMessage) (wire : prost.encoding.wire_type.WireType)
    (b : B) (ctx : prost.encoding.DecodeContext) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field inst m 3#u32 wire b ctx =
    (do
      let (r,v,rest) ← prost.encoding.uint32.merge inst wire (m.previous_counter.getD 0#u32) b ctx
      ok (r,{m with previous_counter := some v},rest)) := by
  unfold proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
  split
  case h_1 | h_2 | h_4 | h_5 | h_6 =>
    rename_i heq
    have hv := congrArg UScalar.val heq
    exfalso; revert hv; decide
  case h_7 =>
    rename_i tag h1 h2 h3 h4 h5 h6
    exact (h3 (by decide)).elim
  case h_3 =>
    cases hc : m.previous_counter <;>
      simp [core.option.Option.get_or_insert_with,
        P.Insts.CoreOpsFunctionFnOnceTupleU32.call_once, core.result.Result.map_err,
        proto.wire.MessageSignalMessage.merge_field.closure_2.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once,
        core.default.DefaultU32.default, hc]
    all_goals intro r v rest h; cases r <;> rfl

theorem ratchet_key_dispatch {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (m : proto.wire.SignalMessage) (wire : prost.encoding.wire_type.WireType)
    (b : B) (ctx : prost.encoding.DecodeContext) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field inst m 1#u32 wire b ctx =
    (do
      let (r,v,rest) ← prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
        inst wire (m.ratchet_key.getD (alloc.vec.Vec.new U8)) b ctx
      ok (r,{m with ratchet_key := some v},rest)) := by
  unfold proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
  split
  case h_2 | h_3 | h_4 | h_5 | h_6 =>
    rename_i heq
    have hv := congrArg UScalar.val heq
    exfalso; revert hv; decide
  case h_7 =>
    rename_i tag h1 h2 h3 h4 h5 h6
    exact (h1 (by decide)).elim
  case h_1 =>
    cases hc : m.ratchet_key <;>
      simp [core.option.Option.get_or_insert_with,
        P.Insts.CoreOpsFunctionFnOnceTupleVec.call_once, core.result.Result.map_err,
        proto.wire.MessageSignalMessage.merge_field.closure.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once,
        alloc.vec.Vec.Insts.CoreDefaultDefault.default, hc]
    all_goals intro r v rest h; cases r <;> rfl

theorem ciphertext_dispatch {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (m : proto.wire.SignalMessage) (wire : prost.encoding.wire_type.WireType)
    (b : B) (ctx : prost.encoding.DecodeContext) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field inst m 4#u32 wire b ctx =
    (do
      let (r,v,rest) ← prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
        inst wire (m.ciphertext.getD (alloc.vec.Vec.new U8)) b ctx
      ok (r,{m with ciphertext := some v},rest)) := by
  unfold proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
  split
  case h_1 | h_2 | h_3 | h_5 | h_6 =>
    rename_i heq
    have hv := congrArg UScalar.val heq
    exfalso; revert hv; decide
  case h_7 =>
    rename_i tag h1 h2 h3 h4 h5 h6
    exact (h4 (by decide)).elim
  case h_4 =>
    cases hc : m.ciphertext <;>
      simp [core.option.Option.get_or_insert_with,
        P.Insts.CoreOpsFunctionFnOnceTupleVec.call_once, core.result.Result.map_err,
        proto.wire.MessageSignalMessage.merge_field.closure_3.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once,
        alloc.vec.Vec.Insts.CoreDefaultDefault.default, hc]
    all_goals intro r v rest h; cases r <;> rfl

theorem pq_ratchet_dispatch {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (m : proto.wire.SignalMessage) (wire : prost.encoding.wire_type.WireType)
    (b : B) (ctx : prost.encoding.DecodeContext) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field inst m 5#u32 wire b ctx =
    (do
      let (r,v,rest) ← prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
        inst wire (m.pq_ratchet.getD (alloc.vec.Vec.new U8)) b ctx
      ok (r,{m with pq_ratchet := some v},rest)) := by
  unfold proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
  split
  case h_1 | h_2 | h_3 | h_4 | h_6 =>
    rename_i heq
    have hv := congrArg UScalar.val heq
    exfalso; revert hv; decide
  case h_7 =>
    rename_i tag h1 h2 h3 h4 h5 h6
    exact (h5 (by decide)).elim
  case h_5 =>
    cases hc : m.pq_ratchet <;>
      simp [core.option.Option.get_or_insert_with,
        P.Insts.CoreOpsFunctionFnOnceTupleVec.call_once, core.result.Result.map_err,
        proto.wire.MessageSignalMessage.merge_field.closure_4.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once,
        alloc.vec.Vec.Insts.CoreDefaultDefault.default, hc]
    all_goals intro r v rest h; cases r <;> rfl

theorem addresses_dispatch {B : Type} (inst : bytes.buf.buf_impl.Buf B)
    (m : proto.wire.SignalMessage) (wire : prost.encoding.wire_type.WireType)
    (b : B) (ctx : prost.encoding.DecodeContext) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field inst m 6#u32 wire b ctx =
    (do
      let (r,v,rest) ← prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
        inst wire (m.addresses.getD (alloc.vec.Vec.new U8)) b ctx
      ok (r,{m with addresses := some v},rest)) := by
  unfold proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
  split
  case h_1 | h_2 | h_3 | h_4 | h_5 =>
    rename_i heq
    have hv := congrArg UScalar.val heq
    exfalso; revert hv; decide
  case h_7 =>
    rename_i tag h1 h2 h3 h4 h5 h6
    exact (h6 (by decide)).elim
  case h_6 =>
    cases hc : m.addresses <;>
      simp [core.option.Option.get_or_insert_with,
        P.Insts.CoreOpsFunctionFnOnceTupleVec.call_once, core.result.Result.map_err,
        proto.wire.MessageSignalMessage.merge_field.closure_5.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once,
        alloc.vec.Vec.Insts.CoreDefaultDefault.default, hc]
    all_goals intro r v rest h; cases r <;> rfl

#print axioms unknown_dispatch
#print axioms observe_failure
#print axioms counter_dispatch
#print axioms previous_counter_dispatch
#print axioms ratchet_key_dispatch
#print axioms ciphertext_dispatch
#print axioms pq_ratchet_dispatch
#print axioms addresses_dispatch
#print axioms error_projection
end DispatcherIntegration
