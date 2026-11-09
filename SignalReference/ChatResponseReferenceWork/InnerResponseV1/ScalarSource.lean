import ChatResponseReferenceWork.InnerResponseV1.BufferBridge
open Aeneas Aeneas.Std Result
namespace ActualInnerResponseV1

/-- Actual pinned generated uint32 body; namespace qualification only. -/
noncomputable def prost.encoding.uint32.merge
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0)
  (wire_type : prost.encoding.wire_type.WireType) (value : Std.U32) (buf : T0)
  (_ctx : prost.encoding.DecodeContext) :
  Result ((core.result.Result Unit prost.error.DecodeError) × Std.U32 × T0)
  := do
  let r ←
    prost.encoding.wire_type.check_wire_type prost.encoding.wire_type.WireType.Varint
      wire_type
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let (r1, buf1) ←
      prost.encoding.varint.decode_varint bytesbufbuf_implBufInst buf
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let value1 ← lift (UScalar.cast .U32 val)
      ok (core.result.Result.Ok (), value1, buf1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame prost.error.DecodeError) residual
      ok (r2, value, buf1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame prost.error.DecodeError) residual
    ok (r1, value, buf)

/-- Actual pinned generated uint64 body; namespace qualification only. -/
noncomputable def prost.encoding.uint64.merge
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0)
  (wire_type : prost.encoding.wire_type.WireType) (value : Std.U64) (buf : T0)
  (_ctx : prost.encoding.DecodeContext) :
  Result ((core.result.Result Unit prost.error.DecodeError) × Std.U64 × T0)
  := do
  let r ←
    prost.encoding.wire_type.check_wire_type prost.encoding.wire_type.WireType.Varint
      wire_type
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let (r1, buf1) ←
      prost.encoding.varint.decode_varint bytesbufbuf_implBufInst buf
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      ok (core.result.Result.Ok (), val, buf1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame prost.error.DecodeError) residual
      ok (r2, value, buf1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame prost.error.DecodeError) residual
    ok (r1, value, buf)

end ActualInnerResponseV1
