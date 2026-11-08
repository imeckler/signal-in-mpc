import ProtoParseWork.FullParserV3Work.WrongWirePlan
import ProtoParseWork.FullParserV3Work.KnownErrorDomain
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
set_option maxHeartbeats 2000000

/-- Wrong-wire scalar rejection occurs before reading the input or replacing
an existing scalar. The generated dispatcher separately performs get-or-insert. -/
theorem scalar_wrong_wire_actual (wire : prost.encoding.wire_type.WireType)
    (old : U32) (before : Slice U8) (ctx : prost.encoding.DecodeContext)
    (hw : wire ≠ .Varint) :
    prost.encoding.uint32.merge DispatcherIntegration.sliceBuf wire old before ctx =
      .ok (.Err (fieldError (LibSignalReference.Candidate.ProstField.decodeError
        (.UnexpectedWireType (toFieldWire wire) .Varint))),old,before) := by
  have hw' : toFieldWire wire ≠ .Varint := by cases wire <;> simp_all [toFieldWire]
  unfold prost.encoding.uint32.merge
  rw [LibSignalReference.Candidate.ProstField.uint32_wire_error _ _ _ _ _ hw']
  rfl

/-- Wrong-wire bytes rejection likewise preserves the complete old vector and
input cursor, including empty and previously present values. -/
theorem bytes_wrong_wire_actual (wire : prost.encoding.wire_type.WireType)
    (old : alloc.vec.Vec U8) (before : Slice U8) (ctx : prost.encoding.DecodeContext)
    (hw : wire ≠ .LengthDelimited) :
    prost.encoding.bytes.merge alloc.vec.VecU8.Insts.ProstEncodingBytesAdapter
      DispatcherIntegration.sliceBuf wire old before ctx =
      .ok (.Err (LibSignalReference.Candidate.ProstBytes.decodeError
        (.UnexpectedWireType (toBytesWire wire) .LengthDelimited)),old,before) := by
  have hw' : toBytesWire wire ≠ .LengthDelimited := by cases wire <;> simp_all [toBytesWire]
  unfold prost.encoding.bytes.merge
  rw [LibSignalReference.Candidate.ProstBytes.bytes_wire_error _ _ _ _ _ _ hw']

#print axioms scalar_wrong_wire_actual
#print axioms bytes_wrong_wire_actual
end FullParserV3
