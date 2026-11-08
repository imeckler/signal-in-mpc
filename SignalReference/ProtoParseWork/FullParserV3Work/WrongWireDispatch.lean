import ProtoParseWork.FullParserV3Work.WrongWirePrimitive
import ProtoParseWork.FullParserV3Work.DispatcherMutation
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open SignalMessageIntegration DispatcherIntegration
set_option maxHeartbeats 2000000

theorem scalar_wrong_dispatch (m : Message) (tag : U32) (ht : ScalarTag tag)
    (wire : prost.encoding.wire_type.WireType) (before : Slice U8) (ctx : prost.encoding.DecodeContext)
    (hw : wire ≠ .Varint) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field DispatcherIntegration.sliceBuf m tag wire before ctx =
    .ok (.Err (fieldError (LibSignalReference.Candidate.ProstField.decodeError
      (.UnexpectedWireType (toFieldWire wire) .Varint))),initializeMessage (BitVec.ofNat 64 tag.val) m,before) := by
  rcases ht with rfl | rfl
  · rw [counter_dispatch,scalar_wrong_wire_actual wire _ before ctx hw]
    simp only [bind_tc_ok]
    simp [initializeMessage]
  · rw [previous_counter_dispatch,scalar_wrong_wire_actual wire _ before ctx hw]
    simp only [bind_tc_ok]
    simp [initializeMessage]

theorem bytes_wrong_dispatch (m : Message) (tag : U32) (ht : BytesTag tag)
    (wire : prost.encoding.wire_type.WireType) (before : Slice U8) (ctx : prost.encoding.DecodeContext)
    (hw : wire ≠ .LengthDelimited) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field DispatcherIntegration.sliceBuf m tag wire before ctx =
    .ok (.Err (LibSignalReference.Candidate.ProstBytes.decodeError
      (.UnexpectedWireType (toBytesWire wire) .LengthDelimited)),initializeMessage (BitVec.ofNat 64 tag.val) m,before) := by
  rcases ht with rfl | rfl | rfl | rfl
  · rw [ratchet_key_dispatch,bytes_wrong_wire_actual wire _ before ctx hw]
    simp [bind_tc_ok,initializeMessage]
  · rw [ciphertext_dispatch,bytes_wrong_wire_actual wire _ before ctx hw]
    simp [bind_tc_ok,initializeMessage]
  · rw [pq_ratchet_dispatch,bytes_wrong_wire_actual wire _ before ctx hw]
    simp [bind_tc_ok,initializeMessage]
  · rw [addresses_dispatch,bytes_wrong_wire_actual wire _ before ctx hw]
    simp [bind_tc_ok,initializeMessage]

#print axioms scalar_wrong_dispatch
#print axioms bytes_wrong_dispatch
end FullParserV3
