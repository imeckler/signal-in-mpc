import ProtoParseWork.DispatcherIntegrationWork.NumericBridge
open Aeneas Aeneas.Std Result TlsMpc TlsMpc.Signal
open SignalMessageIntegration
namespace DispatcherIntegration

/-- Pinned generated Prost initializes the missing Option before rejecting a
wrong wire type; neither a payload decoder nor an input-consumption premise is used. -/
theorem actual_missing_counter_wrong_wire (m : proto.wire.SignalMessage)
    (hm : m.counter = none) (before : Slice U8) (ctx : prost.encoding.DecodeContext) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
      sliceBuf m 2#u32 .LengthDelimited before ctx =
    ok (.Err (fieldError (LibSignalReference.Candidate.ProstField.decodeError
        (.UnexpectedWireType .LengthDelimited .Varint))),
      {m with counter := some 0#u32},before) := by
  rw [counter_dispatch]
  unfold prost.encoding.uint32.merge
  rw [field_slice_adapter]
  simp only [toFieldWire,hm,Option.getD_none]
  rw [LibSignalReference.Candidate.ProstField.uint32_wire_error _ _ _ _ _ (by decide)]
  rfl

/-- Concrete body [18,0]: counter tag with length-delimited wire type, followed
by an empty length. Numeric plan rejects and retains the absent field. -/
def wrongWireInitial := ProtoParse.initial Word64.concrete ByteAuth.concrete 2
def wrongWirePlan := ProtoParse.plan Word64.concrete ByteAuth.concrete 2
  ⟨255,1,18⟩ ⟨255,2,0⟩ wrongWireInitial
def wrongWireNumeric := ProtoParse.applyPlan Word64.concrete ByteAuth.concrete 0
  wrongWirePlan wrongWireInitial

theorem numeric_wrong_wire_rejects : wrongWireNumeric.ok = 0 := by decide

theorem numeric_wrong_wire_counter_absent :
    scalarView (ProtoParse.getField Word64.concrete ByteAuth.concrete wrongWireNumeric 1) = none := by decide

/-- The complete numeric scan of the concrete wire body, not just its plan,
retains the absent counter and rejects completion. -/
theorem numeric_body_counter_absent :
    scalarView (ProtoParse.getField Word64.concrete ByteAuth.concrete
      (ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete [18,0]) 1) = none := by decide

theorem numeric_body_rejects :
    ProtoParse.completeMask Word64.concrete ByteAuth.concrete 2
      (ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete [18,0]) = 0 := by decide

theorem rejection_counter_views_differ :
    scalarView (ProtoParse.getField Word64.concrete ByteAuth.concrete wrongWireNumeric 1) ≠
      some (0#u32) := by
  rw [numeric_wrong_wire_counter_absent]
  intro h; cases h

#print axioms numeric_wrong_wire_rejects
#print axioms numeric_body_counter_absent
#print axioms numeric_body_rejects
#print axioms actual_missing_counter_wrong_wire
#print axioms numeric_wrong_wire_counter_absent
#print axioms rejection_counter_views_differ
end DispatcherIntegration
