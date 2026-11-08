import ProtoParseWork.ParserErrorStateV2Work.FailureScan
import ProtoParseWork.ParserErrorStateV2Work.HistoricalV1
open Aeneas Aeneas.Std Result TlsMpc TlsMpc.Signal
open SignalMessageIntegration DispatcherIntegration
namespace ParserErrorStateV2
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def parse (body : List (BitVec 8)) :=
  ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete body

def counter (body : List (BitVec 8)) :=
  scalarView (ProtoParse.getField Word64.concrete ByteAuth.concrete (parse body) 1)
def bytesField (body : List (BitVec 8)) (i : Nat) : Option (List (BitVec 8)) :=
  let f := ProtoParse.getField Word64.concrete ByteAuth.concrete (parse body) i
  if f.present = 255 then some ((body.drop f.offset.toNat).take f.length.toNat) else none

/-- The frozen v1 mismatch remains explicit historical evidence. -/
theorem historical_counter_absent :
    scalarView (ProtoParse.getField Word64.concrete ByteAuth.concrete
      (ProtoParse.HistoricalV1.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete [18,0]) 1) = none := by decide

theorem wrong_wire_initializes : counter [18,0] = some 0#u32 ∧
    (parse [18,0]).next = 1 ∧ (parse [18,0]).ok = 0 := by decide

#print axioms historical_counter_absent
#print axioms wrong_wire_initializes
end ParserErrorStateV2
