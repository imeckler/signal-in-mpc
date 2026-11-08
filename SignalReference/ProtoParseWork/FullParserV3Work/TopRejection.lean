import ProtoParseWork.FullParserV3Work.FrozenRejection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration

theorem top_rejection_fields (bytes after : Slice U8) (error : prost.error.DecodeError)
    (before result : State (BitVec 8) (BitVec 64)) (tag : BitVec 64) (hd : before.parser.depth = 0)
    (h : ActiveRejection bytes after error before result
      (if before.parser.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 tag before.parser.fields else before.parser.fields)) :
    ActiveRejection bytes after error before result
      (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 tag before.parser.fields) :=
  Eq.mp (congrArg (fun fields => ActiveRejection bytes after error before result fields) (if_pos hd)) h

#print axioms top_rejection_fields
end FullParserV3.Observed
