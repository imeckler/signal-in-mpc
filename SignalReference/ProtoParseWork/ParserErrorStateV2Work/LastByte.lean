import TlsMpc.Signal.ProtoParse
open TlsMpc TlsMpc.Signal
namespace ParserErrorStateV2
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem last_byte_clear : ∀ byte : BitVec 8,
    (ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete [byte] 0).ok =
      if byte.toNat < 128 then 255 else 0 := by decide

#print axioms last_byte_clear
end ParserErrorStateV2
