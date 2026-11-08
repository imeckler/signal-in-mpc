import TlsMpc.Signal.PrivateConversationService
import TlsMpc.Sha256Backend

namespace TlsMpc.Signal.PrivateConversationBackend
open Std.Tactic.BVDecide
open PrivateConversationService

theorem compiled_output_correct (profile : Sha256Backend.Profile) (hasChunk withAddresses : Bool)
    (ephemeralPublic computedSender ephemeralDh staticDh certificate metadata : List (BVExpr 8))
    (i : SpqrSend.Input (BVExpr 8)) (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement
      (output ByteAuth.symbolic i metadata (prepare Aes.symbolic Varint64.symbolic RelayEncoding.decimalSymbolic (Sha256Backend.select profile Sha256.symbolic)
        ByteAuth.symbolic hasChunk withAddresses ephemeralPublic computedSender ephemeralDh staticDh certificate metadata i))
      (output ByteAuth.concrete (i.map (BVExpr.eval assign)) (metadata.map (BVExpr.eval assign))
        (prepare Aes.concrete Varint64.concrete RelayEncoding.decimalConcrete Sha256.concrete ByteAuth.concrete
          hasChunk withAddresses (ephemeralPublic.map (BVExpr.eval assign)) (computedSender.map (BVExpr.eval assign))
          (ephemeralDh.map (BVExpr.eval assign)) (staticDh.map (BVExpr.eval assign)) (certificate.map (BVExpr.eval assign))
          (metadata.map (BVExpr.eval assign)) (i.map (BVExpr.eval assign)))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,output_map (ByteAuth.evaluationHom assign),
    prepare_map (Aes.evaluationHom assign) (Varint64.evaluationHom assign) (RelayEncoding.decimalEvaluationHom assign)
      (Sha256Backend.evaluationHom profile assign) (ByteAuth.evaluationHom assign)]


end TlsMpc.Signal.PrivateConversationBackend
