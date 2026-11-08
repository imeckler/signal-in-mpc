import TlsMpc.Signal.SealedSenderV1
import TlsMpc.Signal.RelayRequest

/-! Actual SSv1 envelope -> relay WebSocket request, with both computed stage
statuses composed inside the proved circuit. No external cryptographic-validity
flag is supplied. The private curve/DH producer is a separate input boundary. -/
namespace TlsMpc.Signal.SealedRelay
open Std.Tactic.BVDecide

def produce (o : Aes.Ops B) (s : Sha256.Ops B W) (d : RelayEncoding.DecimalOps B V)
    (v : Varint64.Ops B V) (a : ByteAuth.Ops B) (shape : RelayRequest.Shape)
    (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender metadata : List B) : List B :=
  let sealedOutput := SealedSenderV1.boundSeal o s a recipientPublic ephemeralPublic senderPublic
    ephemeralDh staticDh certificate inner expectedSender
  let raw := metadata.take 53 ++ sealedOutput.drop 1 ++ (metadata.drop 53).take 4
  let requestOutput := RelayRequest.encodeCore d v a shape raw
  let status := a.and (OpenResult.get a sealedOutput 0) (OpenResult.get a requestOutput 0)
  status :: ByteAuth.release a status (requestOutput.drop 1)

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {d : RelayEncoding.DecimalOps B V} {d' : RelayEncoding.DecimalOps B' V'}
  {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} {fv : V → V'}
  (ho : Aes.Hom o o' f) (hs : Sha256.Hom s s' f fw)
  (hd : RelayEncoding.DecimalHom d d' f fv) (hv : Varint64.Hom v v' f fv) (ha : ByteAuth.Hom a a' f)
include ho hs hd hv ha

theorem produce_map (shape : RelayRequest.Shape)
    (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender metadata : List B) :
    (produce o s d v a shape recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender metadata).map f =
      produce o' s' d' v' a' shape (recipientPublic.map f) (ephemeralPublic.map f) (senderPublic.map f)
        (ephemeralDh.map f) (staticDh.map f) (certificate.map f) (inner.map f) (expectedSender.map f) (metadata.map f) := by
  simp only [produce,List.map_cons,ha.and,OpenResult.get_map ha,
    ByteAuth.release_map ha,List.map_drop,List.map_take,List.map_append,
    SealedSenderV1.boundSeal_map ho hs ha,RelayRequest.encodeCore_map hd hv ha]
end Refinement

theorem compiled_produce_correct (shape : RelayRequest.Shape)
    (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender metadata : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (produce Aes.symbolic Sha256.symbolic RelayEncoding.decimalSymbolic Varint64.symbolic ByteAuth.symbolic
      shape recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender metadata).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (produce Aes.symbolic Sha256.symbolic RelayEncoding.decimalSymbolic Varint64.symbolic ByteAuth.symbolic
        shape recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender metadata))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
      (produce Aes.symbolic Sha256.symbolic RelayEncoding.decimalSymbolic Varint64.symbolic ByteAuth.symbolic
        shape recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner expectedSender metadata))).vec.get index hi)) =
    (ByteCircuit.joinValue (produce Aes.concrete Sha256.concrete RelayEncoding.decimalConcrete Varint64.concrete ByteAuth.concrete
      shape (recipientPublic.map (BVExpr.eval assign)) (ephemeralPublic.map (BVExpr.eval assign))
      (senderPublic.map (BVExpr.eval assign)) (ephemeralDh.map (BVExpr.eval assign)) (staticDh.map (BVExpr.eval assign))
      (certificate.map (BVExpr.eval assign)) (inner.map (BVExpr.eval assign)) (expectedSender.map (BVExpr.eval assign))
      (metadata.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,produce_map (Aes.evaluationHom assign) (Sha256.evaluationHom assign)
    (RelayEncoding.decimalEvaluationHom assign) (Varint64.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.SealedRelay
