import TlsMpc.Signal.PrivateService
import TlsMpc.Signal.PrivateRequestCounter

/-! Retain a private monotone request ID with the selected Signal/SPQR chains.
The current ID is encoded; the candidate next ID is committed before release.
Exhaustion rejects without wrapping. Native execution must generate a fresh
independent WebSocket mask and a fresh SS ephemeral scalar per invocation. -/
namespace TlsMpc.Signal.PrivateConversationService

def oldState (i : SpqrSend.Input B) (metadata : List B) : List B :=
  PrivateSpqrSend.oldState i ++ (metadata.drop 40).take 8

def prepare (o : Aes.Ops B) (v : Varint64.Ops B V) (d : RelayEncoding.DecimalOps B V)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (hasChunk withAddresses : Bool)
    (ephemeralPublic computedSender ephemeralDh staticDh certificate metadata : List B)
    (i : SpqrSend.Input B) : PrivateSpqrSend.Prepared B :=
  let core := PrivateService.prepare o v d s a hasChunk withAddresses
    ephemeralPublic computedSender ephemeralDh staticDh certificate metadata i
  let next := PrivateRequestCounter.next a ((metadata.drop 40).take 8)
  ⟨core.candidateState ++ next.drop 1,PrivateProtobuf.gate a (OpenResult.get a next 0) core.wire⟩

def output (a : ByteAuth.Ops B) (i : SpqrSend.Input B) (metadata : List B) (p : PrivateSpqrSend.Prepared B) : List B :=
  PrivateSpqrSend.output a (oldState i metadata) p

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'}
  {d : RelayEncoding.DecimalOps B V} {d' : RelayEncoding.DecimalOps B' V'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} {fv : V → V'}
  (ho : Aes.Hom o o' f) (hv : Varint64.Hom v v' f fv)
  (hd : RelayEncoding.DecimalHom d d' f fv) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem oldState_map (i : SpqrSend.Input B) (metadata : List B) :
    (oldState i metadata).map f = oldState (i.map f) (metadata.map f) := by
  simp only [oldState,List.map_append,PrivateSpqrSend.oldState_map ha,List.map_take,List.map_drop]
include ho hv hd hs

theorem prepare_map (hasChunk withAddresses : Bool)
    (ephemeralPublic computedSender ephemeralDh staticDh certificate metadata : List B) (i : SpqrSend.Input B) :
    (prepare o v d s a hasChunk withAddresses ephemeralPublic computedSender ephemeralDh staticDh certificate metadata i).map f =
    prepare o' v' d' s' a' hasChunk withAddresses (ephemeralPublic.map f) (computedSender.map f)
      (ephemeralDh.map f) (staticDh.map f) (certificate.map f) (metadata.map f) (i.map f) := by
  have core := PrivateService.prepare_map ho hv hd hs ha hasChunk withAddresses
    ephemeralPublic computedSender ephemeralDh staticDh certificate metadata i
  have state := congrArg PrivateSpqrSend.Prepared.candidateState core
  have wire := congrArg PrivateSpqrSend.Prepared.wire core
  simp only [PrivateSpqrSend.Prepared.map] at state wire
  simp only [prepare,PrivateSpqrSend.Prepared.map,List.map_append,List.map_drop,List.map_take,
    PrivateRequestCounter.next_map ha,PrivateProtobuf.gate_map ha,OpenResult.get_map ha,state,wire]

omit ho hv hd hs in
theorem output_map (i : SpqrSend.Input B) (metadata : List B) (p : PrivateSpqrSend.Prepared B) :
    (output a i metadata p).map f = output a' (i.map f) (metadata.map f) (p.map f) := by
  simp only [output,PrivateSpqrSend.output_map ha,oldState_map ha]

end Refinement
open Std.Tactic.BVDecide

theorem compiled_output_correct (hasChunk withAddresses : Bool)
    (ephemeralPublic computedSender ephemeralDh staticDh certificate metadata : List (BVExpr 8))
    (i : SpqrSend.Input (BVExpr 8)) (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement
      (output ByteAuth.symbolic i metadata (prepare Aes.symbolic Varint64.symbolic RelayEncoding.decimalSymbolic Sha256.symbolic
        ByteAuth.symbolic hasChunk withAddresses ephemeralPublic computedSender ephemeralDh staticDh certificate metadata i))
      (output ByteAuth.concrete (i.map (BVExpr.eval assign)) (metadata.map (BVExpr.eval assign))
        (prepare Aes.concrete Varint64.concrete RelayEncoding.decimalConcrete Sha256.concrete ByteAuth.concrete
          hasChunk withAddresses (ephemeralPublic.map (BVExpr.eval assign)) (computedSender.map (BVExpr.eval assign))
          (ephemeralDh.map (BVExpr.eval assign)) (staticDh.map (BVExpr.eval assign)) (certificate.map (BVExpr.eval assign))
          (metadata.map (BVExpr.eval assign)) (i.map (BVExpr.eval assign)))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,output_map (ByteAuth.evaluationHom assign),
    prepare_map (Aes.evaluationHom assign) (Varint64.evaluationHom assign) (RelayEncoding.decimalEvaluationHom assign)
      (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.PrivateConversationService
